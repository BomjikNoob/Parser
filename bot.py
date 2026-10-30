"""Мониторинг новых объявлений (Depop, Vinted, Poshmark, Wallapop, Milanuncios, OLX) с фильтрами по продавцу."""
import asyncio
import datetime
import html
import itertools
import json
import logging
import os
import re
import socket
import sqlite3
import sys
import time
from contextvars import ContextVar
from logging.handlers import RotatingFileHandler
from pathlib import Path
from urllib.parse import urljoin, urlsplit
from zoneinfo import ZoneInfo

from aiogram import Bot, Dispatcher, F
from aiogram.client.default import DefaultBotProperties
from aiogram.exceptions import TelegramBadRequest, TelegramForbiddenError, TelegramRetryAfter
from aiogram.filters import Command
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.types import (BotCommand, CallbackQuery, InlineKeyboardButton, InlineKeyboardMarkup, KeyboardButton,
                           LinkPreviewOptions, Message, ReplyKeyboardMarkup)
from curl_cffi.requests import AsyncSession

ROOT = Path(__file__).parent
if (ROOT / ".env").exists():
    for line in (ROOT / ".env").read_text(encoding="utf-8").splitlines():
        k, _, v = line.partition("=")
        if k.strip() and not k.lstrip().startswith("#"):
            os.environ.setdefault(k.strip(), v.strip())

_ids = [int(x) for x in re.findall(r"\d+", os.getenv("ALLOWED_USERS", ""))]
ALLOWED = set(_ids)
ADMIN = _ids[0] if _ids else None  # первый id в ALLOWED_USERS — управляет общими прокси
INTERVAL = int(os.getenv("POLL_INTERVAL", "60"))
PROXY_LIST = [p.strip() for p in os.getenv("PROXIES", "").split(",") if p.strip()]  # общий прокси для всех площадок
PROXIES = itertools.cycle(PROXY_LIST or [None])
TZ = ZoneInfo(os.environ["TIMEZONE"]) if os.getenv("TIMEZONE") else None  # None — часовой пояс компьютера
MAX_PER_CYCLE = 10  # карточек за проверку на задачу по умолчанию; свой лимит чата — /limit
LIMITS = (5, 10, 20, 30, 50)
SEEN_TTL = 2 * 86400  # объявление пропало из выдачи на 2 суток — забываем его
CAPTION_MAX = 1024  # лимит Telegram на подпись к фото

log = logging.getLogger("parser")
db = sqlite3.connect(ROOT / "parser.db", check_same_thread=False)
db.row_factory = sqlite3.Row

# --- Схема (сразу с новыми колонками) ---
db.executescript("""
create table if not exists tasks(
    id integer primary key,
    chat_id int,
    site text,
    query text,
    country text,
    pmin real,
    pmax real,
    active int default 1,
    primed int default 0,
    max_age int,
    min_reviews int default 0,
    min_account_days int default 0,
    contacts_only int default 0,
    private_only int default 0
);
create table if not exists seen(task_id int, item_id text, ts real, primary key(task_id, item_id));
create table if not exists hidden(chat_id int, site text, seller text, name text, primary key(chat_id, site, seller));
create table if not exists sent(chat_id int, item text, ts real, task_id int, primary key(chat_id, item));
create table if not exists proxies(chat_id int, site text, geo text, url text, primary key(chat_id, site, geo));
create table if not exists marks(site text, max_id int, ts real);
create table if not exists settings(chat_id int primary key, max_per_cycle int);
create index if not exists marks_idx on marks(site, max_id);
""")

# --- Безопасная миграция для старых БД ---
_existing_cols = {row[1] for row in db.execute("pragma table_info(tasks)").fetchall()}
for _col, _ddl in [
    ("min_reviews", "integer default 0"),
    ("min_account_days", "integer default 0"),
    ("contacts_only", "integer default 0"),
    ("private_only", "integer default 0"),
]:
    if _col not in _existing_cols:
        db.execute(f"alter table tasks add column {_col} {_ddl}")
if "ts" not in {row[1] for row in db.execute("pragma table_info(seen)")}:
    db.execute("alter table seen add column ts real")
    db.execute("update seen set ts=?", (time.time(),))
db.execute("create index if not exists seen_ts on seen(task_id, ts)")
if "name" not in {row[1] for row in db.execute("pragma table_info(hidden)")}:
    db.execute("alter table hidden add column name text")
if "task_id" not in {row[1] for row in db.execute("pragma table_info(sent)")}:
    db.execute("alter table sent add column task_id int")
if "chat_id" not in {row[1] for row in db.execute("pragma table_info(proxies)")}:
    # прокси стали личными (chat_id; 0 — общий): добавленные раньше достаются админу, админа нет — общими
    db.execute("alter table proxies rename to proxies_old")
    db.execute("create table proxies(chat_id int, site text, geo text, url text, primary key(chat_id, site, geo))")
    db.execute("insert into proxies select ?, site, geo, url from proxies_old", (ADMIN or 0,))
    db.execute("drop table proxies_old")
db.commit()

last_error: dict[int, str] = {}  # текущая проблема задачи: полный отказ или часть стран
alerted: dict[int, str] = {}  # о каком состоянии ("fail"/"partial") уже написали в чат
streak: dict[int, tuple] = {}  # (состояние, сколько проверок подряд оно держится)
ALERT_AFTER = 2  # о поломке пишем, только если она держится 2 проверки подряд: разовый таймаут — не повод


class SellerRetry(RuntimeError):
    """Профиль продавца временно недоступен (429/сеть) — объявления проверим в следующем цикле."""


def fetch_result(out, errors, total):
    """errors — [(страна/рынок, текст)]. Упало всё — исключение, упала часть — вернём текст вместе с объявлениями."""
    by_msg: dict[str, list] = {}
    for where, msg in errors:
        by_msg.setdefault(msg[:120], []).append(where)
    text = "; ".join(f"{', '.join(w)}: {m}" for m, w in by_msg.items())
    if errors and len(errors) == total:
        raise RuntimeError(text)
    return out, text


def items_of(d, *path):
    """Список объявлений из ответа по пути ключей. Нет ключа — формат сменился: падаем громко, а не отдаём [] молча."""
    for k in path:
        if not isinstance(d, dict) or k not in d:
            raise RuntimeError(f"формат ответа изменился: нет поля {'.'.join(path)}")
        d = d[k]
    if not isinstance(d, list):
        raise RuntimeError(f"формат ответа изменился: {'.'.join(path)} — не список")
    return d


def parse_each(raw, parse, where):
    """Разбирает объявления по одному: кривое пропускаем; не разобралось ни одно — формат ответа изменился."""
    out, bad = [], []
    for o in raw:
        try:
            item = parse(o)
        except (KeyError, TypeError, ValueError, AttributeError, IndexError) as e:
            bad.append(f"{type(e).__name__}: {e}")
            continue
        if item:  # None — объявление отсеяно правилами площадки (платное, поднятое…)
            item["src"] = where  # страна/рынок выдачи: по нему check узнаёт рынок, ответивший впервые
            out.append(item)
    if bad and len(bad) == len(raw):
        raise RuntimeError(f"формат ответа изменился ({where}): {bad[0]}")
    if bad:
        log.warning("%s: пропущено кривых объявлений %s из %s — %s", where, len(bad), len(raw), bad[0])
    return out

# ---------- Контакты ----------

EMAIL_REGEX = re.compile(r'\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b')
# международный формат с «+» — для всех стран. Разделители — пробел/таб/nbsp, но не перенос строки:
# иначе к номеру приклеиваются цифры со следующей строки («+34 612 345 678\n100% original»)
PHONE_REGEX = re.compile(r'\+\d[\d \t\xa0().-]{6,20}\d')
# Местные форматы мобильных без кода страны: (начало, сколько ещё цифр, код страны[, внутренний префикс]).
# Применяются только для страны продавца/задачи. Внутренний префикс (обычно 0, в Казахстане 8) в международном
# номере отбрасывается. Городские не берём: слишком много совпадений с артикулами и IBAN.
LOCAL_PHONES = {
    "es": (r"[67]", "{8}", "34"),
    "pt": (r"9[1236]", "{7}", "351"),
    "it": (r"3", "{9}", "39"),
    "fr": (r"0[67]", "{8}", "33"),
    "be": (r"04", "{8}", "32"),
    "nl": (r"06", "{8}", "31"),
    "de": (r"01[5-7]\d", "{7,8}", "49"),
    "at": (r"06[5-9]", "{7,10}", "43"),
    "pl": (r"[4-8]", "{8}", "48"),
    "gb": (r"07", "{9}", "44"),
    "ie": (r"08[35-9]", "{7}", "353"),
    "au": (r"04", "{8}", "61"),
    "us": (r"\(?[2-9]\d\d\)?", "{7}", "1"),
    "ca": (r"\(?[2-9]\d\d\)?", "{7}", "1"),
    "ro": (r"07", "{8}", "40"),
    "bg": (r"08[789]", "{7}", "359"),
    "ua": (r"0[3-9]\d", "{7}", "380"),
    "uz": (r"9\d", "{7}", "998"),
    "kz": (r"8[ \t\xa0.-]?\(?7\d\d\)?", "{7}", "7", "8"),
}
_LOCAL_RE = {cc: (re.compile(rf"(?<![\w+]){start}(?:[ \t\xa0.-]?\d){rest}(?!\d)"), code, trunk[0] if trunk else "0")
             for cc, (start, rest, code, *trunk) in LOCAL_PHONES.items()}


def extract_contacts(text, countries=()) -> dict:
    text = text or ""
    phones = ["+" + re.sub(r'\D', '', p) for p in PHONE_REGEX.findall(text)]
    for cc in countries:
        if cc in _LOCAL_RE:
            rx, code, trunk = _LOCAL_RE[cc]
            phones += ["+" + code + re.sub(r'\D', '', p).removeprefix(trunk) for p in rx.findall(text)]
    return {"emails": list(dict.fromkeys(EMAIL_REGEX.findall(text))),
            "phones": list(dict.fromkeys(p for p in phones if 9 <= len(p) <= 16))}  # E.164: 8–15 цифр

# ---------- HTTP ----------

_sessions: dict[str, AsyncSession] = {}
_locks: dict[str, asyncio.Lock] = {}


async def get_json(key, impersonate, url, params=None, headers=None, warmup=None, proxy=None):
    key = f"{key}|{proxy}"  # у пользователей свои прокси — сессии (куки, IP) не смешиваем
    async with _locks.setdefault(key, asyncio.Lock()):
        s = _sessions.get(key)
        try:
            if s is None:
                s = _sessions[key] = AsyncSession(
                    impersonate=impersonate, proxy=proxy or next(PROXIES), timeout=20
                )
                if warmup:
                    await s.get(warmup)
            r = await s.get(url, params=params, headers=headers)
            if r.status_code != 200:
                raise RuntimeError(f"HTTP {r.status_code}")
            try:
                return r.json()
            except ValueError:
                raise RuntimeError("ответ не JSON (капча/заглушка)") from None
        except Exception:
            # любая ошибка (статус, таймаут, мёртвый прокси, заглушка) — новая сессия на следующем прокси
            _sessions.pop(key, None)
            if s is not None:
                try:
                    await s.close()
                except Exception:
                    pass
            raise

# ---------- Depop ----------

DEPOP_CURRENCY = {"gb": "GBP", "us": "USD", "au": "AUD", "de": "EUR", "fr": "EUR", "it": "EUR", "ie": "EUR"}


async def depop_mobile_search(params):
    # Мобильного API api.depop.com нет (404). Работает поиск сайта; Cloudflare пропускает firefox-отпечаток,
    # но с «плохих» IP отвечает 403 — тогда нужен резидентский прокси (/proxy или PROXIES).
    return await get_json(
        f"depop_{params['country']}",
        "firefox",
        "https://www.depop.com/presentation/api/v1/search/products/",
        params,
        {"Accept": "application/json", "Referer": "https://www.depop.com/"},
        proxy=proxy_for("depop", params["country"]),
    )


async def depop_user_profile(user_id: str):
    return await get_json(
        "depop_user",  # одна сессия на все профили (раньше — новая незакрытая сессия на каждого продавца)
        "safari",
        f"https://api.depop.com/api/v1/users/{user_id}/",
        headers={"Accept": "application/json"},
        proxy=proxy_for("depop"),  # профили не привязаны к стране: любой прокси Depop пользователя
    )


async def depop(t):
    out, errors = [], []
    countries = (t["country"] or ",".join(COUNTRIES["depop"])).split(",")
    for c in countries:
        params = {  # пустой запрос — все объявления: «what» не шлём вовсе, как в calibrate
            **({"what": t["query"]} if t["query"] else {}),
            "limit": 24,
            "country": c,
            "currency": DEPOP_CURRENCY.get(c, "EUR"),
            "ranking": "recent",
            "from": "in_country_search",
        }
        if t["pmin"]:
            params["price_min"] = t["pmin"]
        if t["pmax"]:
            params["price_max"] = t["pmax"]

        try:
            d = await depop_mobile_search(params)
            out += parse_each(items_of(d, "objects"), depop_item, c)
        except Exception as e:
            log.warning(f"Depop search error {c}: {e}")
            errors.append((c, str(e)))
    return fetch_result(out, errors, len(countries))


def depop_item(o):
    sizes = ", ".join(s["name"] for s in o.get("sizes") or [])
    cond = (o.get("attributes") or {}).get("condition", "").replace("_", " ")
    seller = o.get("seller") or {}
    seller_id = seller.get("id")
    return dict(
        id=str(o["id"]),
        title=(o.get("description") or o.get("slug", "")).split("\n")[0][:100],
        price=float(o["pricing"]["current_price"]["price_breakdown"]["price"]["amount"]),
        currency=o["pricing"]["currency"],
        brand=o.get("brand_name") or "",
        details=" · ".join(filter(None, [sizes, cond])),
        location=o.get("location") or "",
        photo=next(iter(o["preview"]["formats"].values()))["url"] if o.get("preview") else None,
        url=f"https://www.depop.com/products/{o['slug']}/",
        market="depop",
        seller_id=str(seller_id) if seller_id else None,
        seller_username=seller.get("username"),
        description=o.get("description"),
    )

# ---------- Vinted ----------

VINTED_EU = ["de", "fr", "it", "es", "nl", "be", "at", "pl", "cz", "lt", "lu", "pt", "sk", "hu", "ro", "se", "dk",
             "fi", "gr", "hr", "ie"]

VINTED_MOBILE_HEADERS = {
    "Accept": "application/json",
    "User-Agent": "Vinted/23.10.2 (Linux; Android 13; SM-G998B)",
    "Accept-Language": "en-US",
    "Accept-Encoding": "gzip, deflate",
    "X-App-Version": "23.10.2",
    "X-Platform": "android",
}


def vinted_countries(t):
    return set(t["country"].split(",")) if t["country"] else set(VINTED_EU)


def vinted_markets(t):
    # Каталог Vinted подбирается по IP покупателя: с немецкого IP испанских продавцов в выдаче нет.
    # Если для Vinted ES назначен свой прокси — Испанию ищем отдельным каталогом vinted.es через испанский IP.
    c = vinted_countries(t)
    es_own = "es" in c and bool(own_proxy("vinted", "es", t["chat_id"]))
    markets = []
    if c & set(VINTED_EU) - ({"es"} if es_own else set()):
        markets.append("vinted.de")
    if es_own:
        markets.append("vinted.es")
    if "us" in c:
        markets.append("vinted.com")
    return markets


async def vinted_mobile_call(market, path, params=None):
    tld = market.split(".", 1)[1]
    url = f"https://{'api' if path.startswith('/svc-') else 'www'}.vinted.{tld}{path}"  # поиск — api, профили — www
    proxy = proxy_for("vinted", VINTED_GEO[market])
    return await get_json(
        f"vinted_mobile_{market}",
        "chrome",
        url,
        params,
        VINTED_MOBILE_HEADERS,
        warmup=f"https://www.vinted.{tld}/",
        proxy=proxy,
    )


async def vinted_user_profile(market, user_id):
    data = await vinted_mobile_call(market, f"/api/v2/users/{user_id}")
    return data.get("user", {})


async def vinted(t):
    # 96 — максимум Vinted: по популярным запросам за минуту выходит ~60 новых, при 24 большая часть терялась
    params = {"search_text": t["query"], "order": "newest_first", "per_page": 96}
    if t["pmin"]:
        params["price_from"] = t["pmin"]
    if t["pmax"]:
        params["price_to"] = t["pmax"]

    out, errors = [], []
    markets = vinted_markets(t)
    for market in markets:
        try:
            d = await vinted_mobile_call(market, "/svc-catalogue/items", params)
            out += parse_each(items_of(d, "items"), lambda i: vinted_item(i, market), market)
        except Exception as e:
            log.warning(f"Vinted search error {market}: {e}")
            errors.append((market, str(e)))
    return fetch_result(out, errors, len(markets))


def vinted_item(i, market):
    user_data = i.get("user") or {}
    return dict(
        id=str(i["id"]),
        title=i.get("title", ""),
        price=float(i["price"]["amount"]),
        currency=i["price"]["currency_code"],
        brand=(i.get("item_box") or {}).get("first_line") or "",
        details=(i.get("item_box") or {}).get("second_line") or "",
        location="🇺🇸" if market == "vinted.com" else "",
        photo=(i.get("photo") or {}).get("url"),
        url=urljoin(f"https://www.{market}/", i["url"]),
        seller_id=user_data.get("id"),
        seller_username=user_data.get("login"),
        seller_business=bool(user_data.get("business")),
        market=market,
    )

# ---------- Кэш продавцов ----------

_sellers_cache: dict = {}


def get_seller_cache_key(site, seller_id):
    return f"{site}_{seller_id}"


def _to_dt(value):
    if value is None:
        return None
    if isinstance(value, (int, float)):
        try:
            return datetime.datetime.fromtimestamp(value, tz=datetime.timezone.utc)
        except Exception:
            return None
    if isinstance(value, str):
        try:
            dt = datetime.datetime.fromisoformat(value.replace("Z", "+00:00"))
            return dt if dt.tzinfo else dt.replace(tzinfo=datetime.timezone.utc)  # без пояса — считаем UTC
        except Exception:
            return None
    return None


async def get_seller_info(site, seller_id, market=None, need_age=False):
    """Данные продавца, кэш на час. None — профиль не загрузился: не кэшируем, попробуем в следующий раз.
    need_age — нужен точный возраст аккаунта: для Vinted это лишний запрос отзывов, без фильтра его не делаем."""
    if not seller_id:
        return None

    key = get_seller_cache_key(site, seller_id)
    cached = _sellers_cache.get(key)
    if cached and (cached["age_checked"] or not need_age):
        return cached

    info = {
        "reviews": 0,
        "created_at": None,
        "bio": "",
        "account_days": None,  # None — площадка не отдала дату регистрации
        "country": "",
        "city": "",
        "age_checked": site != "vinted" or need_age,
    }

    try:
        if site == "vinted":
            user_data = await vinted_user_profile(market or "vinted.de", seller_id)
            if user_data:
                info["reviews"] = user_data.get("feedback_count", 0) or user_data.get("positive_feedback_count", 0)
                # Даты регистрации Vinted не отдаёт. Берём самое раннее, что известно об аккаунте: первый отзыв
                # и даты привязки соцсетей. Это нижняя граница — аккаунт точно не моложе.
                dates = [v.get("verified_at") for v in (user_data.get("verification") or {}).values() if isinstance(v, dict)]
                if need_age and user_data.get("feedback_count"):  # отзывы от новых к старым: последняя страница по 1 = первый
                    fb = await vinted_mobile_call(market or "vinted.de", "/api/v2/user_feedbacks",
                                                  {"user_id": seller_id, "page": user_data["feedback_count"], "per_page": 1})
                    dates += [f.get("created_at_ts") for f in fb.get("user_feedbacks", [])]  # created_at — локализованный текст
                dates = [d for d in map(_to_dt, dates) if d]
                info["created_at"] = user_data.get("created_at") or (min(dates).isoformat() if dates else None)
                info["account_days_min"] = not user_data.get("created_at")
                info["bio"] = user_data.get("bio", "") or user_data.get("about", "") or ""
                info["business"] = bool(user_data.get("business"))
                info["country"] = (user_data.get("country_code") or "").lower()
                info["city"] = user_data.get("city") or ""
        elif site == "poshmark":
            d = await get_json(market, "chrome", f"https://{market}/vm-rest/users/{seller_id}",
                               headers={"Accept": "application/json"},
                               proxy=proxy_for("poshmark", {v: k for k, v in POSHMARK.items()}[market]))
            if "error" in d:  # vm-rest отвечает 200 и кладёт код ошибки внутрь
                raise RuntimeError(f"HTTP {d['error'].get('statusCode')}")
            user_data = d.get("data") or {}
            profile = user_data.get("profile_v2") or {}
            # отзывов (Love Notes) API не отдаёт — вместо них число проданных заказов
            info["reviews"] = (user_data.get("aggregates") or {}).get("seller_orders_shipped", 0)
            info["created_at"] = user_data.get("created_at")
            info["bio"] = profile.get("description") or ""
            info["country"] = user_data.get("home_domain") or ""
            info["city"] = ", ".join(filter(None, [profile.get("city"), profile.get("state")]))
        elif site == "wallapop":
            user_data = await wallapop_get(f"/users/{seller_id}")
            stats = await wallapop_get(f"/users/{seller_id}/stats")
            info["reviews"] = next((c["value"] for c in stats.get("counters", []) if c.get("type") == "reviews"), 0)
            info["created_at"] = user_data["register_date"] / 1000 if user_data.get("register_date") else None
            loc = user_data.get("location") or {}
            info["country"] = (loc.get("country_code") or "").lower()
            info["city"] = loc.get("city") or ""
            # У магазинов и PRO-аккаунтов Wallapop публичная карточка бизнеса: телефон, описание, адрес, сайт
            shop = user_data.get("extra_info") or {}
            digits = re.sub(r"\D", "", shop.get("phone_number") or "")
            if len(digits) == 9 or (len(digits) == 11 and digits.startswith("34")):
                info["phones"] = ["+" + digits if len(digits) == 11 else "+34" + digits]
            info["bio"] = shop.get("description") or ""
            info["business"] = user_data.get("type") == "professional"
            info["name"] = user_data.get("micro_name")
            try:  # что продавец подтвердил для самого Wallapop; покупателям номер и почту площадка не показывает
                checks = (await wallapop_get(f"/users/{seller_id}/extra-info")).get("validations") or {}
                info["verified"] = [name for key, name in (("email", "почта"), ("mobile", "телефон"), ("kyc", "личность"))
                                    if checks.get(key) is True]
            except Exception as e:  # отметки — только украшение карточки, без них продавец всё равно годится
                log.info("wallapop extra-info %s: %s", seller_id, e)
        elif site == "depop":
            user_data = await depop_user_profile(seller_id)
            if user_data:
                info["reviews"] = user_data.get("reviews_count", 0) or user_data.get("reviews_total_count", 0)
                info["created_at"] = user_data.get("signup_date") or user_data.get("created_at")
                info["bio"] = user_data.get("bio", "") or ""
    except Exception as e:
        log.warning(f"Error fetching seller info {site} {seller_id}: {e}")
        if str(e) not in ("HTTP 404", "HTTP 410"):  # 404/410 — профиля нет совсем, ждать бесполезно
            raise SellerRetry(f"профиль продавца: {e}") from e
        return None

    created = _to_dt(info["created_at"])
    if created:
        info["account_days"] = (datetime.datetime.now(datetime.timezone.utc) - created).days

    _sellers_cache[key] = info
    asyncio.create_task(clear_seller_cache(key, 3600))
    return info


async def clear_seller_cache(key, delay):
    await asyncio.sleep(delay)
    _sellers_cache.pop(key, None)

# ---------- Poshmark ----------

POSHMARK = {"us": "poshmark.com", "ca": "poshmark.ca"}


async def poshmark(t):
    out, errors = [], []
    countries = (t["country"] or ",".join(POSHMARK)).split(",")
    for c in countries:
        host = POSHMARK[c]
        req = {
            "filters": {"department": "All", "inventory_status": ["available"]},
            "query": t["query"],
            "sort_by": "added_desc",
            "count": 48,
        }
        try:
            d = await get_json(
                host,
                "chrome",
                f"https://{host}/vm-rest/posts",
                {"request": json.dumps(req), "summarize": "true"},
                {"Accept": "application/json"},
                proxy=proxy_for("poshmark", c),
            )
            if "error" in d:  # vm-rest отвечает 200 и кладёт код ошибки внутрь
                raise RuntimeError(f"HTTP {d['error'].get('statusCode')}")
            out += parse_each(items_of(d, "data"), lambda o: poshmark_item(o, c, host), c)
        except Exception as e:
            log.warning(f"Poshmark error {c}: {e}")
            errors.append((c, str(e)))
    return fetch_result(out, errors, len(countries))


def poshmark_item(o, c, host):
    sizes = ", ".join(sq["size_obj"]["display"] for sq in (o.get("inventory") or {}).get("size_quantities") or [])
    return dict(
        id=str(o["id"]),
        title=o.get("title", ""),
        price=float(o["price_amount"]["val"]),
        currency=o["price_amount"]["currency_code"],
        brand=o.get("brand") or "",
        details=sizes,
        location=flag(c),
        photo=(o.get("cover_shot") or {}).get("url"),
        url=f"https://{host}/listing/{o['id']}",
        market=host,
        seller_id=o.get("creator_id"),
        seller_username=o.get("creator_username"),
        description=o.get("description"),
        ts=datetime.datetime.fromisoformat(o["first_published_at"]).timestamp()
            if o.get("first_published_at") else time.time(),
    )


# ---------- Wallapop ----------

WALLAPOP_HEADERS = {"Accept": "application/json", "X-DeviceOS": "0"}  # без X-DeviceOS API отвечает 403


async def wallapop_get(path, params=None):
    return await get_json("wallapop", "chrome", f"https://api.wallapop.com/api/v3{path}", params, WALLAPOP_HEADERS,
                          proxy=proxy_for("wallapop", "es"))


async def wallapop(t):
    # координаты — центр Испании: без них API берёт точку по гео-IP (с немецкого IP — Франкфурт)
    params = {"keywords": t["query"], "order_by": "newest", "source": "search_box",
              "latitude": 40.4168, "longitude": -3.7038}
    if t["pmin"]:
        params["min_sale_price"] = t["pmin"]
    if t["pmax"]:
        params["max_sale_price"] = t["pmax"]
    # Индекс поиска Wallapop обновляется пачками раз в ~5 мин: за это время по популярному запросу выходит
    # больше 40 (одна страница), поэтому берём 2 страницы
    d = await wallapop_get("/search", params)
    items = items_of(d, "data", "section", "payload", "items")
    if (d.get("meta") or {}).get("next_page"):
        d = await wallapop_get("/search", {"next_page": d["meta"]["next_page"]})
        items += items_of(d, "data", "section", "payload", "items")
    countries = set((t["country"] or "es").split(","))
    return parse_each(items, lambda i: wallapop_item(i, countries), "es"), ""


def wallapop_item(i, countries):
    loc = i.get("location") or {}
    if (loc.get("country_code") or "es").lower() not in countries:  # в выдачу попадает и Италия
        return None
    return dict(
        id=str(i["id"]),
        title=i.get("title", ""),
        price=float(i["price"]["amount"]),
        currency=i["price"]["currency"],
        brand="",
        details="",
        location=", ".join(filter(None, [loc.get("city"), flag((loc.get("country_code") or "").lower())])),
        photo=((i.get("images") or [{}])[0].get("urls") or {}).get("medium"),
        url=f"https://es.wallapop.com/item/{i['web_slug']}",
        market="wallapop",
        seller_id=i.get("user_id"),
        description=i.get("description"),
        ts=i["created_at"] / 1000 if i.get("created_at") else time.time(),
    )

# ---------- Milanuncios ----------


async def milanuncios(t):
    # Сайт закрыт защитой от ботов, но поисковый API отвечает. Профиля продавца в API нет — только имя и тип.
    # пустой «text» API понимает как «ничего не нашлось» — для всех объявлений поле не шлём
    params = {**({"text": t["query"]} if t["query"] else {}), "orderBy": "date", "limit": 60}
    if t["pmin"]:
        params["priceFrom"] = t["pmin"]
    if t["pmax"]:
        params["priceTo"] = t["pmax"]
    d = await get_json("milanuncios", "chrome", "https://searchapi.gw.milanuncios.com/v3/classifieds", params,
                       {"Accept": "application/json", "Origin": "https://www.milanuncios.com",
                        "Referer": "https://www.milanuncios.com/"}, proxy=proxy_for("milanuncios", "es"))
    photos = {p["adId"]: p.get("imageUrls") or [] for p in d.get("photos", [])}
    return parse_each(items_of(d, "ads"), lambda a: milanuncios_item(a, photos), "es"), ""


def milanuncios_item(a, photos):
    # «куплю», платные «выделенные» и «поднятые» (sortDate ≠ publicationDate): поднятые старые объявления
    # встают в выдачу как новые, хотя созданы дни и месяцы назад
    if (a.get("transaction", "supply") != "supply" or a.get("isHighlighted")
            or a.get("sortDate", a.get("publicationDate")) != a.get("publicationDate")):
        return None
    loc = a.get("location") or {}
    imgs = photos.get(a["id"])
    posted = _to_dt(a.get("publicationDate"))
    value = ((a.get("price") or {}).get("cash") or {}).get("value")
    return dict(
        id=str(a["id"]),
        title=a.get("title", ""),
        price=float(value) if value else None,  # None — «цена по запросу»
        currency="EUR",
        brand="",
        details=", ".join(x["value"]["formatted"] for x in a.get("attributes") or []
                          if x.get("field", {}).get("raw") == "itemCondition"),
        location=", ".join(filter(None, [(loc.get("city") or {}).get("name"),
                                         (loc.get("province") or {}).get("name"), flag("es")])),
        photo=f"https://{imgs[0]}?rule=hw545" if imgs else None,  # без rule — 404
        url=urljoin("https://www.milanuncios.com/", a["url"]),
        market="milanuncios",
        seller_id=a.get("authorId"),
        seller_name=a.get("authorName") or "?",
        seller_business=a.get("type") == "professional",
        phone_hidden=bool((a.get("contactMethods") or {}).get("phone")),  # номер показывают только на сайте
        country="es",
        description=a.get("description"),
        ts=posted.timestamp() if posted else time.time(),
    )


# ---------- OLX ----------

OLX = {"pl": "www.olx.pl", "pt": "www.olx.pt", "ro": "www.olx.ro", "bg": "www.olx.bg", "ua": "www.olx.ua",
       "kz": "www.olx.kz", "uz": "www.olx.uz"}
OLX_CURRENCY = {"pl": "PLN", "pt": "EUR", "ro": "RON", "bg": "EUR", "ua": "UAH", "kz": "KZT", "uz": "UZS"}


async def olx(t):
    out, errors = [], []
    countries = (t["country"] or ",".join(OLX)).split(",")
    now = datetime.datetime.now(datetime.timezone.utc)
    for c in countries:
        host = OLX[c]
        # sort_by=created_at:desc на деле сортирует по «обновлению»: наверху и новые, и поднятые старые
        params = {"query": t["query"], "sort_by": "created_at:desc", "limit": 50}
        if t["pmin"]:
            params["filter_float_price:from"] = t["pmin"]
        if t["pmax"]:
            params["filter_float_price:to"] = t["pmax"]
        try:
            d = await get_json(host, "chrome", f"https://{host}/api/v1/offers/", params, {"Accept": "application/json"},
                               proxy=proxy_for("olx", c))
            out += parse_each(items_of(d, "data"), lambda o: olx_item(o, c, host, now), c)
        except Exception as e:
            log.warning(f"OLX error {c}: {e}")
            errors.append((c, str(e)))
    return fetch_result(out, errors, len(countries))


def olx_item(o, c, host, now):
    created, refreshed = _to_dt(o.get("created_time")), _to_dt(o.get("last_refresh_time"))
    # платные «топ», «куплю», поднятые старые (обновлены позже чем через час после создания)
    # и возобновлённые после истечения (созданы больше суток назад) — не новые
    if ((o.get("promotion") or {}).get("top_ad") or o.get("offer_type", "offer") != "offer" or not created
            or (refreshed and (refreshed - created).total_seconds() > 3600)
            or (now - created).total_seconds() > 86400):
        return None
    price = next((p["value"] for p in o.get("params") or [] if p.get("key") == "price"), None) or {}
    # обмен и «без цены» числа не имеют: показываем словами и не пропускаем через фильтр цены
    value = price.get("value") if price.get("type") != "exchange" else None
    note = "обмен" if price.get("type") == "exchange" else "торг" if price.get("arranged") or price.get("negotiable") else None
    user = o.get("user") or {}
    joined = _to_dt(user.get("created"))
    loc = o.get("location") or {}
    photo = (o.get("photos") or [None])[0]
    return dict(
        id=str(o["id"]),
        title=o.get("title", ""),
        price=float(value) if value else None,
        price_note=note,
        currency=price.get("currency") or OLX_CURRENCY[c],
        brand="",
        details="",
        location=", ".join(filter(None, [(loc.get("city") or {}).get("name"),
                                         (loc.get("region") or {}).get("name"), flag(c)])),
        photo=photo["link"].replace("{width}x{height}", "1000x1000") if photo else None,  # оригинал до 4000px
        url=o["url"],
        market=host,
        country=c,
        seller_id=user.get("id"),
        seller_name=user.get("name") or "?",
        contact_name=(o.get("contact") or {}).get("name"),  # магазины пишут сюда телефон: «DirectGsm - 0723.777.774»
        seller_business=bool(o.get("business")),
        phone_hidden=bool((o.get("contact") or {}).get("phone")),  # номер OLX отдаёт только после входа
        seller_account_days=(now - joined).days if joined else None,
        description=html.unescape(re.sub(r"<[^>]+>", " ", o.get("description") or "")),  # без тегов и &amp;
        ts=created.timestamp(),
    )


SITES = {"depop": depop, "vinted": vinted, "poshmark": poshmark, "wallapop": wallapop, "milanuncios": milanuncios,
         "olx": olx}
# площадки, чей поиск отдаёт новые объявления с задержкой (замерено): (сколько ждать, мин. разумная свежесть)
SLOW_FEED = {"wallapop": ("1–6 мин", 15), "olx": ("7–20 мин", 30)}
COUNTRIES = {
    "depop": ["gb", "us", "au", "de", "fr", "it", "ie"],
    "vinted": VINTED_EU + ["us"],
    "poshmark": list(POSHMARK),
    "wallapop": ["es"],
    "milanuncios": ["es"],
    "olx": list(OLX),
}

# ---------- Прокси по площадкам ----------

# страны, для которых можно назначить свой прокси; у Vinted — каталоги: eu (vinted.de), es (vinted.es), us (vinted.com)
PROXY_GEOS = {**COUNTRIES, "vinted": ["eu", "es", "us"]}
VINTED_GEO = {"vinted.de": "eu", "vinted.es": "es", "vinted.com": "us"}


current_chat: ContextVar[int] = ContextVar("current_chat", default=0)  # чья задача сейчас ходит в сеть; 0 — ничья


def own_proxy(site, geo, chat):
    """Прокси ровно этой страны: свой, иначе общий (chat_id=0)."""
    row = db.execute("select url from proxies where site=? and geo=? and chat_id in (?, 0) order by chat_id=0 limit 1",
                     (site, geo, chat)).fetchone()
    return row[0] if row else None


def proxy_for(site, geo=None, chat=None):
    """Свой прокси (страны → «все страны»), иначе общий (так же). geo=None — любой прокси площадки, «все страны»
    первым. chat по умолчанию — владелец текущей задачи. None — общий PROXIES из .env (или без прокси)."""
    chat = current_chat.get() if chat is None else chat
    if geo:
        where, args = "geo in (?, '*') order by chat_id=0, geo='*'", (geo,)
    else:
        where, args = "1 order by chat_id=0, geo!='*'", ()
    row = db.execute(f"select url from proxies where site=? and chat_id in (?, 0) and {where} limit 1",
                     (site, chat, *args)).fetchone()
    return row[0] if row else None


def has_proxy(site, geo, chat):
    return bool(proxy_for(site, geo, chat) or PROXY_LIST)


def mask_proxy(url):
    return re.sub(r"//([^:@/]+):[^@/]+@", r"//\1:***@", url)


async def reset_sessions():
    """Прокси поменялись — закрываем сессии: следующие запросы откроют новые уже через нужный прокси."""
    for key in list(_sessions):
        async with _locks.setdefault(key, asyncio.Lock()):
            s = _sessions.pop(key, None)
            if s:
                try:
                    await s.close()
                except Exception:
                    pass


def proxy_notes(site, countries, chat):
    """Предупреждения при запуске задачи: площадка с этого IP не работает без прокси."""
    notes = []
    if site == "depop" and not all(has_proxy("depop", c, chat) for c in countries):
        notes.append("🔒 <b>Depop без прокси не работает:</b> отвечает 403 на обычные домашние и серверные IP. "
                     "Нужен резидентский прокси — добавь через /proxy.")
    if site == "vinted" and "us" in countries and not has_proxy("vinted", "us", chat):
        notes.append("🔒 <b>Vinted США</b> (vinted.com) пускает только американские IP — добавь прокси США: "
                     "/proxy → VINTED → US.")
    if site == "vinted" and "es" in countries and len(countries) < len(COUNTRIES["vinted"]) \
            and not own_proxy("vinted", "es", chat):
        notes.append("ℹ️ Испания ищется в общем каталоге ЕС — испанских продавцов там мало. Для полного каталога "
                     "vinted.es нужен прокси с IP Испании: /proxy → VINTED → ES.")
    return notes


def flag(cc):
    return "".join(chr(0x1F1E6 + ord(ch) - ord("a")) for ch in cc) if re.fullmatch(r"[a-z]{2}", cc or "") else ""

# ---------- Фильтрация ----------


async def should_show_item(item, t, site):
    now = time.time()

    if (t["pmin"] or t["pmax"]) and item["price"] is None:  # обмен / цена не указана — под фильтр цены не подходит
        return False, None
    if t["pmin"] and item["price"] < t["pmin"]:
        return False, None
    if t["pmax"] and item["price"] > t["pmax"]:
        return False, None

    item_age_min = (now - item["ts"]) / 60
    if t["max_age"] and item_age_min > t["max_age"]:
        return False, None
    item["posted"] = posted_text(item["ts"], item.get("ts_older", False), now)

    if t["private_only"] and item.get("seller_business"):  # Vinted и Milanuncios отдают тип продавца прямо в поиске
        return False, None

    if site in ("milanuncios", "olx"):  # профиля в API нет — всё о продавце приходит прямо в выдаче
        if t["min_account_days"] and (item.get("seller_account_days") or 0) < t["min_account_days"]:
            return False, None
        text = "\n".join(filter(None, [item.get("seller_name"), item.get("contact_name"), item.get("description")]))
        item["contacts"] = extract_contacts(text, [item["country"]])  # имя продавца тоже: магазины пишут туда номер
        if t["contacts_only"] and not any(item["contacts"].values()):
            return False, None
        return True, item

    if site in ("depop", "vinted", "poshmark", "wallapop"):
        # Vinted ЕС: каталог общий на весь ЕС, страну продавца знаем только из его профиля
        by_country = site == "vinted" and item.get("market") != "vinted.com" and not set(VINTED_EU) <= vinted_countries(t)
        need_seller = bool(t["min_reviews"] or t["min_account_days"] or t["contacts_only"] or by_country
                           or (t["private_only"] and "seller_business" not in item))
        seller_id = item.get("seller_id")
        try:
            # Depop без фильтров продавца профиль не грузим: данные только для карточки, а запрос дорогой (403/таймауты)
            seller_info = await get_seller_info(site, seller_id, item.get("market"), bool(t["min_account_days"])) \
                if seller_id and (need_seller or site != "depop") else None
        except SellerRetry:
            if need_seller:
                raise
            seller_info = None
        if seller_info is None:
            if not need_seller:
                return True, item  # фильтров продавца нет — показываем и без данных о нём
            return False, None  # продавца нет в выдаче или профиль удалён — проверить фильтры нельзя

        if seller_info.get("country"):
            item["location"] = ", ".join(filter(None, [seller_info.get("city"), flag(seller_info["country"])]))
        if by_country and seller_info.get("country") not in vinted_countries(t):
            return False, None
        if t["min_reviews"] and seller_info["reviews"] < t["min_reviews"]:
            return False, None
        if t["min_account_days"]:
            # возраст неизвестен (нет ни отзывов, ни привязанных соцсетей) — подтвердить нельзя, пропускаем
            if seller_info["account_days"] is None or seller_info["account_days"] < t["min_account_days"]:
                return False, None
        business = item.get("seller_business") or seller_info.get("business")
        if t["private_only"] and business:
            return False, None
        # контакты ищем и в профиле, и в описании объявления (у Wallapop описания профиля нет вовсе);
        # местные форматы телефонов — по стране продавца, если она известна, иначе по странам задачи
        countries = [seller_info["country"]] if seller_info.get("country") else \
            (t["country"] or ",".join(COUNTRIES[site])).split(",")
        contacts = extract_contacts(f"{seller_info['bio']}\n{item.get('description') or ''}", countries)
        if seller_info.get("phones"):  # телефон из публичной карточки магазина — точный, без поиска по тексту
            contacts["phones"] = list(dict.fromkeys(seller_info["phones"] + contacts["phones"]))
        if t["contacts_only"] and not any(contacts.values()):
            return False, None

        item["seller_reviews"] = seller_info["reviews"]
        item["seller_account_days"] = seller_info["account_days"]
        item["seller_account_days_min"] = seller_info.get("account_days_min")
        item["contacts"] = contacts
        item["seller_business"] = bool(business)
        item["seller_verified"] = seller_info.get("verified")
        if seller_info.get("name"):  # Wallapop не отдаёт продавца в выдаче — имя из профиля
            item.setdefault("seller_username", seller_info["name"])

    return True, item


def card(t, i):
    e = html.escape
    if i["price"] is None:
        price = e(i.get("price_note") or "цена не указана")
    else:
        price = f"{i['price']:g} {e(i['currency'])}" + (f" ({e(i['price_note'])})" if i.get("price_note") else "")
    lines = [f"<b>{e(i['title'])}</b>", f"💰 <b>{price}</b>"]

    if i.get("brand") or i.get("details"):
        lines.append("🏷 " + e(" · ".join(filter(None, [i["brand"], i["details"]]))))

    if i.get("location"):
        lines.append(f"📍 {e(i['location'])}")

    if "seller_reviews" in i:
        days = i.get("seller_account_days")
        days = "?" if days is None else f"от {days}" if i.get("seller_account_days_min") else days
        at = "@" if t["site"] in ("vinted", "depop", "poshmark") else ""  # у Wallapop не логин, а имя
        who = f" {at}{i['seller_username']}" if i.get("seller_username") else ""
        what = "продаж" if t["site"] == "poshmark" else "отзывов"
        pro = " · профи" if i.get("seller_business") else ""
        verified = f" · ✔️ подтверждены: {', '.join(i['seller_verified'])}" if i.get("seller_verified") else ""
        lines.append(f"👤 Продавец{e(who)}{pro}: {i.get('seller_reviews', 0)} {what} | {days} дней на площадке{verified}")
    elif i.get("seller_name"):
        days = f" | {i['seller_account_days']} дней на площадке" if i.get("seller_account_days") is not None else ""
        lines.append(f"👤 Продавец: {e(i['seller_name'])} · {'профи' if i.get('seller_business') else 'частный'}{days}")

    if "contacts" in i:  # контакты искали — показываем всегда, даже если пусто
        contacts = i["contacts"]
        lines.append(f"✉️ Email: {e(', '.join(contacts.get('emails') or ['не найден']))}")
        site_name = {"olx": "OLX"}.get(t["site"], t["site"].capitalize())
        hidden = f"скрыт {site_name} — есть, смотри в объявлении" if i.get("phone_hidden") else "не найден"
        lines.append(f"📞 Тел: {e(', '.join(contacts.get('phones') or [hidden]))}")

    if i.get("posted"):
        lines.append(f"🕒 {i['posted']}")

    name = {"olx": "OLX"}.get(t["site"], t["site"].capitalize())
    lines.append(f"🔗 <a href=\"{e(i['url'])}\">Открыть на {name}</a>")
    lines.append(f"🔎 #{t['id']}: {e(query_label(t['query']))}")
    return "\n".join(lines)


def seller_kb(site, seller, hidden=False):
    return kb([[("↩️ Вернуть продавца", f"unhide:{site}:{seller}") if hidden else
                ("🚫 Скрыть продавца", f"hide:{site}:{seller}")]])


async def send(bot, t, i):
    text = card(t, i)
    if i.get("photo") and len(text) > CAPTION_MAX:  # подпись к фото — до 1024 символов: укорачиваем название
        cut = len(text) - CAPTION_MAX + 1
        text = card(t, {**i, "title": i["title"][:max(20, len(i["title"]) - cut)] + "…"})
    markup = seller_kb(t["site"], i["seller_id"]) if i.get("seller_id") else None
    for _ in range(3):
        try:
            if i.get("photo"):
                try:
                    return await bot.send_photo(t["chat_id"], i["photo"], caption=text, reply_markup=markup)
                except (TelegramRetryAfter, TelegramForbiddenError):
                    raise
                except Exception as ex:
                    log.info("photo failed for %s: %s", i["url"], ex)
            # превью включаем обоими параметрами: иначе aiogram досылает второй из глобального is_disabled=True
            return await bot.send_message(t["chat_id"], text, reply_markup=markup, disable_web_page_preview=False,
                                          link_preview_options=LinkPreviewOptions(is_disabled=False))
        except TelegramRetryAfter as ex:
            # флуд-лимит Telegram — не сбой задачи: ждём, сколько сказали, и шлём снова
            log.info("telegram flood limit: ждём %s с", ex.retry_after)
            await asyncio.sleep(ex.retry_after + 1)
    raise RuntimeError("Telegram: флуд-лимит не отпускает")


def record_mark(market, top, now):
    cur = db.execute("select max(max_id) from marks where site=?", (market,)).fetchone()[0] or 0
    if top > cur:
        db.execute("insert into marks values(?,?,?)", (market, top, now))
        db.execute("delete from marks where ts < ?", (now - 7 * 86400,))
        db.commit()


def posted_at(market, item_id, now):
    nxt = db.execute(
        "select max_id, ts from marks where site=? and max_id>=? order by max_id limit 1",
        (market, item_id),
    ).fetchone()
    prev = db.execute(
        "select max_id, ts from marks where site=? and max_id<? order by max_id desc limit 1",
        (market, item_id),
    ).fetchone()
    if nxt is None:
        return ((prev[1] + now) / 2 if prev else now), False
    if prev is None:
        return nxt[1], True
    return prev[1] + (item_id - prev[0]) / (nxt[0] - prev[0]) * (nxt[1] - prev[1]), False


def estimate_ts(items, now):
    """Время публикации для площадок без даты (Vinted, Depop) — по id через метки. Выдача отсортирована по
    публикации, а id выдаётся при создании черновика: опубликованный позже черновик имеет «старый» id. Поэтому
    объявление не старше любого, что стоит ниже него в выдаче, — берём максимум по хвосту."""
    floor = {}
    for i in reversed(items):
        if "ts" in i:
            continue
        try:
            ts, older = posted_at(i["market"], int(i["id"]), now)
        except (ValueError, TypeError):
            ts, older = now, False
        if floor.get(i["market"], ts) > ts:
            ts, older = floor[i["market"]], False
        floor[i["market"]] = ts
        i["ts"], i["ts_older"] = ts, older


def posted_text(ts, older, now):
    m = max(0, int(now - ts) // 60)
    ago = ("только что" if m < 1 else
           f"{m} мин назад" if m < 60 else
           f"{m // 60} ч {m % 60} мин назад" if m < 1440 else
           f"{m // 1440} д назад")
    clock = datetime.datetime.fromtimestamp(ts, TZ).strftime("%H:%M")
    if older:  # «больше чем только что» читалось странно — без «назад», если меньше минуты
        return f"раньше {clock}" + (f" (больше чем {ago})" if m >= 1 else "")
    return f"~{clock} ({ago})"


def is_active(task_id):
    return bool(db.execute("select 1 from tasks where id=? and active=1", (task_id,)).fetchone())


def split_query(q):
    words = q.split()
    return (" ".join(w for w in words if not w.startswith("-")),
            [w[1:].lower() for w in words if w.startswith("-") and len(w) > 1])


def query_label(q):
    return q or "все объявления"


_chat_locks: dict[int, asyncio.Lock] = {}


async def check(bot, t):
    search, minus = split_query(t["query"])
    items, partial = await SITES[t["site"]]({**dict(t), "query": search})
    items = list({str(i["id"]): i for i in items}.values())  # одно объявление может прийти дважды
    if t["site"] in ("depop", "vinted", "poshmark", "wallapop") and items and not any(i.get("seller_id") for i in items) \
            and (t["min_reviews"] or t["min_account_days"] or t["contacts_only"]):
        raise RuntimeError(f"{t['site']} не отдаёт продавца в поиске — фильтры продавца не работают")
    if partial:
        last_error[t["id"]] = f"часть не парсится — {partial}"
    else:
        last_error.pop(t["id"], None)
    now = time.time()

    for market in {i["market"] for i in items if "ts" not in i}:
        try:
            max_id = max(int(i["id"]) for i in items if i["market"] == market)
            record_mark(market, max_id, now)
        except ValueError:
            pass
    estimate_ts(items, now)
    hidden = {r[0] for r in db.execute("select seller from hidden where chat_id=? and site=?", (t["chat_id"], t["site"]))}

    fresh = []
    for i in items:
        item_id = str(i["id"])
        exists = db.execute("select 1 from seen where task_id=? and item_id=?", (t["id"], item_id)).fetchone()
        if not exists:
            fresh.append(i)
    # свежие первыми: упёрлись в лимит карточек — пропускаем самые старые, а не копим очередь с отставанием
    fresh.sort(key=lambda i: i["ts"], reverse=True)
    limit = chat_limit(t["chat_id"])

    # страна/рынок, впервые ответившие после прогрева (добавили прокси, сайт ожил после долгого простоя):
    # их выдачу молча помечаем увиденной, иначе вся она придёт как новая
    known = {r[0] for r in db.execute("select item_id from seen where task_id=? and item_id like 'src:%'", (t["id"],))}
    fresh_ids = {str(i["id"]) for i in fresh}
    new_src = {i["src"] for i in items if f"src:{i['src']}" not in known} \
        - {i["src"] for i in items if str(i["id"]) not in fresh_ids}

    out, retry, profile_err = [], [], None
    if t["primed"]:
        for n, i in enumerate(fresh):
            if i["src"] in new_src or str(i.get("seller_id")) in hidden or \
                    any(w in f"{i.get('title', '')} {i.get('brand', '')} {i.get('description') or ''}".lower()
                        for w in minus):
                continue
            try:
                should_show, processed_item = await should_show_item(i, t, t["site"])
            except SellerRetry as e:
                profile_err = str(e)
                retry.append(i)  # не помечаем увиденным — этот профиль попробуем в следующем цикле
                if "429" in profile_err or len(retry) >= 3:  # лимит запросов или профили не грузятся вообще
                    retry += fresh[n + 1:]
                    log.info("task #%s: %s, отложено объявлений: %s", t["id"], e, len(retry))
                    break
                continue  # один битый профиль не держит остальную выдачу
            if should_show and processed_item:
                out.append(processed_item)
            if len(out) >= limit:
                if len(fresh) > n + 1:
                    log.info("task #%s: лимит %s карточек — старых пропущено: %s", t["id"], limit, len(fresh) - n - 1)
                break
    if profile_err and not out and "429" not in profile_err:  # без этого задача молча ничего не присылает
        last_error.setdefault(t["id"], profile_err)

    current = db.execute("select * from tasks where id=?", (t["id"],)).fetchone()
    if not current or tuple(current) != tuple(t):
        return

    # показанные помечаем увиденными только после отправки: упал Telegram — пришлём в следующем цикле.
    # ts обновляем у всего, что есть в выдаче: чистка seen удаляет только выпавшее из выдачи
    pending = {str(i["id"]) for i in retry + out}
    db.executemany("insert or replace into seen values(?,?,?)",
                   [(t["id"], str(i["id"]), now) for i in items if str(i["id"]) not in pending])
    db.executemany("insert or replace into seen values(?,?,?)", [(t["id"], f"src:{s}", now) for s in {i["src"] for i in items}])
    db.execute("update tasks set primed=1 where id=?", (t["id"],))
    db.commit()

    async with _chat_locks.setdefault(t["chat_id"], asyncio.Lock()):
        for i in sorted(out, key=lambda x: x["ts"]):  # внутри пачки — от старых к новым: лента читается сверху вниз
            if not is_active(t["id"]):
                return
            # то же объявление могла поймать другая задача этого чата — второй раз не шлём
            key = f"{t['site']}:{i['id']}"
            new = not db.execute("select 1 from sent where chat_id=? and item=?", (t["chat_id"], key)).fetchone()
            if new:
                await send(bot, t, i)
                db.execute("insert or replace into sent values(?,?,?,?)", (t["chat_id"], key, time.time(), t["id"]))
            db.execute("insert or replace into seen values(?,?,?)", (t["id"], str(i["id"]), time.time()))
            db.commit()  # до паузы: прибили процесс в эту секунду — после рестарта не будет дубля
            if new:
                await asyncio.sleep(1)


async def calibrate():
    tasks = db.execute("select * from tasks where active=1").fetchall()
    markets = {}  # рынок → чей прокси взять для калибровки; задачи админа первыми — чтобы не тратить трафик друзей
    for t in sorted(tasks, key=lambda t: t["chat_id"] != ADMIN):
        if t["site"] == "vinted":
            for market in vinted_markets(t):
                markets.setdefault(market, t["chat_id"])
        elif t["site"] == "depop":
            markets.setdefault("depop", t["chat_id"])

    for market, chat in markets.items():
        token = current_chat.set(chat)
        try:
            if market == "depop":
                d = await depop_mobile_search({
                    "limit": 24, "country": "gb", "currency": "GBP",
                    "ranking": "recent", "from": "in_country_search",
                })
                top = max((int(o["id"]) for o in d.get("objects", [])), default=0)
            else:
                d = await vinted_mobile_call(market, "/svc-catalogue/items", {"order": "newest_first", "per_page": 20})
                top = max((i["id"] for i in d.get("items", [])), default=0)
            record_mark(market, top, time.time())
        except Exception as ex:
            log.info("calibrate %s: %s", market, ex)
        finally:
            current_chat.reset(token)


async def run(bot, t):
    current_chat.set(t["chat_id"])  # все запросы задачи идут через прокси её владельца (у gather у каждой run свой контекст)
    try:
        await check(bot, t)
    except Exception as ex:
        if isinstance(ex, TelegramForbiddenError) or (isinstance(ex, TelegramBadRequest) and "chat not found" in str(ex)):
            # бота заблокировали или удалили из чата — слать некуда: ставим все задачи этого чата на паузу
            n = db.execute("update tasks set active=0 where chat_id=? and active=1", (t["chat_id"],)).rowcount
            db.commit()
            log.warning("чат %s недоступен (%s) — задач на паузе: %s", t["chat_id"], ex, n)
            return
        last_error[t["id"]] = str(ex)[:300]
        log.warning("task #%s %s %r: %s", t["id"], t["site"], t["query"], ex)

    # пишем в чат только при смене состояния (сломалась / часть стран / починилась), а не каждый цикл
    err = last_error.get(t["id"])
    state = None if err is None else "partial" if err.startswith("часть не парсится") else "fail"
    prev, n = streak.get(t["id"], (None, 0))
    n = n + 1 if state == prev else 1
    streak[t["id"]] = (state, n)
    if state == alerted.get(t["id"]) or (state is not None and n < ALERT_AFTER):
        return
    head = f"Задача #{t['id']} {t['site'].upper()} «{html.escape(query_label(t['query']))}»"
    if state is None:
        text = f"✅ {head} снова работает"
        alerted.pop(t["id"], None)
    else:
        hint = "\n\nСайт блокирует IP — нужен прокси: /proxy (или PROXIES в .env)." if "HTTP 403" in err else ""
        what = "часть стран не парсится" if state == "partial" else "не парсится"
        text = f"⚠️ {head}: {what}\n<code>{html.escape(err.removeprefix('часть не парсится — '))}</code>{hint}"
        alerted[t["id"]] = state
    try:
        await bot.send_message(t["chat_id"], text)
    except Exception as ex2:
        log.warning("alert #%s: %s", t["id"], ex2)


def prune_seen():
    # Отсчёт от последней проверки задачи, а не от «сейчас»: на паузе или при падении сайта ничего не теряем
    for tid, last in db.execute("select task_id, max(ts) from seen group by task_id").fetchall():
        db.execute("delete from seen where task_id=? and ts<?", (tid, last - SEEN_TTL))
    db.execute("delete from sent where ts<?", (time.time() - 7 * 86400,))
    db.commit()


async def poll(bot):
    while True:
        try:
            await calibrate()
            await asyncio.gather(*(run(bot, t) for t in db.execute("select * from tasks where active=1").fetchall()))
            prune_seen()
        except Exception:  # любой сбой цикла не должен молча остановить парсинг, пока бот продолжает отвечать
            log.exception("цикл проверки упал — продолжаю со следующего")
        await asyncio.sleep(INTERVAL)

# ---------- Telegram UI ----------

dp = Dispatcher()
if ALLOWED:
    dp.message.filter(F.from_user.id.in_(ALLOWED))
    dp.callback_query.filter(F.from_user.id.in_(ALLOWED))

BTN_NEW, BTN_LIST, BTN_STOP, BTN_GO = "🔍 Новый поиск", "📋 Мои задачи", "⏹️ Стоп", "▶️ Запустить все"
MENU = ReplyKeyboardMarkup(
    keyboard=[[KeyboardButton(text=BTN_NEW), KeyboardButton(text=BTN_LIST)],
              [KeyboardButton(text=BTN_STOP), KeyboardButton(text=BTN_GO)]],
    resize_keyboard=True, is_persistent=True,
)
AGES = {0: "Любой", 15: "15 мин", 30: "30 мин", 60: "1 час", 360: "6 часов", 1440: "1 день"}


class New(StatesGroup):
    countries = State()
    query = State()
    price = State()
    age = State()
    seller_filters = State()


def kb(rows):
    return InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text=txt, callback_data=data) for txt, data in row] for row in rows]
    )


def parse_price(s):
    s = s.lower().replace(",", ".").replace(" ", "")
    num = r"(\d+(?:\.\d+)?)"
    if m := re.fullmatch(num + "-" + num, s):
        lo, hi = float(m[1]), float(m[2])
        if lo > hi:
            raise ValueError
        return lo, hi
    if m := re.fullmatch("(?:до)?" + num, s):
        return None, float(m[1])
    if m := re.fullmatch("от" + num, s):
        return float(m[1]), None
    raise ValueError


def countries_text(site, country):
    codes = country.split(",") if country else []
    if not codes or len(codes) == len(COUNTRIES[site]):
        return "🌍 все страны"
    return " ".join(map(flag, codes))


def price_text(lo, hi):
    return f"{lo:g}–{hi:g}" if lo and hi else f"до {hi:g}" if hi else f"от {lo:g}" if lo else ""


def task_row(t):
    e = html.escape
    price = f" 💰{price_text(t['pmin'], t['pmax'])}" if t["pmin"] or t["pmax"] else ""
    err = f"\n   ⚠️ {e(last_error[t['id']][:100])}" if t["id"] in last_error else ""
    age = f" ≤{AGES.get(t['max_age'], str(t['max_age']) + ' мин')}" if t["max_age"] else ""
    reviews = f" ⭐️{t['min_reviews']}+" if t["min_reviews"] else ""
    acc_age = f" 📅{t['min_account_days']}д+" if t["min_account_days"] else ""
    contacts = " 📧" if t["contacts_only"] else ""
    private = " 🙋частные" if t["private_only"] else ""
    return (f"{'▶️' if t['active'] else '⏸️'} #{t['id']} {t['site'].upper()} «{e(query_label(t['query']))}»"
            f"{price}{age}{reviews}{acc_age}{contacts}{private}"
            f"\n   {countries_text(t['site'], t['country'])}{err}")


TASKS_PAGE = 10  # задач на страницу списка: лимиты Telegram — 4096 символов и 100 кнопок на сообщение


def task_kb(rows, page, pages):
    nav = ([("◀️", f"list:{page - 1}")] if page > 0 else []) + [("🔄 Обновить", f"list:{page}")] + \
          ([("▶️", f"list:{page + 1}")] if page < pages - 1 else [])
    return kb([[(f"{'⏸️' if t['active'] else '▶️'} #{t['id']}", f"toggle:{t['id']}:{page}"),
                (f"✏️ #{t['id']}", f"edit:{t['id']}"),
                (f"🗑 #{t['id']}", f"del:{t['id']}:{page}")] for t in rows] + [nav])


def countries_kb(site, chosen):
    codes = COUNTRIES[site]
    btns = [(("✅ " if cc in chosen else "") + flag(cc) + " " + cc.upper(), "cc:" + cc) for cc in codes]
    rows = [btns[i:i + 3] for i in range(0, len(btns), 3)]
    rows.append([("✖️ Снять все" if len(chosen) == len(codes) else "🌍 Выбрать все", "cc:all"),
                 ("Далее ➡️", "cc:done")])
    return kb(rows + [BACK_ROW])


def countries_prompt(d):
    site = d["site"]
    text = (f"✏️ Правка #{d['edit']} <b>{site.upper()}</b> — страны:" if "edit" in d
            else f"<b>{site.upper()}</b> — выбери страны (можно несколько):")
    return text, countries_kb(site, d["countries"])


def sites_kb():
    sites = [(f"🛍 {s.upper()}", f"site:{s}") for s in SITES]
    return kb([sites[i:i + 3] for i in range(0, len(sites), 3)])


@dp.message(Command("start", "help"))
async def cmd_start(m: Message, state: FSMContext):
    await state.clear()
    await m.answer(
        f"<b>Парсер новых объявлений</b>\nПлощадки: {', '.join(s.upper() for s in SITES)}\n"
        f"Проверка каждые {INTERVAL} сек.\n\n"
        f"Фильтры продавца:\n"
        f"• Мин. отзывы у продавца\n"
        f"• Мин. возраст аккаунта (дней)\n"
        f"• Только объявления с email/телефоном\n"
        f"• Только частные продавцы (без профи и магазинов)\n\n"
        f"Скрытые продавцы — /hidden · свои прокси — /proxy · статистика — /stats · лимит карточек — /limit\n"
        f"Твой id: <code>{m.from_user.id}</code>",
        reply_markup=MENU,
    )


@dp.message(F.text == BTN_NEW)
async def new_search(m: Message, state: FSMContext):
    await state.clear()
    await m.answer("Выбери площадку:", reply_markup=sites_kb())


@dp.message(F.text == BTN_LIST)
async def my_tasks(m: Message, state: FSMContext):
    await state.clear()
    text, markup = render_list(m.chat.id)
    await m.answer(text, reply_markup=markup)


def render_list(chat_id, page=0):
    rows = db.execute("select * from tasks where chat_id=? order by id", (chat_id,)).fetchall()
    if not rows:
        return f"Задач нет. Нажми «{BTN_NEW}».", None
    pages = -(-len(rows) // TASKS_PAGE)
    page = min(max(page, 0), pages - 1)
    chunk = rows[page * TASKS_PAGE:(page + 1) * TASKS_PAGE]
    text = "\n".join(map(task_row, chunk))
    if pages > 1:
        text += f"\n\nСтраница {page + 1} из {pages} · задач: {len(rows)}"
    return text, task_kb(chunk, page, pages)


def render_hidden(chat_id):
    rows = db.execute("select site, seller, name from hidden where chat_id=? order by rowid desc limit 50",
                      (chat_id,)).fetchall()
    if not rows:
        return "Скрытых продавцов нет. Скрыть — кнопкой «🚫 Скрыть продавца» под карточкой.", None
    return "🚫 Скрытые продавцы — нажми, чтобы вернуть:", \
        kb([[(f"↩️ {r['site'].upper()} · {r['name'] or r['seller']}"[:60], f"unh:{r['site']}:{r['seller']}")]
            for r in rows])


@dp.message(Command("hidden"))
async def cmd_hidden(m: Message, state: FSMContext):
    await state.clear()
    text, markup = render_hidden(m.chat.id)
    await m.answer(text, reply_markup=markup)


@dp.callback_query(F.data.regexp(r"^unh:[a-z]+:[\w-]+$"))
async def unhide_from_list(c: CallbackQuery):
    _, site, seller = c.data.split(":", 2)
    db.execute("delete from hidden where chat_id=? and site=? and seller=?", (c.message.chat.id, site, seller))
    db.commit()
    text, markup = render_hidden(c.message.chat.id)
    await c.message.edit_text(text, reply_markup=markup)
    await c.answer("Продавец снова показывается")


def render_stats(chat_id):
    day_start = datetime.datetime.now(TZ).replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
    counts = {r[0]: (r[1], r[2]) for r in db.execute(
        "select task_id, sum(ts >= ?), count(*) from sent where chat_id=? and ts >= ? group by task_id",
        (day_start, chat_id, time.time() - 7 * 86400))}
    lines = ["📊 <b>Прислано карточек</b> (сегодня · за 7 дней)", ""]
    for t in db.execute("select * from tasks where chat_id=? order by id", (chat_id,)):
        today, week = counts.pop(t["id"], (0, 0))
        lines.append(f"{'▶️' if t['active'] else '⏸️'} #{t['id']} {t['site'].upper()} «{html.escape(query_label(t['query']))}»: "
                     f"<b>{today}</b> · {week}")
    if counts:  # задачи уже удалены (и записи до появления статистики)
        lines.append(f"🗑 удалённые задачи: {sum(v[0] for v in counts.values())} · {sum(v[1] for v in counts.values())}")
    total = db.execute("select sum(ts >= ?), count(*) from sent where chat_id=? and ts >= ?",
                       (day_start, chat_id, time.time() - 7 * 86400)).fetchone()
    lines.append(f"\nВсего: <b>{total[0] or 0}</b> · {total[1]}")
    text = "\n".join(lines)
    if len(text) >= 4000:  # режем целыми строками: разрезанный посреди <b> текст Telegram не примет
        text = text[:3990].rsplit("\n", 1)[0] + "\n…"
    return text


@dp.message(Command("stats"))
async def cmd_stats(m: Message, state: FSMContext):
    await state.clear()
    await m.answer(render_stats(m.chat.id))


def chat_limit(chat_id):
    row = db.execute("select max_per_cycle from settings where chat_id=?", (chat_id,)).fetchone()
    return row[0] if row else MAX_PER_CYCLE


def render_limit(chat_id):
    cur = chat_limit(chat_id)
    return (f"📦 <b>Лимит карточек</b>: сейчас <b>{cur}</b> за проверку (~{INTERVAL} с) на каждую задачу.\n"
            "Новых больше лимита — присылаю самые свежие, старые пропускаю: без очереди и отставания.\n"
            "Большой лимит — больше трафика прокси на профили продавцов и риск флуд-лимита Telegram."), \
        kb([[(f"✅ {n}" if n == cur else str(n), f"limit:{n}") for n in LIMITS]])


@dp.message(Command("limit"))
async def cmd_limit(m: Message, state: FSMContext):
    await state.clear()
    text, markup = render_limit(m.chat.id)
    await m.answer(text, reply_markup=markup)


@dp.callback_query(F.data.regexp(r"^limit:\d+$"))
async def set_limit(c: CallbackQuery):
    n = int(c.data[6:])
    if n not in LIMITS:
        return await c.answer()
    db.execute("insert or replace into settings values(?, ?)", (c.message.chat.id, n))
    db.commit()
    text, markup = render_limit(c.message.chat.id)
    await c.message.edit_text(text, reply_markup=markup)
    await c.answer(f"Лимит: {n}")


class ProxyForm(StatesGroup):
    url = State()


def geo_label(site, geo):
    if geo == "*":
        return "🌍 все страны"
    if site == "vinted":
        return {"eu": "🇪🇺 EU (vinted.de)", "es": "🇪🇸 ES (vinted.es)", "us": "🇺🇸 US (vinted.com)"}[geo]
    return f"{flag(geo)} {geo.upper()}"


def render_proxies(chat_id, admin):
    """Свои прокси пользователя и общие (chat_id=0): общими управляет только админ, остальным виден лишь список."""
    label = lambda r: f"{r['site'].upper()} {geo_label(r['site'], r['geo'])}"
    own = db.execute("select site, geo, url from proxies where chat_id=? order by site, geo", (chat_id,)).fetchall()
    shared = db.execute("select site, geo, url from proxies where chat_id=0 order by site, geo").fetchall()
    lines = ["🌐 <b>Твои прокси</b> — только для твоих задач, другим не видны",
             "Порядок выбора: твой прокси страны → твой «все страны» → общий так же → PROXIES из .env → без прокси.", ""]
    lines += [f"• {label(r)} — <code>{html.escape(mask_proxy(r['url']))}</code>" for r in own] or ["Своих прокси пока нет."]
    lines.append("\n🤝 <b>Общие</b> — для тех, у кого нет своего:")
    lines += [f"• {label(r)}" + (f" — <code>{html.escape(mask_proxy(r['url']))}</code>" if admin else "")
              for r in shared] or ["нет"]
    lines.append(f"Общий PROXIES из .env: {len(PROXY_LIST)} шт.")
    rows = [[("➕ Добавить / заменить свой", "pxadd")]] + ([[("➕ Общий прокси", "pxadd:s")]] if admin else [])
    rows += [[(f"🗑 {label(r)}"[:60], f"pxdel:{r['site']}:{r['geo']}")] for r in own]
    if admin:
        rows += [[(f"🗑 общий {label(r)}"[:60], f"pxdel:{r['site']}:{r['geo']}:s")] for r in shared]
    return "\n".join(lines), kb(rows)


def proxy_scope(c: CallbackQuery):
    """Хвост ':s' в кнопке — общий прокси. Чужой (не админ) — None: такие кнопки игнорируем."""
    shared = c.data.endswith(":s")
    return None if shared and c.from_user.id != ADMIN else (":s" if shared else "")


@dp.message(Command("proxy"))
async def cmd_proxy(m: Message, state: FSMContext):
    await state.clear()
    text, markup = render_proxies(m.chat.id, m.from_user.id == ADMIN)
    await m.answer(text, reply_markup=markup)


@dp.callback_query(F.data == "pxlist")
async def proxy_list(c: CallbackQuery, state: FSMContext):
    await state.clear()
    text, markup = render_proxies(c.message.chat.id, c.from_user.id == ADMIN)
    await c.message.edit_text(text, reply_markup=markup)
    await c.answer()


@dp.callback_query(F.data.regexp(r"^pxadd(:s)?$"))
async def proxy_pick_site(c: CallbackQuery, state: FSMContext):
    if (s := proxy_scope(c)) is None:
        return await c.answer()
    await state.clear()
    sites = [(f"🛍 {site.upper()}", f"pxsite:{site}{s}") for site in SITES]
    await c.message.edit_text(f"Для какой площадки {'общий ' if s else ''}прокси?",
                              reply_markup=kb([sites[i:i + 3] for i in range(0, len(sites), 3)] + [[("⬅️ Назад", "pxlist")]]))
    await c.answer()


@dp.callback_query(F.data.regexp(r"^pxsite:[a-z]+(:s)?$"))
async def proxy_pick_geo(c: CallbackQuery, state: FSMContext):
    site = c.data.split(":")[1]
    if site not in SITES or (s := proxy_scope(c)) is None:
        return await c.answer()
    await state.clear()
    geos = [(geo_label(site, g), f"pxgeo:{site}:{g}{s}") for g in PROXY_GEOS[site]]
    await c.message.edit_text(
        f"<b>{site.upper()}</b> — для какой страны? «Все страны» сработает там, где нет прокси конкретной страны.",
        reply_markup=kb([[("🌍 Все страны площадки", f"pxgeo:{site}:*{s}")]] + [geos[i:i + 3] for i in range(0, len(geos), 3)]
                        + [[("⬅️ Назад", f"pxadd{s}")]]))
    await c.answer()


@dp.callback_query(F.data.regexp(r"^pxgeo:[a-z]+:([a-z]{2}|\*)(:s)?$"))
async def proxy_ask_url(c: CallbackQuery, state: FSMContext):
    _, site, geo, *_ = c.data.split(":")
    if (s := proxy_scope(c)) is None:
        return await c.answer()
    await state.set_state(ProxyForm.url)
    await state.set_data({"site": site, "geo": geo, "owner": 0 if s else c.message.chat.id})
    await c.message.edit_text(
        f"{'🤝 Общий: ' if s else ''}<b>{site.upper()}</b> {geo_label(site, geo)}\n\nПришли прокси одной строкой:\n"
        "<code>http://user:pass@host:port</code> или <code>socks5://user:pass@host:port</code>\n\n"
        "Проверю его перед сохранением, а сообщение с паролем удалю из чата.",
        reply_markup=kb([[("⬅️ Назад", f"pxsite:{site}{s}")]]))
    await c.answer()


@dp.message(Command("stop"))
@dp.message(F.text == BTN_STOP)
async def stop_all(m: Message, state: FSMContext):
    await state.clear()
    n = db.execute("update tasks set active=0 where chat_id=? and active=1", (m.chat.id,)).rowcount
    db.commit()
    await m.answer(f"⏹️ Остановлено задач: {n}. Запустить снова — «{BTN_GO}» или /go.", reply_markup=MENU)


@dp.message(Command("go"))
@dp.message(F.text == BTN_GO)
async def go_all(m: Message, state: FSMContext):
    await state.clear()
    n = db.execute("update tasks set active=1 where chat_id=? and active=0", (m.chat.id,)).rowcount
    db.commit()
    await m.answer(f"▶️ Запущено задач: {n}." if n else "Остановленных задач нет.", reply_markup=MENU)


@dp.message(ProxyForm.url, F.text)
async def proxy_got_url(m: Message, state: FSMContext):
    url = m.text.strip()
    try:
        await m.delete()  # в сообщении логин и пароль прокси — не храним в истории чата
    except Exception:
        pass
    parts = urlsplit(url)
    try:
        port = parts.port
    except ValueError:
        port = None
    if parts.scheme not in ("http", "https", "socks5", "socks5h") or not parts.hostname or not port:
        return await m.answer("Не похоже на прокси. Формат: <code>http://user:pass@host:port</code> "
                              "или <code>socks5://host:port</code>. Пришли ещё раз или /proxy — отмена.")
    d = await state.get_data()
    try:
        async with AsyncSession(impersonate="chrome", proxy=url, timeout=15) as s:
            info = (await s.get("https://ipinfo.io/json")).json()
    except Exception as e:
        return await m.answer(f"❌ Прокси не отвечает: <code>{html.escape(str(e)[:200])}</code>\n"
                              "Пришли другой или /proxy — отмена.")
    await state.clear()
    db.execute("insert or replace into proxies(chat_id, site, geo, url) values(?,?,?,?)",
               (d["owner"], d["site"], d["geo"], url))
    db.commit()
    await reset_sessions()
    cc = (info.get("country") or "").lower()
    text = (f"✅ Сохранил{' общий' if d['owner'] == 0 else ''}: {d['site'].upper()} {geo_label(d['site'], d['geo'])} — "
            f"<code>{html.escape(mask_proxy(url))}</code>\nIP прокси: <code>{html.escape(str(info.get('ip', '?')))}</code> "
            f"{flag(cc)} {cc.upper()}")
    if d["geo"] not in ("*", "eu") and cc and cc != d["geo"]:
        text += (f"\n⚠️ IP из {cc.upper()}, а выбрана страна {d['geo'].upper()} — площадка может показывать "
                 "каталог не той страны или не пускать.")
    await m.answer(text)
    text, markup = render_proxies(m.chat.id, m.from_user.id == ADMIN)
    await m.answer(text, reply_markup=markup)


@dp.callback_query(F.data.regexp(r"^pxdel:[a-z]+:([a-z]{2}|\*)(:s)?$"))
async def proxy_delete(c: CallbackQuery, state: FSMContext):
    _, site, geo, *_ = c.data.split(":")
    if (s := proxy_scope(c)) is None:
        return await c.answer()
    db.execute("delete from proxies where chat_id=? and site=? and geo=?", (0 if s else c.message.chat.id, site, geo))
    db.commit()
    await reset_sessions()
    text, markup = render_proxies(c.message.chat.id, c.from_user.id == ADMIN)
    await c.message.edit_text(text, reply_markup=markup)
    await c.answer("Прокси удалён")


@dp.callback_query(F.data.startswith("site:"))
async def pick_site(c: CallbackQuery, state: FSMContext):
    site = c.data[5:]
    if site not in SITES:
        return await c.answer()
    await state.set_data({"site": site, "countries": []})
    await state.set_state(New.countries)
    text, markup = countries_prompt(await state.get_data())
    await c.message.edit_text(text, reply_markup=markup)
    await c.answer()


@dp.callback_query(F.data.startswith("cc:"))
async def pick_country(c: CallbackQuery, state: FSMContext):
    d = await state.get_data()
    if "site" not in d:
        return await c.answer(f"Начни заново: «{BTN_NEW}»", show_alert=True)
    site, chosen, cc = d["site"], d["countries"], c.data[3:]
    codes = COUNTRIES[site]
    if cc == "done":
        if not chosen:
            return await c.answer("Выбери хотя бы одну страну", show_alert=True)
        await state.set_state(New.query)
        text, markup = query_prompt({**d, "countries": chosen})
        await c.message.edit_text(text, reply_markup=markup)
        return await c.answer()
    if cc == "all":
        chosen = [] if len(chosen) == len(codes) else list(codes)
    elif cc in codes:
        chosen = [x for x in chosen if x != cc] if cc in chosen else chosen + [cc]
    await state.update_data(countries=chosen)
    await c.message.edit_reply_markup(reply_markup=countries_kb(site, chosen))
    await c.answer()


@dp.message(New.query, F.text)
async def got_query(m: Message, state: FSMContext):
    query = m.text.strip()
    if len(query) > 100:
        return await m.answer("Слишком длинный запрос, до 100 символов.")
    if query.lower() in ("all", "все", "*"):
        query = ""
    await state.update_data(query=query)
    await state.set_state(New.price)
    text, markup = price_prompt(await state.get_data())
    await m.answer(text, reply_markup=markup)


@dp.callback_query(New.query, F.data == "query:all")
async def query_all(c: CallbackQuery, state: FSMContext):
    await state.update_data(query="")
    await state.set_state(New.price)
    await c.message.edit_reply_markup(reply_markup=None)
    text, markup = price_prompt(await state.get_data())
    await c.message.answer(text, reply_markup=markup)
    await c.answer()


@dp.message(New.price, F.text)
async def got_price(m: Message, state: FSMContext):
    try:
        pmin, pmax = parse_price(m.text)
    except ValueError:
        return await m.answer("Не понял цену. Примеры: <code>10-50</code>, <code>до 50</code>, <code>от 10</code>")
    await state.update_data(pmin=pmin, pmax=pmax)
    await state.set_state(New.age)
    text, markup = age_prompt(await state.get_data())
    await m.answer(text, reply_markup=markup)


@dp.callback_query(New.price, F.data == "price:any")
async def any_price(c: CallbackQuery, state: FSMContext):
    await state.update_data(pmin=None, pmax=None)
    await c.message.edit_reply_markup(reply_markup=None)
    await state.set_state(New.age)
    text, markup = age_prompt(await state.get_data())
    await c.message.answer(text, reply_markup=markup)
    await c.answer()


SELLER_NOTES = {
    "poshmark": "Poshmark: вместо отзывов считаются продажи; тип продавца не отдаёт — «частные» недоступно.",
    "depop": "Depop: тип продавца не отдаёт — «частные» недоступно.",
    "milanuncios": "Milanuncios: отзывы и возраст аккаунта не отдаёт — работают только контакты и «частные».",
    "olx": "OLX: отзывы не отдаёт — работают возраст аккаунта, контакты и «частные».",
}
# какие фильтры продавца площадка не поддерживает: (отзывы, дни, частные)
NO_FILTER = {"milanuncios": (True, True, False), "olx": (True, False, False),
             "poshmark": (False, False, True), "depop": (False, False, True)}
SELLER_KEYS = ("min_reviews", "min_account_days", "contacts_only", "private_only")


BACK_ROW = [("⬅️ Назад", "back")]


def keep_row(d, label, step):
    """При правке задачи — кнопка «оставить как было» с текущим значением."""
    return [[(f"↩️ Оставить: {label}"[:60], f"keep:{step}")]] if "old" in d else []


def query_prompt(d):
    site = d["site"]
    return (f"<b>{site.upper()}</b> · {countries_text(site, ','.join(d['countries']))}\n\n"
            "✏️ Напиши, что искать (например: <code>nike dunk low</code>)\n"
            "Исключить слова — через минус: <code>nike dunk -kids -replica</code>\n"
            "Все новые объявления подряд — кнопка ниже или <code>all</code> (можно с минусами: <code>-kids</code>)"), \
        kb([[("📋 Все объявления", "query:all")]]
           + keep_row(d, query_label((d.get("old") or {}).get("query")), "query") + [BACK_ROW])


def currencies(site, countries):
    if site == "vinted":
        return sorted({"USD" if c == "us" else "EUR" for c in countries})
    table = {"depop": DEPOP_CURRENCY, "poshmark": {"us": "USD", "ca": "CAD"}, "olx": OLX_CURRENCY}.get(site)
    return sorted({table[c] for c in countries}) if table else ["EUR"]  # Wallapop, Milanuncios


def price_prompt(d):
    old = d.get("old") or {}
    cur = currencies(d["site"], d["countries"])
    note = (f"Валюта: <b>{cur[0]}</b>" if len(cur) == 1 else
            f"Валюты: <b>{', '.join(cur)}</b> — число применяется как есть в валюте каждой страны, без пересчёта")
    return (f"💰 Цена: напиши <code>10-50</code>, <code>до 50</code> или <code>от 10</code>\n<i>{note}</i>",
            kb([[("Любая цена", "price:any")]] + keep_row(d, price_text(old.get("pmin"), old.get("pmax")) or "любая", "price")
               + [BACK_ROW]))


def age_prompt(d):
    ages = list(AGES.items())
    old_age = (d.get("old") or {}).get("max_age") or 0
    return ("🕒 Насколько свежие объявления присылать?",
            kb([[(txt, f"age:{v}") for v, txt in ages[i:i + 3]] for i in (0, 3)]
               + keep_row(d, AGES.get(old_age, f"{old_age} мин"), "age") + [BACK_ROW]))


def seller_prompt(d):
    note = SELLER_NOTES.get(d["site"], "")
    cur = " ".join(str((d.get("old") or {}).get(k, 0)) for k in SELLER_KEYS)
    return ("👤 Фильтры продавца:\n\n"
            "Напиши через пробел:\n"
            "<code>мин_отзывов мин_дней_акка контакты частные</code>\n"
            "(последнее число можно не писать)\n\n"
            "Примеры:\n"
            "• <code>5 30 0</code> — от 5 отзывов, аккаунт 30+ дней, любые объявления\n"
            "• <code>0 0 1</code> — только с email/телефоном в профиле или описании\n"
            "• <code>0 0 0 1</code> — только частные продавцы, без профи и магазинов\n"
            "• <code>10 0 1 1</code> — от 10 отзывов, есть контакты, частный продавец"
            + (f"\n\n<i>{note}</i>" if note else ""),
            kb([[("Пропустить (0 0 0 0)", "seller:skip")]] + keep_row(d, cur, "seller_filters") + [BACK_ROW]))


# шаг мастера → предыдущий шаг и его вопрос
BACK = {
    New.query.state: (New.countries, countries_prompt),
    New.price.state: (New.query, query_prompt),
    New.age.state: (New.price, price_prompt),
    New.seller_filters.state: (New.age, age_prompt),
}


@dp.callback_query(F.data == "back")
async def go_back(c: CallbackQuery, state: FSMContext):
    st, d = await state.get_state(), await state.get_data()
    if st == New.countries.state:  # первый шаг: новая задача — к выбору площадки, правка — к списку задач
        await state.clear()
        text, markup = render_list(c.message.chat.id) if "edit" in d else ("Выбери площадку:", sites_kb())
    elif st in BACK:
        prev, prompt = BACK[st]
        await state.set_state(prev)
        text, markup = prompt(d)
    else:
        return await c.answer(f"Начни заново: «{BTN_NEW}»", show_alert=True)
    await c.message.edit_text(text, reply_markup=markup)
    await c.answer()


@dp.callback_query(New.age, F.data.regexp(r"^age:\d+$"))
async def got_age(c: CallbackQuery, state: FSMContext):
    age = int(c.data[4:])
    if age not in AGES:
        return await c.answer()
    await state.update_data(max_age=age or None)
    await state.set_state(New.seller_filters)
    text, markup = seller_prompt(await state.get_data())
    await c.message.edit_text(text, reply_markup=markup)
    await c.answer()


@dp.callback_query(New.seller_filters, F.data == "seller:skip")
async def skip_seller_filters(c: CallbackQuery, state: FSMContext):
    await state.update_data(min_reviews=0, min_account_days=0, contacts_only=0, private_only=0)
    await finish_task(c, state)


@dp.message(New.seller_filters, F.text)
async def got_seller_filters(m: Message, state: FSMContext):
    parts = m.text.strip().split()
    if len(parts) not in (3, 4):
        return await m.answer("Нужно 3 или 4 числа через пробел: отзывы дни контакты(0/1) частные(0/1)")
    try:
        reviews, days, contacts, private = (int(p) for p in parts + ["0"] * (4 - len(parts)))
        if contacts not in (0, 1) or private not in (0, 1) or not 0 <= reviews <= 10**6 or not 0 <= days <= 10**5:
            raise ValueError
    except ValueError:
        return await m.answer("Неверный формат. Примеры: <code>5 30 1</code> или <code>0 0 0 1</code>")
    site = (await state.get_data()).get("site")
    no_reviews, no_days, no_private = NO_FILTER.get(site, (False, False, False))
    if (no_reviews and reviews) or (no_days and days) or (no_private and private):
        return await m.answer(f"{SELLER_NOTES[site]}\nВведи фильтры заново.")
    await state.update_data(min_reviews=reviews, min_account_days=days, contacts_only=contacts, private_only=private)
    await finish_task(m, state)


# шаг мастера → какие поля оставить как в задаче, следующий шаг и его вопрос (None — шаг последний)
KEEP = {
    New.query.state: (("query",), New.price, price_prompt),
    New.price.state: (("pmin", "pmax"), New.age, age_prompt),
    New.age.state: (("max_age",), New.seller_filters, seller_prompt),
    New.seller_filters.state: (SELLER_KEYS, None, None),
}


@dp.callback_query(F.data.startswith("keep:"))
async def keep_value(c: CallbackQuery, state: FSMContext):
    d = await state.get_data()
    st = await state.get_state()
    step = KEEP.get(st)
    if not step or "old" not in d or st != f"New:{c.data[5:]}":  # кнопка из старого сообщения — от другого шага
        return await c.answer()
    keys, nxt, prompt = step
    await state.update_data({k: d["old"][k] for k in keys})
    await c.answer()
    if nxt is None:
        return await finish_task(c, state)
    await c.message.edit_reply_markup(reply_markup=None)
    await state.set_state(nxt)
    text, markup = prompt(await state.get_data())
    await c.message.answer(text, reply_markup=markup)



async def finish_task(msg_or_callback, state: FSMContext):
    d = await state.get_data()
    await state.clear()

    if isinstance(msg_or_callback, Message):
        chat_id = msg_or_callback.chat.id
    else:
        chat_id = msg_or_callback.message.chat.id

    vals = (
        ",".join(d["countries"]),
        d["query"],
        d["pmin"],
        d["pmax"],
        d.get("max_age"),
        d.get("min_reviews", 0),
        d.get("min_account_days", 0),
        d.get("contacts_only", 0),
        d.get("private_only", 0),
    )

    dup = db.execute(
        "select id from tasks where chat_id=? and site=? and country=? and query=? and pmin is ? and pmax is ? "
        "and max_age is ? and min_reviews=? and min_account_days=? and contacts_only=? and private_only=? and id!=?",
        (chat_id, d["site"], *vals, d.get("edit") or 0),
    ).fetchone()
    if dup:  # такая задача уже есть — запускаем её, чтобы не идти за ней в «Мои задачи»
        was_active = db.execute("select active from tasks where id=?", (dup["id"],)).fetchone()[0]
        db.execute("update tasks set active=1 where id=?", (dup["id"],))
        db.commit()
        t = db.execute("select * from tasks where id=?", (dup["id"],)).fetchone()
        head = "уже работает" if was_active else "была на паузе — запустил её"
        text = f"♻️ Такая задача уже есть: #{dup['id']} {head}" + \
               (", а правку не сохранил" if d.get("edit") else "") + f".\n\n{task_row(t)}"
        if isinstance(msg_or_callback, Message):
            return await msg_or_callback.answer(text)
        return await msg_or_callback.message.edit_text(text)

    if tid := d.get("edit"):
        if not db.execute(
            "update tasks set country=?, query=?, pmin=?, pmax=?, max_age=?, min_reviews=?, "
            "min_account_days=?, contacts_only=?, private_only=?, primed=0 where id=? and chat_id=?",
            (*vals, tid, chat_id),
        ).rowcount:
            if isinstance(msg_or_callback, Message):
                await msg_or_callback.answer("Задача уже удалена.")
            else:
                await msg_or_callback.message.edit_text("Задача уже удалена.")
            return
        last_error.pop(tid, None)
        alerted.pop(tid, None)
        streak.pop(tid, None)
        text = "✅ Задача обновлена"
    else:
        tid = db.execute(
            "insert into tasks(chat_id, site, country, query, pmin, pmax, max_age, min_reviews, "
            "min_account_days, contacts_only, private_only) values(?,?,?,?,?,?,?,?,?,?,?)",
            (chat_id, d["site"], *vals),
        ).lastrowid
        text = "✅ Задача запущена"

    db.commit()
    t = db.execute("select * from tasks where id=?", (tid,)).fetchone()
    answer_msg = f"{text}\n\n{task_row(t)}\n\nШлю только объявления, появившиеся после этого момента."
    if t["site"] in SLOW_FEED:
        lag, min_age = SLOW_FEED[t["site"]]
        answer_msg += (f"\n\n⏳ <b>{t['site'].upper()} отдаёт новые объявления с задержкой:</b> поиск площадки обновляется "
                       f"пачками, объявление попадает в него через {lag} после публикации. Первые минуты тишины — "
                       f"это нормально: бот работает и пришлёт всё, как только площадка выдаст.")
        if t["max_age"] and t["max_age"] < min_age:
            answer_msg += (f"\n⚠️ Свежесть «{AGES.get(t['max_age'])}» здесь будет отсекать часть объявлений — "
                           f"лучше {AGES.get(min_age)} или больше.")
    for note in proxy_notes(t["site"], (t["country"] or ",".join(COUNTRIES[t["site"]])).split(","), t["chat_id"]):
        answer_msg += "\n\n" + note
    if not split_query(t["query"])[0]:
        answer_msg += (f"\n\n📋 <b>Все объявления:</b> на крупных площадках это десятки в минуту, а за проверку я шлю "
                       f"{chat_limit(t['chat_id'])} самых свежих (лимит — /limit), остальные пропускаю. Фильтры продавца "
                       f"грузят профиль каждого объявления: больше трафика прокси и лимитов площадки.")
        if t["site"] == "milanuncios":
            answer_msg += ("\n⚠️ Milanuncios без запроса отдаёт почти одни «поднятые» старые объявления — новых будет "
                           "очень мало. Лучше задать слово.")

    if isinstance(msg_or_callback, Message):
        await msg_or_callback.answer(answer_msg)
    else:
        await msg_or_callback.message.edit_text(answer_msg)


@dp.callback_query(F.data.regexp(r"^(toggle|del):\d+(:\d+)?$"))  # без страницы — кнопки старых сообщений
async def on_task_button(c: CallbackQuery):
    action, tid, *page = c.data.split(":")
    chat_id = c.message.chat.id
    if action == "toggle":
        db.execute("update tasks set active=1-active where id=? and chat_id=?", (tid, chat_id))
    else:
        if db.execute("delete from tasks where id=? and chat_id=?", (tid, chat_id)).rowcount:
            db.execute("delete from seen where task_id=?", (tid,))
            # id без AUTOINCREMENT достанется следующей задаче — чужие статистика и алерты ей не нужны
            db.execute("update sent set task_id=null where task_id=?", (tid,))
            for state_by_task in (last_error, alerted, streak):
                state_by_task.pop(int(tid), None)
    db.commit()
    await show_list(c, int(page[0]) if page else 0)


@dp.callback_query(F.data.regexp(r"^(hide|unhide):[a-z]+:[\w-]+$"))
async def on_hide_seller(c: CallbackQuery):
    action, site, seller = c.data.split(":", 2)
    if action == "hide":
        # имя — из строки «👤 Продавец …» карточки, чтобы в /hidden было видно, кто это
        m = re.search(r"👤 Продавец(?:: (.+?) · (?:частный|профи)| @?(.+?)(?: · профи)?:)",
                      c.message.caption or c.message.text or "")
        name = (m.group(1) or m.group(2)) if m else None
        db.execute("insert or ignore into hidden values(?,?,?,?)", (c.message.chat.id, site, seller, name))
    else:
        db.execute("delete from hidden where chat_id=? and site=? and seller=?", (c.message.chat.id, site, seller))
    db.commit()
    await c.message.edit_reply_markup(reply_markup=seller_kb(site, seller, action == "hide"))
    await c.answer("Продавец скрыт: его объявления больше не придут в этот чат" if action == "hide"
                   else "Продавец снова показывается")


@dp.callback_query(F.data.regexp(r"^edit:\d+$"))
async def edit_task(c: CallbackQuery, state: FSMContext):
    t = db.execute(
        "select * from tasks where id=? and chat_id=?",
        (int(c.data[5:]), c.message.chat.id),
    ).fetchone()
    if t is None:
        return await c.answer("Задача уже удалена", show_alert=True)
    site = t["site"]
    chosen = t["country"].split(",") if t["country"] else list(COUNTRIES[site])
    await state.set_data({
        "site": site,
        "countries": chosen,
        "edit": t["id"],
        "old": {k: t[k] for k in ("query", "pmin", "pmax", "max_age", *SELLER_KEYS)},
    })
    await state.set_state(New.countries)
    text, markup = countries_prompt(await state.get_data())
    await c.message.answer(text, reply_markup=markup)
    await c.answer()


@dp.callback_query(F.data.regexp(r"^list(:\d+)?$"))
async def refresh_list(c: CallbackQuery):
    await show_list(c, int(c.data[5:] or 0))


async def show_list(c: CallbackQuery, page):
    text, markup = render_list(c.message.chat.id, page)
    try:
        await c.message.edit_text(text, reply_markup=markup)
    except TelegramBadRequest:
        pass
    await c.answer()


_instance_lock = socket.socket()  # держим открытым всё время работы: занятый порт = бот уже запущен


async def main():
    handlers = [RotatingFileHandler(ROOT / "parser.log", maxBytes=5_000_000, backupCount=3, encoding="utf-8")]
    if sys.stderr:  # под pythonw (автозапуск без окна) консоли нет — пишем только в файл
        handlers.append(logging.StreamHandler())
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s", handlers=handlers)
    try:
        _instance_lock.bind(("127.0.0.1", 47613))
    except OSError:
        log.error("Бот уже запущен (порт 47613 занят) — второй экземпляр не стартую, иначе Telegram выдаст Conflict")
        return
    if not ALLOWED:
        log.warning("ALLOWED_USERS пуст — бот отвечает ВСЕМ: любой может создать задачи, и они пойдут с твоего IP")
    bot = Bot(
        os.environ["BOT_TOKEN"],
        default=DefaultBotProperties(parse_mode="HTML", link_preview_is_disabled=True),
    )
    await bot.set_my_commands([
        BotCommand(command="start", description="Меню"),
        BotCommand(command="stop", description="Остановить все задачи"),
        BotCommand(command="go", description="Запустить все задачи"),
        BotCommand(command="hidden", description="Скрытые продавцы"),
        BotCommand(command="proxy", description="Свои прокси по площадкам"),
        BotCommand(command="stats", description="Статистика карточек"),
        BotCommand(command="limit", description="Лимит карточек за проверку"),
    ])
    poller = asyncio.create_task(poll(bot))
    try:
        await dp.start_polling(bot)
    finally:
        poller.cancel()


if __name__ == "__main__":
    asyncio.run(main())