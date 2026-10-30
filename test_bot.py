import sqlite3

import bot
from bot import extract_contacts, flag, parse_price, posted_at, split_query

assert parse_price("10-50") == (10, 50)
assert parse_price("до 50") == (None, 50) == parse_price("50")
assert parse_price("от 10,5") == (10.5, None)
for bad in ["", "abc", "50-10", "10-", "-5"]:
    try:
        parse_price(bad)
    except ValueError:
        continue
    raise AssertionError(bad)

assert flag("de") == "🇩🇪" and flag("gb") == "🇬🇧" and flag("") == "" and flag("x1") == ""

assert split_query("nike  dunk -Kids -replica") == ("nike dunk", ["kids", "replica"])
assert split_query("-kids") == ("", ["kids"]) and split_query("a - b") == ("a b", [])

c = extract_contacts("WA +49 151 2345-6789, +7 (999) 123-45-67, a.b@x.de; IBAN DE89370400440532013000, sku 12345678901234, "
                     "tel 0612345678, +10 скидка, A.B@x.de")
assert c == {"emails": ["a.b@x.de", "A.B@x.de"], "phones": ["+4915123456789", "+79991234567"]}, c
assert extract_contacts("") == extract_contacts(None) == {"emails": [], "phones": []}

# местные форматы — только для указанной страны; IBAN, артикулы и номера других стран не цепляются
txt = "WhatsApp 612 345 678, fijo 912345678, IBAN ES91 2100 0418 4502 0005 1332, ref 6123456789, +34 699-111-222"
assert extract_contacts(txt)["phones"] == ["+34699111222"]
assert extract_contacts(txt, ["es"])["phones"] == ["+34699111222", "+34612345678"], extract_contacts(txt, ["es"])
assert extract_contacts("06 12 34 56 78", ["fr"])["phones"] == ["+33612345678"]
assert extract_contacts("call (555) 123-4567 or 07700 900123", ["us", "gb"])["phones"] == ["+15551234567", "+447700900123"]
assert extract_contacts("0151 23456789", ["de"])["phones"] == ["+4915123456789"]
assert extract_contacts("612 345 678", ["fr"])["phones"] == []
assert extract_contacts("Тел. 8 701 234 56 78, 8(777)1234567", ["kz"])["phones"] == ["+77012345678", "+77771234567"]

# разбор объявлений по одному: кривое пропускается, None — отсеяно правилами, всё кривое — формат сменился
parse = lambda o: None if o.get("skip") else {"id": o["id"]}
assert bot.parse_each([{"id": 1}, {"oops": 1}, {"skip": 1}, {"id": 2}], parse, "x") == [{"id": 1}, {"id": 2}]
assert bot.parse_each([{"skip": 1}], parse, "x") == [] and bot.parse_each([], parse, "x") == []
for bad_call in (lambda: bot.parse_each([{"oops": 1}, {}], parse, "x"), lambda: bot.items_of({"data": {}}, "data", "items"),
                 lambda: bot.items_of({"items": None}, "items")):
    try:
        bad_call()
    except RuntimeError as e:
        assert "формат ответа изменился" in str(e), e
    else:
        raise AssertionError("ожидали RuntimeError")
assert bot.items_of({"a": {"b": []}}, "a", "b") == []

# время публикации по меткам id: id 100 видели в t=0, id 200 — в t=600
bot.db = sqlite3.connect(":memory:")
bot.db.execute("create table marks(site text, max_id int, ts real)")
bot.db.executemany("insert into marks values('x', ?, ?)", [(100, 0), (200, 600)])
now = 3600
assert posted_at("x", 150, now) == (300, False)    # между метками — интерполяция
assert posted_at("x", 200, now) == (600, False)
assert posted_at("x", 50, now) == (0, True)        # старше первой метки — только «раньше»
assert posted_at("x", 300, now) == (2100, False)   # новее всех — середина между последней меткой и сейчас
assert posted_at("y", 50, now) == (now, False)     # меток нет

# черновик со «старым» id, опубликованный сейчас, стоит в выдаче выше новых — время не старше тех, что ниже
items = [{"id": i, "market": "x"} for i in ("300", "150", "250", "50")]
bot.estimate_ts(items, now)
assert [(i["ts"], i["ts_older"]) for i in items] == [(2100, False), (2100, False), (2100, False), (0, True)], items

# чистка seen: отсчёт от последней проверки задачи — задача на паузе (2) ничего не теряет
bot.db.execute("create table seen(task_id int, item_id text, ts real, primary key(task_id, item_id))")
bot.db.execute("create table sent(chat_id int, item text, ts real, primary key(chat_id, item))")
day = 86400
bot.db.executemany("insert into seen values(?,?,?)",
                   [(1, "old", 0), (1, "kept", 9 * day), (1, "new", 10 * day), (2, "paused", 0)])
bot.prune_seen()
assert {r[0] for r in bot.db.execute("select item_id from seen")} == {"kept", "new", "paused"}
print("ok")
