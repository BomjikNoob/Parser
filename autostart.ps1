# Автозапуск бота при входе в Windows, без окна консоли (через Планировщик заданий).
#   powershell -ExecutionPolicy Bypass -File autostart.ps1          — включить и сразу запустить
#   powershell -ExecutionPolicy Bypass -File autostart.ps1 -Remove  — выключить и остановить
# Логи — в parser.log рядом с bot.py.
param([switch]$Remove)

$name = "ParserBot"
if ($Remove) {
    Stop-ScheduledTask -TaskName $name -ErrorAction SilentlyContinue
    Unregister-ScheduledTask -TaskName $name -Confirm:$false -ErrorAction SilentlyContinue
    Get-CimInstance Win32_Process -Filter "Name = 'pythonw.exe'" |
        Where-Object { $_.CommandLine -like "*$PSScriptRoot*bot.py*" } |
        ForEach-Object { Stop-Process -Id $_.ProcessId -Force }
    "Автозапуск выключен, бот остановлен."
    exit
}

$pythonw = (Get-Command pythonw.exe -ErrorAction Stop).Source
$action = New-ScheduledTaskAction -Execute $pythonw -Argument "`"$PSScriptRoot\bot.py`"" -WorkingDirectory $PSScriptRoot
$trigger = New-ScheduledTaskTrigger -AtLogOn -User $env:USERNAME
# без лимита времени работы; если процесс упал — перезапуск каждую минуту; второй экземпляр не запускать
$settings = New-ScheduledTaskSettingsSet -ExecutionTimeLimit ([TimeSpan]::Zero) -RestartCount 999 `
    -RestartInterval (New-TimeSpan -Minutes 1) -MultipleInstances IgnoreNew `
    -AllowStartIfOnBatteries -DontStopIfGoingOnBatteries -StartWhenAvailable
Register-ScheduledTask -TaskName $name -Action $action -Trigger $trigger -Settings $settings -Force | Out-Null
Start-ScheduledTask -TaskName $name
"Автозапуск включён: бот запущен в фоне и будет стартовать при каждом входе в Windows. Логи: $PSScriptRoot\parser.log"
