@echo off
setlocal
powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0support\run.ps1" %*
set "H12_EXIT_CODE=%ERRORLEVEL%"
exit /b %H12_EXIT_CODE%
