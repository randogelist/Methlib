@echo off
setlocal
set "HVR_PS=%SystemRoot%\System32\WindowsPowerShell\v1.0\powershell.exe"
if not exist "%HVR_PS%" (
  echo LAUNCHER_ERROR=Windows_PowerShell_not_found
  exit /b 1
)
"%HVR_PS%" -NoProfile -ExecutionPolicy Bypass -File "%~dp0run.ps1" %*
set "HVR_EXIT=%ERRORLEVEL%"
if not "%HVR_EXIT%"=="0" echo LAUNCHER_EXIT_CODE=%HVR_EXIT%
exit /b %HVR_EXIT%
