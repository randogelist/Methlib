@echo off
setlocal
set "COLLATZ_PS=%SystemRoot%\System32\WindowsPowerShell\v1.0\powershell.exe"
if not exist "%COLLATZ_PS%" (
  echo RUNNER_ERROR=WINDOWS_POWERSHELL_NOT_FOUND
  exit /b 1
)
if "%~1"=="" (
  "%COLLATZ_PS%" -NoProfile -ExecutionPolicy Bypass -File "%~dp0run.ps1"
) else (
  "%COLLATZ_PS%" -NoProfile -ExecutionPolicy Bypass -File "%~dp0replay.ps1" %*
)
set "COLLATZ_EXIT=%ERRORLEVEL%"
if not "%COLLATZ_EXIT%"=="0" echo RUNNER_EXIT_CODE=%COLLATZ_EXIT%
exit /b %COLLATZ_EXIT%
