@echo off
setlocal EnableExtensions DisableDelayedExpansion
pushd "%~dp0"
if errorlevel 1 exit /b 2
if not exist "%SystemRoot%\System32\cscript.exe" (
  echo RUN=FAIL_NATIVE_WINDOWS_CSCRIPT_REQUIRED
  popd
  exit /b 2
)
rem TRUSTED_FAST_V2. Native Windows; existing cached Mathlib; no runtime hashing.
rem No network, Lake, PowerShell, Python, WSL, or assistant-local Lean run.
"%SystemRoot%\System32\cscript.exe" //nologo //E:JScript "scripts\native-runner.js" C3 %*
set "HXY_EXIT=%ERRORLEVEL%"
popd
endlocal & exit /b %HXY_EXIT%
