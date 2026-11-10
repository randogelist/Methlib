@echo off
setlocal EnableExtensions DisableDelayedExpansion
rem NSE_DECOMP v0_1_9_FIX2 FASTCACHE: native Windows Lean 4.34.0-rc1, cache-only, -j16.
rem No lake update, cache get, lake build, clean, or dependency downloads.
"%SystemRoot%\System32\WindowsPowerShell\v1.0\powershell.exe" -NoLogo -NoProfile -NonInteractive -ExecutionPolicy Bypass -File "%~dp0support\run.ps1" %*
exit /b %ERRORLEVEL%
