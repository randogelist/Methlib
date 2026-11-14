@echo off
setlocal EnableExtensions
cd /d "%~dp0"
set "PYTHONUTF8=1"
set "MATHLIB_NO_CACHE_ON_UPDATE=1"
set "LEAN_NUM_THREADS=2"
python scripts\audit.py --external
set "RC=%ERRORLEVEL%"
if not "%RC%"=="0" exit /b %RC%
endlocal
