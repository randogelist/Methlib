@echo off
setlocal EnableExtensions
rem External native Windows Lean only. Preserve all Lake and Mathlib caches.
set "QFA_PACKAGE=%~dp0"
set "PYTHONUTF8=1"
set "MATHLIB_NO_CACHE_ON_UPDATE=1"
pushd "%QFA_PACKAGE%"
py -3 scripts\audit.py --external
set "QFA_EXIT=%ERRORLEVEL%"
popd
exit /b %QFA_EXIT%
