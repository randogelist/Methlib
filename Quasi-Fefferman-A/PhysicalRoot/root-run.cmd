@echo off
setlocal EnableExtensions
rem External native Windows Lean only. Preserve all Lake and Mathlib caches.
set "QFA_ROOT_PACKAGE=%~dp0"
set "PYTHONUTF8=1"
set "MATHLIB_NO_CACHE_ON_UPDATE=1"
pushd "%QFA_ROOT_PACKAGE%"
py -3 scripts\root_audit.py --external
set "QFA_ROOT_EXIT=%ERRORLEVEL%"
popd
exit /b %QFA_ROOT_EXIT%
