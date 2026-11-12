@echo off
setlocal
cd /d "%~dp0"
set "SINGULARITY_EXTERNAL_COMPILER=1"
set "MATHLIB_NO_CACHE_ON_UPDATE=1"
where py >nul 2>nul
if errorlevel 1 (
  echo Python 3 launcher py is required.
  exit /b 1
)
where lake >nul 2>nul
if errorlevel 1 (
  echo Lean elan and lake are required.
  exit /b 1
)
py -3 ci\prepare_package.py --native "..\Singular-Axiomatic-closure" --extension "." --output ".work\package" --reuse-native-cache
if errorlevel 1 exit /b 1
cd /d "%~dp0.work\package"
call lake exe cache get >evidence\cache.log 2>&1
if errorlevel 1 (
  type evidence\cache.log
  exit /b 1
)
py -3 ci_singularity\test_endpoint_audit.py
if errorlevel 1 exit /b 1
py -3 ci_singularity\build_endpoints.py
set "SINGULARITY_RESULT=%ERRORLEVEL%"
type evidence\endpoint-status.json
exit /b %SINGULARITY_RESULT%
