@echo off
setlocal EnableExtensions DisableDelayedExpansion
set "PYTHONUTF8=1"
rem Resolve the batch path once, before changing the current directory.
for %%I in ("%~dp0.") do set "RH_COORDINATE_ROOT=%%~fI"
pushd "%RH_COORDINATE_ROOT%"
if errorlevel 1 exit /b 11
where py >nul 2>&1
if not errorlevel 1 goto run_py
where python >nul 2>&1
if not errorlevel 1 goto run_python
echo RUN=BLOCKED
echo REASON=PYTHON_3_REQUIRED
popd
exit /b 10

:run_py
py -3 "%RH_COORDINATE_ROOT%\ci\run_coordinates.py" %*
set "RH_COORDINATE_EXIT=%ERRORLEVEL%"
goto finish

:run_python
python "%RH_COORDINATE_ROOT%\ci\run_coordinates.py" %*
set "RH_COORDINATE_EXIT=%ERRORLEVEL%"

:finish
popd
exit /b %RH_COORDINATE_EXIT%
