@echo off
setlocal EnableExtensions DisableDelayedExpansion
set "RH_PACKAGE_DIR=%~dp0"
if defined PYTHON_EXE goto use_explicit_python
where py.exe >nul 2>nul
if not errorlevel 1 goto use_py_launcher
where python.exe >nul 2>nul
if not errorlevel 1 goto use_python
echo ERROR=PYTHON_NOT_FOUND
exit /b 2
:use_py_launcher
py.exe -3 "%RH_PACKAGE_DIR%scripts\run_frontier.py" %*
exit /b %ERRORLEVEL%
:use_python
python.exe "%RH_PACKAGE_DIR%scripts\run_frontier.py" %*
exit /b %ERRORLEVEL%
:use_explicit_python
"%PYTHON_EXE%" "%RH_PACKAGE_DIR%scripts\run_frontier.py" %*
exit /b %ERRORLEVEL%
