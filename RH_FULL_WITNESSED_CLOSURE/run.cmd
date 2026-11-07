@echo off
setlocal EnableExtensions DisableDelayedExpansion
cd /d "%~dp0"
where py >nul 2>&1
if not errorlevel 1 (
  py -3 "%~dp0ci\run_coordinates.py" %*
  exit /b
)
where python >nul 2>&1
if not errorlevel 1 (
  python "%~dp0ci\run_coordinates.py" %*
  exit /b
)
echo RUN=BLOCKED
echo REASON=PYTHON_3_REQUIRED
exit /b 10
