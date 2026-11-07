@echo off
setlocal EnableExtensions
set "PACKAGE_ROOT=%~dp0"
cd /d "%PACKAGE_ROOT%"
if defined PYTHON_EXE (
  "%PYTHON_EXE%" "%PACKAGE_ROOT%scripts\admit_coordinates.py" %*
) else (
  python "%PACKAGE_ROOT%scripts\admit_coordinates.py" %*
)
exit /b %ERRORLEVEL%

