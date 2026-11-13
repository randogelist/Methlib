@echo off
setlocal
cd /d "%~dp0"
py -3 ci\stage.py --package .work\package
if errorlevel 1 exit /b %errorlevel%
py -3 ci\runner.py --package .work\package --phase all
exit /b %errorlevel%
