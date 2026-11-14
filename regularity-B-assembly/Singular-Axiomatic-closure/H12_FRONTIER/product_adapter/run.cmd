@echo off
setlocal
cd /d "%~dp0.."
python ci\run_product_windows.py
exit /b %ERRORLEVEL%
