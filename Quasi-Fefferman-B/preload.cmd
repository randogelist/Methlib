@echo off
setlocal EnableExtensions
rem External Windows Lean 4.33.0. Import closure: 74 modules, 409 declarations.
call "%~dp0run.cmd" --target QuasiFeffermanB.Endpoints.Root
exit /b %errorlevel%
