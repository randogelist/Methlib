@echo off
setlocal EnableExtensions DisableDelayedExpansion
pushd "%~dp0" || exit /b 1

rem The committed Lake manifest pins Mathlib and its transitive dependencies.
rem Cache downloads and local Lake build products are reused between runs.
set "PYTHON=python"
where py.exe >nul 2>nul
if not errorlevel 1 set "PYTHON=py -3"

call lake exe cache get
if errorlevel 1 goto :failed
call lake build FeffermanD
if errorlevel 1 goto :failed

call lake env lean ci\Audit.lean >audit.log 2>&1
set "rc=%errorlevel%"
type audit.log
if not "%rc%"=="0" goto :done
%PYTHON% ci\check_axioms.py audit.log
if errorlevel 1 goto :failed

echo RUN=PASS
set "rc=0"
goto :done

:failed
set "rc=%errorlevel%"
:done
popd
endlocal & exit /b %rc%
