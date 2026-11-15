@echo off
setlocal EnableExtensions
cd /d "%~dp0..\.."
where lake >nul 2>nul
if errorlevel 1 (
  echo FAIL: Lake/Elan unavailable.
  exit /b 1
)
if not exist evidence mkdir evidence
call lake env lean --version > evidence\noether-lean-version.txt 2>&1
if errorlevel 1 goto fail
findstr /C:"version 4.33.0," evidence\noether-lean-version.txt >nul
if errorlevel 1 goto fail
call lake exe cache get > evidence\noether-cache.log 2>&1
if errorlevel 1 goto fail
call lake build SingularClosure.NoetherClosure.Root > evidence\noether-build.log 2>&1
if errorlevel 1 goto fail
call lake env lean ci\NoetherClosureAudit.lean > evidence\noether-axioms.log 2>&1
if errorlevel 1 goto fail
where python >nul 2>nul
if errorlevel 1 goto fail
python ci\check_axioms.py evidence\noether-axioms.log ci\noether_expected_axioms.json > evidence\noether-audit.json 2>&1
if errorlevel 1 goto fail
type evidence\noether-audit.json
echo PASS: external cached Noether root and checked theorem audit.
exit /b 0
:fail
echo FAIL: read evidence\noether-build.log and evidence\noether-axioms.log.
exit /b 1
