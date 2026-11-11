@echo off
setlocal EnableExtensions
cd /d "%~dp0"
where lake >nul 2>nul
if errorlevel 1 (
  echo ERROR: elan and Lake are required.
  exit /b 1
)
where python >nul 2>nul
if errorlevel 1 (
  echo ERROR: Python 3 is required for the exact-type and axiom audit checker.
  exit /b 1
)
if not exist evidence mkdir evidence
call lake env lean --version > evidence\lean-version.txt 2>&1
if errorlevel 1 goto fail
type evidence\lean-version.txt
findstr /C:"version 4.33.0," evidence\lean-version.txt >nul
if errorlevel 1 goto fail
python ci\check_sources.py > evidence\source-policy.json 2>&1
if errorlevel 1 goto fail
python ci\test_check_axioms.py > evidence\audit-checker-tests.log 2>&1
if errorlevel 1 goto fail
call lake exe cache get > evidence\cache.log 2>&1
if errorlevel 1 goto fail
git -C .lake\packages\mathlib rev-parse HEAD > evidence\mathlib-revision.txt
if errorlevel 1 goto fail
set /p AX6_MATHLIB_REV=<evidence\mathlib-revision.txt
if not "%AX6_MATHLIB_REV%"=="db584cd6d46c92f209a44c0f1c829460d327499d" goto fail
call lake build > evidence\build.log 2>&1
if errorlevel 1 goto fail
python ci\build_critical.py
if errorlevel 1 goto fail
call lake env lean ci\Audit.lean > evidence\axioms.log 2>&1
if errorlevel 1 goto fail
python ci\check_axioms.py evidence\axioms.log ci\expected_axioms.json > evidence\audit.json 2>&1
if errorlevel 1 goto fail
type evidence\audit.json
echo PASS: cached native Lean 4.33.0 build and exact-type axiom audit.
exit /b 0
:fail
echo FAIL: inspect the files in evidence.
exit /b 1
