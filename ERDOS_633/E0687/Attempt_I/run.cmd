@echo off
setlocal EnableExtensions EnableDelayedExpansion
cd /d "%~dp0"
set "EVIDENCE=%CD%\_evidence"
if not exist "%EVIDENCE%" mkdir "%EVIDENCE%"
if not exist "%CD%\_build\lib\lean" mkdir "%CD%\_build\lib\lean"
if not defined LEAN_EXE set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.34.0-rc1\bin\lean.exe"
if not exist "%LEAN_EXE%" (
  echo LEAN_EXE_NOT_FOUND
  exit /b 2
)
if not defined MATHLIB_OLEAN_DIR (
  for %%D in (
    "%CD%\.lake\build\lib\lean"
    "%CD%\.lake\packages\mathlib\.lake\build\lib\lean"
    "%USERPROFILE%\Downloads\KTHETA_MO_RC1_CACHE\.lake\build\lib\lean"
    "%USERPROFILE%\Downloads\KTHETA_MO_RC1_CACHE\.lake\packages\mathlib\.lake\build\lib\lean"
  ) do (
    if not defined MATHLIB_OLEAN_DIR if exist "%%~D\Mathlib.olean" set "MATHLIB_OLEAN_DIR=%%~D"
  )
)
if not defined MATHLIB_OLEAN_DIR (
  echo CACHED_MATHLIB_NOT_FOUND
  exit /b 3
)
set "LEAN_PATH=%CD%\_build\lib\lean;%MATHLIB_OLEAN_DIR%;%LEAN_PATH%"
"%LEAN_EXE%" --version >"%EVIDENCE%\lean-version.txt" 2>&1
"%LEAN_EXE%" -o "%CD%\_build\lib\lean\Erdos687.olean" "%CD%\Erdos687.lean" >"%EVIDENCE%\run-build.log" 2>&1
if errorlevel 1 (
  echo DAG_COMPILE=FAIL
  exit /b 5
)
"%LEAN_EXE%" "Audit.lean" >"%EVIDENCE%\run-audit.log" 2>&1
if errorlevel 1 (
  echo AXIOM_AUDIT=FAIL_COMPILER
  exit /b 6
)
findstr /i /c:"sorryAx" "%EVIDENCE%\run-audit.log" >nul
if not errorlevel 1 (
  echo AXIOM_AUDIT=FAIL_SORRY
  exit /b 7
)
echo DAG_COMPILE=PASS
echo AUDIT_LOG_CREATED=PASS
echo NOTE=Inspect theorem-level audit to certify A_TIER
exit /b 0
