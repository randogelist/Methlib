@echo off
setlocal EnableExtensions
cd /d "%~dp0"
set "PKG=ERDOS687_ATTEMPT_B"
echo PACKAGE=%PKG%
echo MODE=NATIVE_WINDOWS_CACHED_ONLY
echo NETWORK=NOT_USED
echo LAKE=NOT_USED
if not defined LEAN_EXE set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lean.exe"
if not exist "%LEAN_EXE%" (
  echo PRECONDITION_FAIL=LEAN_4_34_1_MISSING
  exit /b 2
)
"%LEAN_EXE%" --version | findstr /C:"4.34.1" >nul
if errorlevel 1 (
  echo PRECONDITION_FAIL=LEAN_VERSION_MISMATCH
  exit /b 2
)
if not defined MATHLIB_LEAN_CACHE (
  echo PRECONDITION_FAIL=MATHLIB_LEAN_CACHE_MISSING
  exit /b 2
)
if not defined OAI_LEAN_CACHE (
  echo PRECONDITION_FAIL=OAI_LEAN_CACHE_MISSING
  exit /b 2
)
if not defined REFEREE_LEAN_CACHE (
  echo PRECONDITION_FAIL=REFEREE_LEAN_CACHE_MISSING
  exit /b 2
)
if not exist "%MATHLIB_LEAN_CACHE%\Mathlib.olean" (
  echo PRECONDITION_FAIL=MATHLIB_4341_OLEAN_MISSING
  exit /b 2
)
if not exist "%OAI_LEAN_CACHE%\OAI\NumberTheory\Jacobsthal\Main.olean" (
  echo PRECONDITION_FAIL=EXTERNAL_OAI_OLEAN_MISSING
  exit /b 2
)
if not exist "%REFEREE_LEAN_CACHE%\Bridge687.olean" (
  echo PRECONDITION_FAIL=EXTERNAL_BRIDGE_OLEAN_MISSING
  exit /b 2
)
set "LEAN_PATH=%~dp0;%REFEREE_LEAN_CACHE%;%OAI_LEAN_CACHE%;%MATHLIB_LEAN_CACHE%;%LEAN_PATH%"
"%LEAN_EXE%" -o "Erdos687Spectral.olean" "Erdos687Spectral.lean" > "run-build-core.log" 2>&1
if errorlevel 1 (
  echo BUILD_CORE=FAIL
  type "run-build-core.log"
  exit /b 1
)
"%LEAN_EXE%" -o "ExternalRoot.olean" "ExternalRoot.lean" > "run-build-root.log" 2>&1
if errorlevel 1 (
  echo BUILD_ROOT=FAIL
  type "run-build-root.log"
  exit /b 1
)
"%LEAN_EXE%" --trust=0 "Audit.lean" > "run-audit.log" 2>&1
if errorlevel 1 (
  echo AUDIT=FAIL
  type "run-audit.log"
  exit /b 1
)
findstr /I /C:"sorryAx" /C:"unexpected" /C:"unknown constant" "run-audit.log" >nul
if not errorlevel 1 (
  echo AUDIT=FAIL_UNAPPROVED_AXIOM_OR_UNKNOWN_CONSTANT
  exit /b 3
)
echo BUILD=PASS
echo AUDIT=REPORTS_GENERATED_REVIEW_AXIOM_LISTS
echo STATUS=A_TIER_CANDIDATE_UNTIL_MATCHING_AXIOM_VALIDATION
exit /b 0
