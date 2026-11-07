@echo off
setlocal EnableExtensions
cd /d "%~dp0"
set "NETWORK=NOT_USED"
set "LAKE=NOT_USED"
if not exist "_evidence" mkdir "_evidence"
if not defined LEAN_EXE set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lean.exe"
if not exist "%LEAN_EXE%" (
  echo COMPILER=NOT_FOUND
  exit /b 20
)
"%LEAN_EXE%" --version > "_evidence\compiler.log" 2>&1
findstr /C:"4.34.1" "_evidence\compiler.log" >nul || exit /b 21
if not defined OAI_CACHE (
  echo OAI_CACHE=NOT_CONFIGURED
  exit /b 22
)
if not exist "%OAI_CACHE%\OAI\NumberTheory\Jacobsthal\Conclusions\QuadraticBound.olean" exit /b 23
if defined MATHLIB_CACHE (
  set "LEAN_PATH=%OAI_CACHE%;%MATHLIB_CACHE%;%LEAN_PATH%"
) else (
  set "LEAN_PATH=%OAI_CACHE%;%LEAN_PATH%"
)
"%LEAN_EXE%" -DautoImplicit=false -o "_evidence\AttemptE.olean" "AttemptE.lean" > "_evidence\core.log" 2>&1 || exit /b 24
set "LEAN_PATH=%CD%\_evidence;%LEAN_PATH%"
"%LEAN_EXE%" -DautoImplicit=false "ExternalRoot.lean" > "_evidence\external.log" 2>&1 || exit /b 25
python check_axioms.py "_evidence\core.log" core || exit /b 26
copy /b "_evidence\core.log"+"_evidence\external.log" "_evidence\combined.log" >nul
python check_axioms.py "_evidence\combined.log" external || exit /b 27
echo A_TIER_EXTERNAL=PASS_STANDARD_ONLY
