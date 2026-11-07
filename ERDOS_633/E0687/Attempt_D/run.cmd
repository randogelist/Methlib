@echo off
setlocal EnableExtensions
set "PKG=%~dp0"
set "EVID=%PKG%_evidence"
if not exist "%EVID%" mkdir "%EVID%"
echo PACKAGE=ERDOS_633_E0687_Attempt_D
echo MODE=NATIVE_WINDOWS_CACHED_ONLY
echo REQUIRED_LEAN=4.34.1
echo REQUIRED_EXTERNAL_PIN=adc7f1241b42e322a6451854ab7e4b4c146bf78a
if not defined LEAN_EXE set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lean.exe"
if not exist "%LEAN_EXE%" (echo ERROR=LEAN_MISSING& exit /b 2)
"%LEAN_EXE%" --version | findstr /C:"4.34.1" >nul
if errorlevel 1 (echo ERROR=LEAN_VERSION_MISMATCH& exit /b 3)
if not defined MATHLIB_OLEAN_ROOT (
 echo ERROR=SET_MATHLIB_OLEAN_ROOT_TO_MATCHING_CACHED_4_34_1
 exit /b 4
)
if not exist "%MATHLIB_OLEAN_ROOT%\Mathlib.olean" (echo ERROR=MATHLIB_CACHE_MISSING& exit /b 5)
set "LEAN_PATH=%EVID%;%MATHLIB_OLEAN_ROOT%;%LEAN_PATH%"
"%LEAN_EXE%" -o "%EVID%\ERDOS_687.olean" "%PKG%ERDOS_687.lean" >"%EVID%\core-build.log" 2>&1
if errorlevel 1 (type "%EVID%\core-build.log"& exit /b 6)
python "%PKG%ci\audit.py" --log "%EVID%\core-build.log" --scope core
if errorlevel 1 exit /b 7
echo CORE=PASS
if not defined OAI_OLEAN_ROOT (
 echo EXTERNAL_IMPORT=NOT_RUN_SET_OAI_OLEAN_ROOT
 exit /b 8
)
if not exist "%OAI_OLEAN_ROOT%\OAI\NumberTheory\Jacobsthal\Conclusions\QuadraticBound.olean" (echo EXTERNAL_CACHE=MISSING_QUADRATIC& exit /b 9)
if not exist "%OAI_OLEAN_ROOT%\OAI\NumberTheory\Jacobsthal\Conclusions\IteratedLogBound.olean" (echo EXTERNAL_CACHE=MISSING_ITERATEDLOG& exit /b 10)
set "LEAN_PATH=%EVID%;%OAI_OLEAN_ROOT%;%MATHLIB_OLEAN_ROOT%;%LEAN_PATH%"
"%LEAN_EXE%" -o "%EVID%\ERDOS_687_EXTERNAL.olean" "%PKG%ERDOS_687_EXTERNAL.lean" >"%EVID%\external-build.log" 2>&1
if errorlevel 1 (type "%EVID%\external-build.log"& exit /b 11)
python "%PKG%ci\audit.py" --log "%EVID%\external-build.log" --scope external
if errorlevel 1 exit /b 12
echo EXTERNAL_IMPORT=PASS
echo STRONG_EXPONENT_UNCONDITIONAL=OPEN
exit /b 0
