@echo off
setlocal EnableExtensions
cd /d "%~dp0"
echo PACKAGE=ERDOS_687_ATTEMPT_F
echo MODE=NATIVE_WINDOWS_CACHED_DEPENDENCIES
echo NETWORK=NOT_USED
echo LAKE=NOT_USED
if not defined LEAN_EXE set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lean.exe"
if not exist "%LEAN_EXE%" (echo LEAN_4_34_1_EXE=NOT_FOUND & exit /b 2)
"%LEAN_EXE%" --version | findstr /c:"4.34.1" >nul
if errorlevel 1 (echo COMPILER_MISMATCH_EXPECTED_4_34_1 & exit /b 3)
if not defined CACHED_LEAN_PATH (echo CACHED_LEAN_PATH=MISSING & exit /b 4)
if not defined BRIDGE687_ROOT (echo BRIDGE687_ROOT=MISSING & exit /b 5)
if not exist "%BRIDGE687_ROOT%\Bridge687.olean" (echo BRIDGE687_OLEAN=MISSING & exit /b 6)
if not exist "_evidence" mkdir "_evidence"
set "LEAN_PATH=%CD%;%BRIDGE687_ROOT%;%CACHED_LEAN_PATH%"
"%LEAN_EXE%" -o "FiniteCore.olean" "FiniteCore.lean" > "_evidence\finite-build.log" 2>&1
if errorlevel 1 (echo FINITE_BUILD=FAIL & exit /b 10)
"%LEAN_EXE%" -o "ExternalRoot.olean" "ExternalRoot.lean" > "_evidence\external-root-build.log" 2>&1
if errorlevel 1 (echo EXTERNAL_BUILD=FAIL & exit /b 11)
"%LEAN_EXE%" --trust=0 "Audit.lean" > "_evidence\axiom-audit.log" 2>&1
if errorlevel 1 (echo AXIOM_AUDIT=FAIL & exit /b 12)
echo BUILD=PASS
echo THEOREM_AXIOM_AUDIT=REQUIRES_REVIEW_OF_EVIDENCE
echo NEAR_LINEAR_ERDOS_687=OPEN
