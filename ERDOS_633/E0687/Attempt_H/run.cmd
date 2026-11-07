@echo off
setlocal
cd /d "%~dp0"
set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lean.exe"
if not exist "%LEAN_EXE%" (echo TOOLCHAIN_MISSING=Lean_4.34.1 & exit /b 11)
if not defined LEAN_PATH (echo LEAN_PATH_MISSING=CACHED_MATHLIB_REQUIRED & exit /b 12)
"%LEAN_EXE%" --trust=0 -o Erdos687AttemptH.olean Erdos687AttemptH.lean
if errorlevel 1 exit /b 20
"%LEAN_EXE%" --trust=0 Audit.lean
if errorlevel 1 exit /b 21
echo BUILD_AND_AUDIT_COMMANDS=PASS
echo AXIOM_CONTENT_REQUIRES_INSPECTION
