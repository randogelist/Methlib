@echo off
setlocal EnableExtensions DisableDelayedExpansion
pushd "%~dp0" || exit /b 2
if not defined LEAN_EXE set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.34.0-rc1\bin\lean.exe"
if not defined MATHLIB_CACHE (
 echo ERROR=MATHLIB_CACHE_NOT_SET
 echo Set MATHLIB_CACHE to the directory containing Mathlib.olean compiled by this exact Lean toolchain.
 popd
 exit /b 12
)
if not exist "%MATHLIB_CACHE%\Mathlib.olean" (
 echo ERROR=MATHLIB_OLEAN_MISSING
 popd
 exit /b 13
)
if not exist "_build\lib\lean" mkdir "_build\lib\lean"
if not exist "_evidence" mkdir "_evidence"
set "LEAN_PATH=%CD%\_build\lib\lean;%MATHLIB_CACHE%"
"%LEAN_EXE%" --version > "_evidence\compiler.txt" 2>&1
"%LEAN_EXE%" -o "%CD%\_build\lib\lean\ERDOS_687_CRT_BKQR.olean" "%CD%\ERDOS_687_CRT_BKQR.lean" > "_evidence\core-build.log" 2>&1
if errorlevel 1 (
 type "_evidence\core-build.log"
 echo CORE_COMPILE=FAIL
 popd
 exit /b 21
)
type "_evidence\core-build.log"
echo CORE_COMPILE=PASS
echo AXIOM_AUDIT=INSPECT_THEOREM_LEVEL_OUTPUT
echo EXTERNAL_JOIN=NOT_RUN_IN_RC1
popd
exit /b 0
