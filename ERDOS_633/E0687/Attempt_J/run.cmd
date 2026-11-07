@echo off
setlocal EnableExtensions
rem Erdős 687 / Attempt_J; remote CI is preferred. No local Lean is run by ChatGPT.
rem Requires exact pinned OpenAI math and Bridge687 source trees, Lean v4.34.1.
set "ATTEMPT=%~dp0"
if not defined OAI_LEAN_ROOT (
  echo ERROR=OAI_LEAN_ROOT_NOT_CONFIGURED
  exit /b 2
)
if not defined BRIDGE687_SOURCE (
  echo ERROR=BRIDGE687_SOURCE_NOT_CONFIGURED
  exit /b 2
)
if not exist "%BRIDGE687_SOURCE%" (
  echo ERROR=BRIDGE687_SOURCE_NOT_FOUND
  exit /b 2
)
set "EXPECTED_LEAN=leanprover/lean4:v4.34.1"
if not exist "%OAI_LEAN_ROOT%\lean-toolchain" (
  echo ERROR=OAI_MANIFEST_NOT_FOUND
  exit /b 3
)
findstr /C:"%EXPECTED_LEAN%" "%OAI_LEAN_ROOT%\lean-toolchain" >nul || (
  echo ERROR=TOOLCHAIN_MISMATCH
  exit /b 3
)
pushd "%OAI_LEAN_ROOT%" || exit /b 4
lean --version || goto :fail
call lake update || goto :fail
call lake exe cache get || goto :fail
call lake -j1 build OAI.NumberTheory.Jacobsthal.Main || goto :fail
copy /Y "%BRIDGE687_SOURCE%" ".\Bridge687.lean" >nul || goto :fail
copy /Y "%ATTEMPT%Erdos687AttemptJ.lean" ".\Erdos687AttemptJ.lean" >nul || goto :fail
copy /Y "%ATTEMPT%Audit.lean" ".\Audit.lean" >nul || goto :fail
call lake env lean --trust=0 -o ".lake\build\lib\lean\Bridge687.olean" Bridge687.lean || goto :fail
call lake env lean --trust=0 -o ".lake\build\lib\lean\Erdos687AttemptJ.olean" Erdos687AttemptJ.lean || goto :fail
call lake env lean --trust=0 Audit.lean || goto :fail
echo DAG_COMPILE=PASS
echo AXIOM_AUDIT=REQUIRES_MANUAL_STANDARD_ONLY_REVIEW
echo STRONG_ERDOS_687_ENDPOINT=NOT_PROVED
popd
exit /b 0
:fail
echo DAG_COMPILE=FAIL
popd
exit /b 1
