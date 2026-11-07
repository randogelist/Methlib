@echo off
setlocal EnableExtensions
rem Native Windows replay; requires the pinned upstream checkouts and Lean 4.34.1.
if not defined OAI_LEAN_ROOT (
  echo Set OAI_LEAN_ROOT to the pinned openai/math/lean source directory.
  exit /b 2
)
if not defined BRIDGE687_SOURCE (
  echo Set BRIDGE687_SOURCE to the pinned Bridge687.lean file.
  exit /b 2
)
if not exist "%BRIDGE687_SOURCE%" exit /b 2
set "ATTEMPT=%~dp0"
pushd "%OAI_LEAN_ROOT%" || exit /b 2
lean --version || goto :fail
call lake update || goto :fail
call lake exe cache get || goto :fail
call lake build OAI.NumberTheory.Jacobsthal.Main || goto :fail
copy /Y "%BRIDGE687_SOURCE%" ".\Bridge687.lean" >nul || goto :fail
copy /Y "%ATTEMPT%Erdos687AttemptA.lean" ".\Erdos687AttemptA.lean" >nul || goto :fail
copy /Y "%ATTEMPT%Audit.lean" ".\Audit.lean" >nul || goto :fail
call lake env lean -o ".lake\build\lib\lean\Bridge687.olean" Bridge687.lean || goto :fail
call lake env lean -o ".lake\build\lib\lean\Erdos687AttemptA.olean" Erdos687AttemptA.lean || goto :fail
call lake env lean --trust=0 Audit.lean || goto :fail
echo COMPILATION=PASS
echo THEOREM_AXIOM_AUDIT=INSPECT_OUTPUT
popd
exit /b 0
:fail
echo RUN=FAIL
popd
exit /b 1
