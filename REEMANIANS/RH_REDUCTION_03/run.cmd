@echo off
setlocal EnableExtensions EnableDelayedExpansion
set "PACKAGE=RH_QUADRATIC_COFINAL_433_v0_2_0_FIX1"
set "ROOT=%~dp0"
if not exist "!ROOT!RH_QUADRATIC_COFINAL.lean" (
  echo RUN=FAIL_COFINAL_SOURCE_LAYOUT
  exit /b 2
)
if not exist "!ROOT!Audit.lean" (
  echo RUN=FAIL_BASE_AUDIT_SOURCE_LAYOUT
  exit /b 2
)
if not exist "!ROOT!AuditCofinal.lean" (
  echo RUN=FAIL_COFINAL_AUDIT_SOURCE_LAYOUT
  exit /b 2
)
if not exist "!ROOT!RH_QUADRATIC_LYAPUNOV.lean" (
  echo RUN=FAIL_SOURCE_LAYOUT
  exit /b 2
)
pushd "!ROOT!"
if errorlevel 1 exit /b 2
set "EVIDENCE=!ROOT!evidence"
set "OUT=!ROOT!_build\lib\lean"
if not exist "!EVIDENCE!" mkdir "!EVIDENCE!" >nul 2>nul
if not exist "!OUT!" mkdir "!OUT!" >nul 2>nul
set "BUILD_LOG=!EVIDENCE!\run-build.log"
set "AUDIT_LOG=!EVIDENCE!\run-audit.log"
> "!BUILD_LOG!" echo PACKAGE=!PACKAGE!
> "!AUDIT_LOG!" echo PACKAGE=!PACKAGE!
call :mark "MODE=NATIVE_WINDOWS_CACHED_DEPENDENCIES"
call :mark "NETWORK=NOT_USED"
call :mark "LAKE=NOT_USED"
call :mark "POWERSHELL=NOT_USED"
call :mark "SOURCE_LAYOUT=PASS"
call :mark "HXY_BASELINE_REBUILD=DISABLED"
if not defined HXY_LEAN_EXE set "HXY_LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
if not exist "!HXY_LEAN_EXE!" (
  call :mark "RUN=FAIL_LEAN_4_33_NOT_FOUND"
  goto :failed
)
set "HXY_FOUND="
if defined HXY_CACHE_LEAN call :try_hxy "!HXY_CACHE_LEAN!"
if not defined HXY_FOUND if defined LEAN_ANCHORINGS_HOME call :try_hxy "!LEAN_ANCHORINGS_HOME!\HXY_THREE_SPACES_433\oleans"
if not defined HXY_FOUND call :try_hxy "%LOCALAPPDATA%\LEAN_ANCHORINGS\HXY_THREE_SPACES_433\oleans"
if not defined HXY_FOUND call :try_hxy "%USERPROFILE%\Downloads\HXY_THREE_SPACES_433_v0_1_0_FIX6\_build\lib\lean"
if not defined HXY_FOUND (
  call :mark "RUN=FAIL_HXY_OLEAN_CACHE_MISSING"
  goto :failed
)
set "HXY_CACHE_LEAN=!HXY_FOUND!"
set "MATHLIB_ROOT="
if defined MATHLIB_CACHE_ROOT call :try_mathlib_root "!MATHLIB_CACHE_ROOT!"
if not defined MATHLIB_ROOT call :try_mathlib_root "%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1"
if not defined MATHLIB_ROOT for /d %%D in ("%USERPROFILE%\lean-native\*") do (
  if not defined MATHLIB_ROOT call :try_mathlib_root "%%~fD"
)
if not defined MATHLIB_ROOT (
  call :mark "RUN=FAIL_MATHLIB_CACHE_MISSING"
  goto :failed
)
set "LEAN_PATH=!OUT!;!HXY_CACHE_LEAN!"
if exist "!MATHLIB_ROOT!\.lake\build\lib\lean" set "LEAN_PATH=!LEAN_PATH!;!MATHLIB_ROOT!\.lake\build\lib\lean"
for /d %%P in ("!MATHLIB_ROOT!\.lake\packages\*") do (
  if exist "%%~fP\.lake\build\lib\lean" set "LEAN_PATH=!LEAN_PATH!;%%~fP\.lake\build\lib\lean"
)
set "LEAN_SRC_PATH="
set "LEAN_NUM_THREADS=16"
set "LEAN_OPTS=-j16 -DmaxHeartbeats=4000000 -DmaxRecDepth=4096"
call :mark "LEAN_EXE=!HXY_LEAN_EXE!"
call :mark "HXY_CACHE_LEAN=!HXY_CACHE_LEAN!"
call :mark "MATHLIB_ROOT=!MATHLIB_ROOT!"
"!HXY_LEAN_EXE!" --version > "!EVIDENCE!\lean-version.log" 2>&1
if errorlevel 1 goto :failed
findstr /C:"version 4.33.0" "!EVIDENCE!\lean-version.log" >nul 2>nul
if errorlevel 1 (
  call :mark "RUN=FAIL_WRONG_LEAN_VERSION"
  goto :failed
)
type "!EVIDENCE!\lean-version.log"
call :mark "COMPILE=RH_QUADRATIC_LYAPUNOV"
"!HXY_LEAN_EXE!" !LEAN_OPTS! -o "!OUT!\RH_QUADRATIC_LYAPUNOV.olean" "!ROOT!RH_QUADRATIC_LYAPUNOV.lean" >> "!BUILD_LOG!" 2>&1
if errorlevel 1 (
  call :mark "COMPILE_FAIL=RH_QUADRATIC_LYAPUNOV"
  goto :failed
)
call :mark "COMPILE_PASS=RH_QUADRATIC_LYAPUNOV"
call :mark "COMPILE=RH_QUADRATIC_COFINAL"
"!HXY_LEAN_EXE!" !LEAN_OPTS! -o "!OUT!\RH_QUADRATIC_COFINAL.olean" "!ROOT!RH_QUADRATIC_COFINAL.lean" >> "!BUILD_LOG!" 2>&1
if errorlevel 1 (
  call :mark "COMPILE_FAIL=RH_QUADRATIC_COFINAL"
  goto :failed
)
call :mark "COMPILE_PASS=RH_QUADRATIC_COFINAL"
call :mark "AXIOM_AUDIT=START"
call :mark "AUDIT_FILE=Audit.lean"
"!HXY_LEAN_EXE!" !LEAN_OPTS! "!ROOT!Audit.lean" > "!AUDIT_LOG!" 2>&1
if errorlevel 1 goto :failed
call :mark "AUDIT_FILE=AuditCofinal.lean"
"!HXY_LEAN_EXE!" !LEAN_OPTS! "!ROOT!AuditCofinal.lean" >> "!AUDIT_LOG!" 2>&1
if errorlevel 1 goto :failed
findstr /C:"sorryAx" "!AUDIT_LOG!" >nul 2>nul
if not errorlevel 1 (
  call :mark "RUN=FAIL_SORRYAX"
  goto :failed
)
for %%X in (RHQuadratic.actual_squareEnergy_le_one_iff_nativeRH RHQuadratic.actual_exists_uniform_squareEnergy_iff_nativeRH RHQuadratic.actual_quadratic_unit_steps_iff_nativeRH RHQuadratic.actual_all_scalar_gates_iff_nativeRH RHQuadratic.source_quadratic_gate_iff RHQuadratic.checkRationalSquareGate_sound) do (
  findstr /C:"%%X" "!AUDIT_LOG!" >nul 2>nul
  if errorlevel 1 (
    call :mark "RUN=FAIL_AUDIT_ENDPOINT_MISSING=%%X"
    goto :failed
  )
)
for %%X in (RHQuadratic.nativeRH_of_cofinal_squareEnergy_bound RHQuadratic.cofinal_squareEnergy_iff_nativeRH RHQuadratic.eventual_large_squareEnergy_of_not_nativeRH) do (
  findstr /C:"%%X" "!AUDIT_LOG!" >nul 2>nul
  if errorlevel 1 (
    call :mark "RUN=FAIL_COFINAL_AUDIT_ENDPOINT_MISSING=%%X"
    goto :failed
  )
)
call :mark "ACTUAL_XI_COFINAL_EQUIVALENCE=PASS"
call :mark "COFINAL_HITS=UNBOUNDED_FAMILY_REQUIRED"
call :mark "FINITE_SINGLE_WITNESS_SOUNDNESS=OPEN"
call :mark "ACTUAL_XI_QUADRATIC_EQUIVALENCES=PASS"
call :mark "FINITE_ONE_STEP_RATIONAL_GATE=PASS"
call :mark "SOURCE_STEP=EXPLICIT_PREMISE"
call :mark "STRONG_MONOTONICITY_RH_FORWARD=NOT_AUDITED"
call :mark "ACTUAL_XI_TAIL_WITNESS=OPEN"
call :mark "ACCEPTED_RAW_WITNESS=NOT_CLAIMED"
call :mark "RH_PROVED=NO"
call :mark "RUN=PASS_CANDIDATE_COMPILED_AND_AUDITED"
popd
endlocal & exit /b 0
:mark
echo %~1
>> "!BUILD_LOG!" echo %~1
exit /b 0
:try_hxy
if defined HXY_FOUND exit /b 0
if exist "%~1\RH_HilbertLimit\AnalyticClosure.olean" set "HXY_FOUND=%~1"
exit /b 0
:try_mathlib_root
if defined MATHLIB_ROOT exit /b 0
if exist "%~1\.lake\packages\mathlib\.lake\build\lib\lean\Mathlib.olean" set "MATHLIB_ROOT=%~1"
exit /b 0
:failed
call :mark "RUN=FAIL_COMPILE_OR_AUDIT"
echo BUILD_LOG=!BUILD_LOG!
echo AUDIT_LOG=!AUDIT_LOG!
if exist "!BUILD_LOG!" type "!BUILD_LOG!"
if exist "!AUDIT_LOG!" type "!AUDIT_LOG!"
popd
endlocal & exit /b 1
