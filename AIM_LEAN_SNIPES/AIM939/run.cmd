@echo off
setlocal EnableExtensions DisableDelayedExpansion
cd /d "%~dp0"
if errorlevel 1 exit /b 1

set "AIM939_PACKAGE=AIM939_DIAGONAL_CONCAVITY_COUNTEREXAMPLE_433_v0_1_0_FIX3"
if not defined AIM939_LEAN_EXE set "AIM939_LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
if not defined AIM939_CACHE_ROOT set "AIM939_CACHE_ROOT=%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1"
if not defined AIM939_THREADS set "AIM939_THREADS=16"
set "AIM939_EVIDENCE=%CD%\evidence\r-%RANDOM%-%RANDOM%-%RANDOM%"
set "AIM939_BUILD=%AIM939_EVIDENCE%\build"
set "AIM939_MATHLIB=%AIM939_CACHE_ROOT%\.lake\packages\mathlib\.lake\build\lib\lean"

if not exist "%AIM939_LEAN_EXE%" (
  echo ERROR=NATIVE_LEAN_433_EXECUTABLE_MISSING
  echo EXPECTED="%AIM939_LEAN_EXE%"
  exit /b 1
)
if not exist "%AIM939_MATHLIB%\Mathlib.olean" (
  echo ERROR=CACHED_MATHLIB_MISSING
  echo EXPECTED="%AIM939_MATHLIB%\Mathlib.olean"
  exit /b 1
)
if not exist "sources.sha256" (
  echo ERROR=SOURCE_MANIFEST_MISSING
  exit /b 1
)

mkdir "%AIM939_BUILD%\AIM939" >nul 2>&1
if errorlevel 1 (
  echo ERROR=EVIDENCE_DIRECTORY_CREATION_FAILED
  exit /b 1
)
echo PACKAGE=%AIM939_PACKAGE%
echo EVIDENCE="%AIM939_EVIDENCE%"
echo CACHED_MATHLIB="%AIM939_MATHLIB%"
echo MODE=NATIVE_WINDOWS_CACHED_DEPENDENCIES

"%AIM939_LEAN_EXE%" --version >"%AIM939_EVIDENCE%\lean-version.log" 2>&1
if errorlevel 1 goto failed
type "%AIM939_EVIDENCE%\lean-version.log"
findstr /L /C:"version 4.33.0," "%AIM939_EVIDENCE%\lean-version.log" >nul
if errorlevel 1 (
  echo ERROR=LEAN_VERSION_MISMATCH_EXPECTED_4.33.0
  goto failed
)

type nul >"%AIM939_EVIDENCE%\source-hashes.log"
for /f "usebackq tokens=1,2" %%H in ("sources.sha256") do (
  call :check_hash "%%I" "%%H"
  if errorlevel 1 goto failed
)
certutil -hashfile "sources.sha256" SHA256 >"%AIM939_EVIDENCE%\manifest-hash.log" 2>&1
if errorlevel 1 goto failed
copy /y "sources.sha256" "%AIM939_EVIDENCE%\sources.sha256" >nul
if errorlevel 1 goto failed
if exist "%AIM939_CACHE_ROOT%\.lake\packages\mathlib\lean-toolchain" copy /y "%AIM939_CACHE_ROOT%\.lake\packages\mathlib\lean-toolchain" "%AIM939_EVIDENCE%\mathlib-lean-toolchain.txt" >nul
if exist "%AIM939_CACHE_ROOT%\.lake\packages\mathlib\lake-manifest.json" copy /y "%AIM939_CACHE_ROOT%\.lake\packages\mathlib\lake-manifest.json" "%AIM939_EVIDENCE%\mathlib-lake-manifest.json" >nul

set "LEAN_PATH=%AIM939_BUILD%;%AIM939_MATHLIB%"
for /d %%D in ("%AIM939_CACHE_ROOT%\.lake\packages\*") do call :add_cache "%%~fD\.lake\build\lib\lean"
set "LEAN_NUM_THREADS=%AIM939_THREADS%"
>"%AIM939_EVIDENCE%\environment.log" echo LEAN_EXE=%AIM939_LEAN_EXE%
>>"%AIM939_EVIDENCE%\environment.log" echo CACHE_ROOT=%AIM939_CACHE_ROOT%
>>"%AIM939_EVIDENCE%\environment.log" echo LEAN_PATH=%LEAN_PATH%
>>"%AIM939_EVIDENCE%\environment.log" echo THREADS=%AIM939_THREADS%
>>"%AIM939_EVIDENCE%\environment.log" echo SOURCE_API_REFERENCE_MATHLIB=db584cd6d46c92f209a44c0f1c829460d327499d

type nul >"%AIM939_EVIDENCE%\run-build.log"
call :build "AIM939\Core.lean" "AIM939\Core.olean"
if errorlevel 1 goto failed
call :build "AIM939\Diagonal.lean" "AIM939\Diagonal.olean"
if errorlevel 1 goto failed
call :build "AIM939\FiniteWitness.lean" "AIM939\FiniteWitness.olean"
if errorlevel 1 goto failed
call :build "AIM939_COUNTEREXAMPLE.lean" "AIM939_COUNTEREXAMPLE.olean"
if errorlevel 1 goto failed

echo STAGE=THEOREM_AXIOM_AUDIT
"%AIM939_LEAN_EXE%" -j %AIM939_THREADS% "Audit.lean" >"%AIM939_EVIDENCE%\run-audit.log" 2>&1
if errorlevel 1 goto failed
findstr /L /C:"AIM939_THEOREM_AUDIT=PASS_STANDARD_ONLY" "%AIM939_EVIDENCE%\run-audit.log" >nul
if errorlevel 1 (
  echo ERROR=EXPECTED_AUDIT_MARKER_MISSING
  goto failed
)
type "%AIM939_EVIDENCE%\run-audit.log"

>"%AIM939_EVIDENCE%\result.txt" echo PACKAGE=%AIM939_PACKAGE%
>>"%AIM939_EVIDENCE%\result.txt" echo SOURCE_HASH_CHECK=PASS
>>"%AIM939_EVIDENCE%\result.txt" echo NATIVE_COMPILER=LEAN_4.33.0
>>"%AIM939_EVIDENCE%\result.txt" echo COMPILE_PASS=ALL_FOUR_PROOF_MODULES
>>"%AIM939_EVIDENCE%\result.txt" echo ROOT_THEOREM=AIM939.AIM939_COUNTEREXAMPLE
>>"%AIM939_EVIDENCE%\result.txt" echo ROOT_SCOPE=NEGATION_OF_ORIGINAL_DIAGONAL_CONCAVITY_IMPLICATION_AT_N_EQ_P_EQ_4
>>"%AIM939_EVIDENCE%\result.txt" echo AXIOM_AUDIT=PASS_STANDARD_ONLY
>>"%AIM939_EVIDENCE%\result.txt" echo AIM_REPOSITORY_LINUX_VERIFIER=NOT_RUN
echo AIM939_NATIVE_RESULT=PASS
echo EVIDENCE="%AIM939_EVIDENCE%"
exit /b 0

:add_cache
if exist "%~1" set "LEAN_PATH=%LEAN_PATH%;%~1"
exit /b 0

:check_hash
if not exist "%~1" (
  echo ERROR=SOURCE_FILE_MISSING:%~1
  exit /b 1
)
certutil -hashfile "%~1" SHA256 >"%AIM939_EVIDENCE%\hash-current.tmp" 2>&1
if errorlevel 1 exit /b 1
findstr /I /L /C:"%~2" "%AIM939_EVIDENCE%\hash-current.tmp" >nul
if errorlevel 1 (
  echo ERROR=SOURCE_HASH_MISMATCH:%~1
  type "%AIM939_EVIDENCE%\hash-current.tmp"
  exit /b 1
)
>>"%AIM939_EVIDENCE%\source-hashes.log" echo SOURCE_SHA256_PASS=%~1 %~2
exit /b 0

:build
echo STAGE=COMPILE:%~1
>>"%AIM939_EVIDENCE%\run-build.log" echo STAGE=COMPILE:%~1
"%AIM939_LEAN_EXE%" -j %AIM939_THREADS% -o "%AIM939_BUILD%\%~2" "%~1" >>"%AIM939_EVIDENCE%\run-build.log" 2>&1
if errorlevel 1 exit /b 1
echo COMPILE_PASS=%~1
>>"%AIM939_EVIDENCE%\run-build.log" echo COMPILE_PASS=%~1
exit /b 0

:failed
echo AIM939_NATIVE_RESULT=FAIL
if exist "%AIM939_EVIDENCE%\run-build.log" type "%AIM939_EVIDENCE%\run-build.log"
if exist "%AIM939_EVIDENCE%\run-audit.log" type "%AIM939_EVIDENCE%\run-audit.log"
echo EVIDENCE="%AIM939_EVIDENCE%"
exit /b 1
