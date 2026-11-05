@echo off
setlocal EnableExtensions DisableDelayedExpansion
if /i "%~1"=="/keep" goto keep_console
set "ROOT=%~dp0"
set "CACHE=%ROOT%cache"
if defined FEF_CACHE_DIR set "CACHE=%FEF_CACHE_DIR%"
set "PRIORCACHE="
set "SIBLINGA=%ROOT%..\COND_FEFF_A_OBSTRUCT\cache"
set "SIBLINGA1=%ROOT%..\COND_FEFF_A_OBSTRUCT_FIX1\cache"
set "SIBLINGA2=%ROOT%..\COND_FEFF_A_OBSTRUCT_FIX2\cache"
set "MODLIST=%ROOT%modules.txt"
set "TARGETS=%ROOT%audit-targets.txt"
set "TOP=CondFeffB.COND_FEFF_B_OBSTRUCT"
set "STAGE=setup"
set "PUSHED="
set "LEAN_SYSROOT="
set "LEAN_SRC_PATH="
set "LEAN_NUM_THREADS=8"
set "VERSION=COND_FEFF_B_OBSTRUCT_433_FIX5"
set "EXPLICIT_MATH=%MATHLIB_LEAN%"
if defined FEF_MATHLIB set "EXPLICIT_MATH=%FEF_MATHLIB%"
set "REUSE="
if not defined ELAN_HOME set "ELAN_HOME=%USERPROFILE%\.elan"
if not defined LEAN_EXE set "LEAN_EXE=%ELAN_HOME%\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
:options
if "%~1"=="" goto setup
if /i "%~1"=="/reuse" goto reuse_arg
if /i "%~1"=="/mathlib" goto math_arg
echo USAGE=run.cmd [/reuse PRIOR_COND_EVIDENCE] [/mathlib NATIVE_MATHLIB_DIRECTORY]
exit /b 2
:reuse_arg
if "%~2"=="" exit /b 2
set "REUSE=%~f2"
shift
shift
goto options
:math_arg
if "%~2"=="" exit /b 2
set "EXPLICIT_MATH=%~f2"
shift
shift
goto options
:setup
if not exist "%ROOT%evidence" mkdir "%ROOT%evidence"
if not exist "%ROOT%evidence" exit /b 2
:new_evidence
set "RUNID=r-%RANDOM%-%RANDOM%-%RANDOM%"
set "EV=%ROOT%evidence\%RUNID%"
if exist "%EV%" goto new_evidence
mkdir "%EV%" || exit /b 2
mkdir "%EV%\src" || goto fail
echo EVIDENCE="%EV%"
echo MODE=NATIVE_CMD_OFFLINE_CACHED
if defined REUSE if not exist "%REUSE%\cache-root.txt" call :selectPriorEvidence
if defined REUSE echo REUSE_EVIDENCE="%REUSE%"
if defined REUSE (
  if not exist "%REUSE%\cache-root.txt" goto fail
  set /p "PRIORCACHE="<"%REUSE%\cache-root.txt"
  if not defined EXPLICIT_MATH if exist "%REUSE%\mathlib-root.txt" set /p "EXPLICIT_MATH="<"%REUSE%\mathlib-root.txt"
)
if not exist "%LEAN_EXE%" goto fail
for %%D in ("%LEAN_EXE%") do set "LEAN_BIN=%%~dpD"
for %%D in ("%LEAN_EXE%") do set "CHECKER=%%~dpDleanchecker.exe"
for %%D in ("%LEAN_BIN%..\lib\lean") do set "STANDARD=%%~fD"
if not exist "%STANDARD%\Init.olean" goto fail
if not exist "%ROOT%Audit.lean" goto fail
if not exist "%ROOT%tools\CheckAxioms.lean" goto fail
if not exist "%MODLIST%" goto fail
if not exist "%TARGETS%" goto fail
findstr /x /l /c:"%TOP%" "%TARGETS%" >nul || goto fail
findstr /x /l /c:"COND_FEFF_B_OBSTRUCT" "%MODLIST%" >nul || goto fail
if not exist "%CACHE%\index" mkdir "%CACHE%\index"
if not exist "%CACHE%\index" goto fail
if not exist "%CACHE%\objects" mkdir "%CACHE%\objects"
if not exist "%CACHE%\objects" goto fail
set "STAGE=compiler"
"%LEAN_EXE%" --version >"%EV%\lean-version.log" 2>&1 || goto fail
type "%EV%\lean-version.log"
findstr /l /c:"version 4.33.0, x86_64-w64-windows-gnu," "%EV%\lean-version.log" >nul || goto fail
pushd "%EV%\src" || goto fail
set "PUSHED=1"
>MathlibProbe.lean echo import Mathlib
set "ML="
set "STAGE=mathlib_cache"
if defined EXPLICIT_MATH (
  call :tryMath "%EXPLICIT_MATH%"
  goto math_selected
)
call :tryMath "%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1"
if not defined ML if exist "%USERPROFILE%\lean-native" for /f "delims=" %%F in ('where /r "%USERPROFILE%\lean-native" Mathlib.olean 2^>nul') do if not defined ML call :tryMath "%%~dpF."
if not defined ML if exist "%USERPROFILE%\Downloads" for /f "delims=" %%F in ('where /r "%USERPROFILE%\Downloads" Mathlib.olean 2^>nul') do if not defined ML call :tryMath "%%~dpF."
:math_selected
if not defined ML (
  echo EXPECTED=Prebuilt Mathlib for native Lean 4.33.0. Set MATHLIB_LEAN or use /mathlib.
  goto fail
)
> "%EV%\mathlib-root.txt" <nul set /p "=%ML%"
>>"%EV%\mathlib-root.txt" echo(
> "%EV%\cache-root.txt" <nul set /p "=%CACHE%"
>>"%EV%\cache-root.txt" echo(
echo MATHLIB="%ML%"
set "STAGE=cache_identity"
echo VERIFY_NATIVE_CACHE_INPUTS=START
copy /y "%EV%\lean-version.log" "%EV%\identity.txt" >nul || goto fail
>>"%EV%\identity.txt" echo SCHEMA=4
>>"%EV%\identity.txt" echo FLAGS=lean -j8 -o,LEAN_NUM_THREADS=8
call :identityFile "%LEAN_EXE%" || goto fail
call :identityFile "%ML%\Mathlib.olean" || goto fail
if exist "%MREPO%\lean-toolchain" call :identityFile "%MREPO%\lean-toolchain" || goto fail
if exist "%MREPO%\lake-manifest.json" call :identityFile "%MREPO%\lake-manifest.json" || goto fail
set "GIT_HASH="
where git.exe >nul 2>&1
if not errorlevel 1 set "GIT_HASH=1"
for /f "usebackq delims=" %%L in ("%EV%\native-paths.txt") do (
  call :identityTree "%%L"
  if errorlevel 1 goto fail
)
call :hash "%EV%\identity.txt" || goto fail
set "LEGACYKEY=%HEX%"
copy /b /y "%EV%\identity.txt" "%EV%\legacy-environment.txt" >nul || goto fail
>>"%EV%\identity.txt" echo STRICT_SCHEMA=PERIODIC_B_1
call :identityTree "%STANDARD%" || goto fail
call :moreObjects "%STANDARD%" || goto fail
for /f "usebackq delims=" %%L in ("%EV%\native-paths.txt") do (
  call :moreObjects "%%L"
  if errorlevel 1 goto fail
)
for %%D in ("%LEAN_BIN%*.dll") do if exist "%%~fD" (
  call :identityFile "%%~fD"
  if errorlevel 1 goto fail
)
call :hash "%EV%\identity.txt" || goto fail
set "BASEKEY=%HEX%"
rem Lean resolves a namespace from one search root. Put every local module
rem in the same run-scoped tree while keeping cache object directories immutable.
set "IMPORT_ROOT=%EV%\lib"
mkdir "%IMPORT_ROOT%" || goto fail
set "ORD=0"
set "BUILD_FAILED="
for /f "usebackq delims=" %%M in ("%MODLIST%") do (
  call :compileModule "%%M"
  if errorlevel 1 (
    set "BUILD_FAILED=1"
    echo MODULE_FAILED_OR_BLOCKED=%%M
    >>"%EV%\failed-modules.txt" echo %%M
  )
)
if defined BUILD_FAILED (
  set "STAGE=see_failed-modules.txt"
  goto fail
)
if not exist "%EV%\COND_FEFF_B_OBSTRUCT.dep" goto fail
set "STAGE=fresh_signature_check"
copy /b /y "%ROOT%Audit.lean" Audit.lean >nul || goto fail
set "LEAN_PATH=%IMPORT_ROOT%;%NATIVE_PATHS%"
"%LEAN_EXE%" -j8 -o "%IMPORT_ROOT%\Audit.olean" Audit.lean >"%EV%\signature.log" 2>&1
if errorlevel 1 (
  type "%EV%\signature.log"
  goto fail
)
findstr /l /c:"declaration uses 'sorry'" "%EV%\signature.log" >nul && goto fail
set "STAGE=fresh_axiom_audit"
call :hash "%ROOT%tools\CheckAxioms.lean" || goto fail
if /i not "%HEX%"=="637a74dafaa06140773a14dcc5cc703a91c9ec717643d4c12d043805f9413b8b" goto fail
copy /b /y "%ROOT%tools\CheckAxioms.lean" FreshAudit.lean >nul || goto fail
>>FreshAudit.lean echo.
for /f "usebackq delims=" %%T in ("%TARGETS%") do (
  >>FreshAudit.lean echo #print axioms %%T
  >>FreshAudit.lean echo assert_standard_axioms %%T
)
"%LEAN_EXE%" -j8 FreshAudit.lean >"%EV%\audit.log" 2>&1
if errorlevel 1 (
  type "%EV%\audit.log"
  goto fail
)
set "COUNT=0"
for /f "usebackq delims=" %%T in ("%TARGETS%") do (
  call :checkAudit "%%T"
  if errorlevel 1 goto fail
)
if %COUNT%==0 goto fail
type "%EV%\audit.log"
>"%EV%\result.tmp" echo RUN=PASS
>>"%EV%\result.tmp" echo LEAN=4.33.0
>>"%EV%\result.tmp" echo THEOREM=%TOP%
>>"%EV%\result.tmp" echo THEOREM_AXIOM_AUDITS=%COUNT%
>>"%EV%\result.tmp" echo THEOREM_AXIOM_AUDIT=STANDARD_ONLY
>>"%EV%\result.tmp" echo SCOPE=V0_25_0_ANALYTIC_PERIODIC_B
move /y "%EV%\result.tmp" "%EV%\result.txt" >nul || goto fail
type "%EV%\result.txt"
echo GOODWORKFLOWFRONTIER::%VERSION%::FINAL=ANALYTIC_PERIODIC_OBSTRUCTION_AUDITED
popd
exit /b 0

:keep_console
call "%~f0" %2 %3 %4 %5 %6 %7 %8 %9
set "SAVED_RC=%ERRORLEVEL%"
pause
exit /b %SAVED_RC%

:selectPriorEvidence
rem /reuse accepts one run or its parent evidence directory. Only consider
rem directories with completed results and installed module dependency receipts.
set "EVIDENCE_PARENT=%REUSE%"
if not exist "%EVIDENCE_PARENT%\." exit /b 0
for /f "delims=" %%D in ('dir /b /a:d /o:-d /t:c "%EVIDENCE_PARENT%\r-*" 2^>nul') do (
  if exist "%EVIDENCE_PARENT%\%%D\result.txt" if exist "%EVIDENCE_PARENT%\%%D\cache-root.txt" if exist "%EVIDENCE_PARENT%\%%D\ConcreteABCDUnifiedClosure.dep" if exist "%EVIDENCE_PARENT%\%%D\lib\ConcreteABCDUnifiedClosure.olean" (
    set "REUSE=%EVIDENCE_PARENT%\%%D"
    exit /b 0
  )
)
exit /b 0

:tryMath
set "CAND="
if exist "%~1\Mathlib.olean" for %%D in ("%~1") do set "CAND=%%~fD"
if not defined CAND if exist "%~1\.lake\packages\mathlib\.lake\build\lib\lean\Mathlib.olean" for %%D in ("%~1\.lake\packages\mathlib\.lake\build\lib\lean") do set "CAND=%%~fD"
if not defined CAND if exist "%~1\.lake\build\lib\lean\Mathlib.olean" for %%D in ("%~1\.lake\build\lib\lean") do set "CAND=%%~fD"
if not defined CAND exit /b 0
for %%D in ("%CAND%\..\..\..\..") do set "MREPO=%%~fD"
if exist "%MREPO%\lean-toolchain" (
  findstr /l /x /c:"leanprover/lean4:v4.33.0" "%MREPO%\lean-toolchain" >nul
  if errorlevel 1 exit /b 0
)
set "NATIVE_PATHS=%CAND%"
> "%EV%\native-paths.txt" <nul set /p "=%CAND%"
>>"%EV%\native-paths.txt" echo(
if exist "%MREPO%\.lake\packages" for /d %%P in ("%MREPO%\.lake\packages\*") do call :appendLib "%%~fP\.lake\build\lib\lean"
for %%D in ("%MREPO%\..") do set "MREPOPARENT=%%~fD"
for %%D in ("%MREPOPARENT%") do if /i "%%~nxD"=="packages" for /d %%P in ("%%~fD\*") do call :appendLib "%%~fP\.lake\build\lib\lean"
set "LEAN_PATH=%NATIVE_PATHS%"
"%LEAN_EXE%" MathlibProbe.lean >"%EV%\mathlib-probe.log" 2>&1
if errorlevel 1 exit /b 0
set "ML=%CAND%"
exit /b 0

:appendLib
if not exist "%~1\." exit /b 0
if /i "%~f1"=="%CAND%" exit /b 0
set "NATIVE_PATHS=%NATIVE_PATHS%;%~f1"
>>"%EV%\native-paths.txt" <nul set /p "=%~f1"
>>"%EV%\native-paths.txt" echo(
exit /b 0

:identityFile
call :hash "%~1" || exit /b 1
>>"%EV%\identity.txt" echo HASH %HEX% "%~1"
exit /b 0

:identityTree
>>"%EV%\identity.txt" echo NATIVE_LIB "%~1"
rem Verify exact native module bytes, also when two cache checkouts have the same name.
rem Git, if installed, hashes all streams in one process without modifying any repository.
dir /s /b /o:n /a:-d "%~1\*.olean*" >"%EV%\native-files.tmp" 2>nul
for %%Z in ("%EV%\native-files.tmp") do if %%~zZ==0 exit /b 0
call :hash "%EV%\native-files.tmp" || exit /b 1
>>"%EV%\identity.txt" echo NAMES=%HEX%
if defined GIT_HASH (
  git hash-object --no-filters --stdin-paths <"%EV%\native-files.tmp" >"%EV%\native-hashes.tmp" 2>"%EV%\git-hash.log"
  if not errorlevel 1 goto treeGit
)
rem Slow fallback for machines without Git; native CMD and certutil only.
for /f "usebackq delims=" %%F in ("%EV%\native-files.tmp") do (
  call :identityFile "%%F"
  if errorlevel 1 exit /b 1
)
exit /b 0
:treeGit
call :hash "%EV%\native-hashes.tmp" || exit /b 1
>>"%EV%\identity.txt" echo CONTENTS=%HEX%
exit /b 0

:moreObjects
>>"%EV%\identity.txt" echo RUNTIME_LIB "%~1"
dir /s /b /o:n /a:-d "%~1\*.ir" "%~1\*.ir.*" "%~1\*.dll" "%~1\*.so" "%~1\*.dylib" >"%EV%\native-files.tmp" 2>nul
for %%Z in ("%EV%\native-files.tmp") do if %%~zZ==0 exit /b 0
call :hash "%EV%\native-files.tmp" || exit /b 1
>>"%EV%\identity.txt" echo NAMES=%HEX%
if defined GIT_HASH (
  git hash-object --no-filters --stdin-paths <"%EV%\native-files.tmp" >"%EV%\native-hashes.tmp" 2>"%EV%\git-hash.log"
  if not errorlevel 1 goto treeGit
)
for /f "usebackq delims=" %%F in ("%EV%\native-files.tmp") do (
  call :identityFile "%%F"
  if errorlevel 1 exit /b 1
)
exit /b 0

:hash
set "HEX="
if not exist "%~1" exit /b 1
certutil -hashfile "%~1" SHA256 >"%EV%\hash.tmp" 2>nul || exit /b 1
for /f "tokens=* skip=1 delims=" %%H in ('type "%EV%\hash.tmp"') do if not defined HEX set "HEX=%%H"
set "HEX=%HEX: =%"
if "%HEX:~63,1%"=="" exit /b 1
if not "%HEX:~64,1%"=="" exit /b 1
exit /b 0

:compileModule
set "MOD=%~1"
set "STAGE=module_%~1"
set /a ORD+=1 >nul
set "SRC=%ROOT%%MOD%.lean"
set "BASEMOD="
if /i "%MOD%"=="Fefferman\Analysis" set "BASEMOD=1"
if /i "%MOD%"=="Fefferman\Statements" set "BASEMOD=1"
if /i "%MOD%"=="ConcreteABCDUnifiedClosure" set "BASEMOD=1"
if defined BASEMOD set "SRC=%ROOT%base\%MOD%.lean"
if not exist "%SRC%" exit /b 1
for %%D in ("%EV%\src\%MOD%.lean") do if not exist "%%~dpD" mkdir "%%~dpD"
copy /b /y "%SRC%" "%EV%\src\%MOD%.lean" >nul || exit /b 1
call :hash "%EV%\src\%MOD%.lean" || exit /b 1
if /i "%MOD%"=="ConcreteABCDUnifiedClosure" if /i not "%HEX%"=="b50becc18ace6fb2596fe2b98398363983727163bb573a5aedf6c76e6df6b706" exit /b 1
if /i "%MOD%"=="Fefferman\Analysis" if /i not "%HEX%"=="d70620b1e3035563a983351d193241b7dccdfc579af283487e811eabeaa60c24" exit /b 1
if /i "%MOD%"=="Fefferman\Statements" if /i not "%HEX%"=="e026d1b26e3e4b6fccb6d338bbfb5c1f3c6c6fb75b15750616923e80c3da287f" exit /b 1
>"%EV%\module-%ORD%.key" echo ENVIRONMENT=%BASEKEY%
>>"%EV%\module-%ORD%.key" echo MODULE=%MOD%
>>"%EV%\module-%ORD%.key" echo SOURCE=%HEX%
>"%EV%\module-%ORD%.legacykey" echo ENVIRONMENT=%LEGACYKEY%
>>"%EV%\module-%ORD%.legacykey" echo MODULE=%MOD%
>>"%EV%\module-%ORD%.legacykey" echo SOURCE=%HEX%
for /f "tokens=2" %%D in ('findstr /b /c:"import " "%EV%\src\%MOD%.lean"') do (
  call :addImport "%%D"
  if errorlevel 1 exit /b 1
)
call :hash "%EV%\module-%ORD%.key" || exit /b 1
set "CHAIN=%HEX%"
set "INDEX=%CACHE%\index\%CHAIN%.txt"
set "OBJ="
call :hash "%EV%\module-%ORD%.legacykey" || exit /b 1
set "LEGACYCHAIN=%HEX%"
set "FOUND="
set "EVIDENCE_RECEIPT="
call :tryStrict "%CACHE%"
if not defined FOUND if defined PRIORCACHE call :tryStrict "%PRIORCACHE%"
if not defined FOUND if defined REUSE call :tryEvidence
if defined FOUND goto moduleReady
if defined BASEMOD if exist "%CHECKER%" (
  if defined PRIORCACHE call :tryLegacy "%PRIORCACHE%"
  if not defined FOUND call :tryLegacy "%SIBLINGA%"
  if not defined FOUND call :tryLegacy "%SIBLINGA1%"
  if not defined FOUND call :tryLegacy "%SIBLINGA2%"
)
if defined FOUND goto promoteLegacy
goto buildModule

:tryStrict
set "OBJ="
if not exist "%~1\index\%CHAIN%.txt" exit /b 0
set /p "OBJ="<"%~1\index\%CHAIN%.txt"
if not defined OBJ exit /b 0
if not exist "%OBJ%\receipt.txt" exit /b 0
call :receipt "%EV%\receipt-%ORD%.txt" || exit /b 0
fc /b "%EV%\receipt-%ORD%.txt" "%OBJ%\receipt.txt" >nul || exit /b 0
set "FOUND=1"
echo GOODWORKFLOWFRONTIER::%VERSION%::CACHE_HIT_%ORD%=%MOD%
exit /b 0

:tryEvidence
rem A previous run can include verified modules it imported from another cache.
rem Compare its module dependency record with a receipt regenerated from its lib tree.
set "EVMODNAME=%MOD:\=.%"
if not exist "%REUSE%\%EVMODNAME%.dep" exit /b 0
set "OBJ=%REUSE%\lib"
call :receipt "%EV%\prior-%ORD%.receipt" || exit /b 0
call :hash "%EV%\prior-%ORD%.receipt" || exit /b 0
>"%EV%\prior-%ORD%.dep" echo %CHAIN% %HEX%
fc /b "%EV%\prior-%ORD%.dep" "%REUSE%\%EVMODNAME%.dep" >nul || exit /b 0
set "FOUND=1"
set "EVIDENCE_RECEIPT=%EV%\prior-%ORD%.receipt"
echo GOODWORKFLOWFRONTIER::%VERSION%::EVIDENCE_HIT_%ORD%=%MOD%
exit /b 0

:tryLegacy
set "OBJ="
if not exist "%~1\index\%LEGACYCHAIN%.txt" exit /b 0
set /p "OBJ="<"%~1\index\%LEGACYCHAIN%.txt"
if not defined OBJ exit /b 0
if not exist "%OBJ%\receipt.txt" exit /b 0
set "STRICTCHAIN=%CHAIN%"
set "CHAIN=%LEGACYCHAIN%"
call :receipt "%EV%\compat-receipt.txt"
set "MATCHRC=%ERRORLEVEL%"
set "CHAIN=%STRICTCHAIN%"
if not "%MATCHRC%"=="0" exit /b 0
fc /b "%EV%\compat-receipt.txt" "%OBJ%\receipt.txt" >nul || exit /b 0
for %%D in ("%IMPORT_ROOT%\%MOD%.olean") do if not exist "%%~dpD" mkdir "%%~dpD"
for %%S in (olean.private olean.server ir olean) do if exist "%OBJ%\%MOD%.%%S" (
  call :installSidecar "%%S"
  if errorlevel 1 goto legacyRejected
)
set "MODNAME=%MOD:\=.%"
set "LEAN_PATH=%IMPORT_ROOT%;%NATIVE_PATHS%"
"%CHECKER%" "%MODNAME%" >"%EV%\replay-%ORD%.log" 2>&1
if errorlevel 1 goto legacyRejected
set "FOUND=1"
set "OLDOBJ=%OBJ%"
echo VERIFIED_BASE_REPLAY=%MOD%
:legacyRejected
for %%S in (olean.private olean.server ir olean) do if exist "%IMPORT_ROOT%\%MOD%.%%S" del /q "%IMPORT_ROOT%\%MOD%.%%S"
exit /b 0

:promoteLegacy
set "OBJ=%CACHE%\objects\%RUNID%-%ORD%"
if exist "%OBJ%" exit /b 1
for %%D in ("%OBJ%\%MOD%.olean") do mkdir "%%~dpD" || exit /b 1
for %%S in (olean.private olean.server ir olean) do if exist "%OLDOBJ%\%MOD%.%%S" (
  copy /b /y "%OLDOBJ%\%MOD%.%%S" "%OBJ%\%MOD%.%%S" >nul || exit /b 1
  fc /b "%OLDOBJ%\%MOD%.%%S" "%OBJ%\%MOD%.%%S" >nul || exit /b 1
)
goto sealModule

:buildModule
set "OBJ=%CACHE%\objects\%RUNID%-%ORD%"
if exist "%OBJ%" exit /b 1
for %%D in ("%OBJ%\%MOD%.olean") do mkdir "%%~dpD" || exit /b 1
set "LEAN_PATH=%IMPORT_ROOT%;%NATIVE_PATHS%"
echo GOODWORKFLOWFRONTIER::%VERSION%::COMPILE_%ORD%=%MOD%
"%LEAN_EXE%" -j8 -o "%OBJ%\%MOD%.olean" "%MOD%.lean" >"%EV%\module-%ORD%.log" 2>&1
if errorlevel 1 (
  type "%EV%\module-%ORD%.log"
  exit /b 1
)
findstr /l /c:"declaration uses 'sorry'" "%EV%\module-%ORD%.log" >nul && exit /b 1
:sealModule
call :receipt "%OBJ%\receipt.txt" || exit /b 1
> "%CACHE%\index\%RUNID%-%ORD%.tmp" <nul set /p "=%OBJ%"
>>"%CACHE%\index\%RUNID%-%ORD%.tmp" echo(
move /y "%CACHE%\index\%RUNID%-%ORD%.tmp" "%INDEX%" >nul || exit /b 1
:moduleReady
set "STAGE=install_%MOD%"
for %%D in ("%IMPORT_ROOT%\%MOD%.olean") do if not exist "%%~dpD" mkdir "%%~dpD"
if not exist "%OBJ%\%MOD%.olean" exit /b 1
rem Publish the primary olean last. A dependent becomes eligible only after
rem all copies were byte-checked and the dependency marker was published.
for %%S in (olean.private olean.server ir olean) do (
  if exist "%OBJ%\%MOD%.%%S" (
    call :installSidecar "%%S"
    if errorlevel 1 exit /b 1
  )
)
set "MODNAME=%MOD:\=.%"
set "SOURCE_RECEIPT=%OBJ%\receipt.txt"
if defined EVIDENCE_RECEIPT set "SOURCE_RECEIPT=%EVIDENCE_RECEIPT%"
set "OBJ=%IMPORT_ROOT%"
call :receipt "%EV%\installed-%ORD%.receipt" || exit /b 1
fc /b "%EV%\installed-%ORD%.receipt" "%SOURCE_RECEIPT%" >nul || exit /b 1
call :hash "%EV%\installed-%ORD%.receipt" || exit /b 1
>"%EV%\%MODNAME%.dep.tmp" echo %CHAIN% %HEX%
move /y "%EV%\%MODNAME%.dep.tmp" "%EV%\%MODNAME%.dep" >nul || exit /b 1
if not defined BASEMOD exit /b 0
set "STRICTCHAIN=%CHAIN%"
set "CHAIN=%LEGACYCHAIN%"
call :receipt "%EV%\compat-receipt.txt" || exit /b 1
call :hash "%EV%\compat-receipt.txt" || exit /b 1
>"%EV%\%MODNAME%.compat.dep" echo %LEGACYCHAIN% %HEX%
set "CHAIN=%STRICTCHAIN%"
exit /b 0

:installSidecar
set "FROM_FILE=%OBJ%\%MOD%.%~1"
set "TO_FILE=%IMPORT_ROOT%\%MOD%.%~1"
if exist "%TO_FILE%" exit /b 1
copy /b /y "%FROM_FILE%" "%TO_FILE%.tmp" >nul || exit /b 1
fc /b "%FROM_FILE%" "%TO_FILE%.tmp" >nul || exit /b 1
move /y "%TO_FILE%.tmp" "%TO_FILE%" >nul || exit /b 1
exit /b 0

:addImport
set "DEP=%~1"
set "DEP_SRC=%DEP:.=\%"
if not exist "%ROOT%%DEP_SRC%.lean" if not exist "%ROOT%base\%DEP_SRC%.lean" exit /b 0
if not exist "%EV%\%DEP%.dep" exit /b 1
if defined BASEMOD (
  if not exist "%EV%\%DEP%.compat.dep" exit /b 1
  >>"%EV%\module-%ORD%.legacykey" echo IMPORT=%DEP%
  type "%EV%\%DEP%.compat.dep" >>"%EV%\module-%ORD%.legacykey"
)
>>"%EV%\module-%ORD%.key" echo IMPORT=%DEP%
type "%EV%\%DEP%.dep" >>"%EV%\module-%ORD%.key"
exit /b 0

:receipt
if not exist "%OBJ%\%MOD%.olean" exit /b 1
>"%~1" echo KEY=%CHAIN%
>>"%~1" echo NATIVE_MODULE_BUILD=PASS
for %%S in (olean olean.private olean.server ir) do (
  if exist "%OBJ%\%MOD%.%%S" (
    call :stampSidecar "%%S" "%~1"
    if errorlevel 1 exit /b 1
  )
)
exit /b 0

:stampSidecar
call :hash "%OBJ%\%MOD%.%~1" || exit /b 1
>>"%~2" echo %~1=%HEX%
exit /b 0

:checkAudit
if exist "%EV%\%~1.audit-ok" exit /b 1
findstr /l /c:"AXIOM_AUDIT_PASS=[%~1]" "%EV%\audit.log" >nul || exit /b 1
>"%EV%\%~1.audit-ok" echo PASS
set /a COUNT+=1 >nul
exit /b 0

:fail
echo RUN=FAIL
echo STAGE=%STAGE%
if defined EV (
  >"%EV%\result.txt" echo RUN=FAIL
  >>"%EV%\result.txt" echo STAGE=%STAGE%
  echo EVIDENCE="%EV%"
)
if defined PUSHED popd
exit /b 1
