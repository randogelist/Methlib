@echo off
setlocal EnableExtensions DisableDelayedExpansion
set "ROOT=%~dp0"
set "CACHE=%ROOT%cache"
set "MODLIST=%ROOT%modules.txt"
set "TARGETS=%ROOT%audit-targets.txt"
set "TOP=CondFeffA.Literature.WJI_LITERATURE_CONDITIONAL_CLOSURE"
set "TOPMODULE=WJI_LITERATURE_CONDITIONAL_CLOSURE"
set "READ_CACHES="
set "STAGE=setup"
set "PUSHED="
set "LEAN_SYSROOT="
set "LEAN_SRC_PATH="
set "LEAN_NUM_THREADS=8"
set "VERSION=WJI_LITERATURE_CONDITIONAL_433"
set "EXPLICIT_MATH=%MATHLIB_LEAN%"
set "REUSE="
set "INFERRED_MATH="
if not defined LEAN_EXE set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
:options
if "%~1"=="" goto setup
if /i "%~1"=="/reuse" goto reuse_arg
if /i "%~1"=="/mathlib" goto math_arg
echo USAGE=run.cmd [/reuse PRIOR_EVIDENCE] [/mathlib NATIVE_MATHLIB_DIRECTORY]
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
set "STAGE=cache_selection"
set "READ_CACHES=%EV%\read-cache-roots.txt"
type nul >"%READ_CACHES%" || goto fail
if defined REUSE (
  call :useEvidence "%REUSE%"
  if errorlevel 1 (
    echo INVALID_REUSE_EVIDENCE="%REUSE%"
    goto fail
  )
)
rem Both sibling branches can contribute verified objects. All writes remain local.
call :discoverCaches "%ROOT%.."
call :discoverCaches "%USERPROFILE%\Downloads"
for /f "usebackq delims=" %%C in ("%READ_CACHES%") do echo READ_ONLY_CACHE="%%C"
if not exist "%LEAN_EXE%" goto fail
set "STAGE=manifest_validation"
call :snapshot "modules.txt" "80f4937f3e1ddc558a8e5daba520cf87ccaa7f14c360b49b6a5c2c508be8eed1" || goto fail
call :snapshot "audit-targets.txt" "eea596e9da42249c8152206f13602ff36ab188494b64b7ea81cc71a4f3a14cff" || goto fail
call :snapshot "source-pins.txt" "d7f04b3b409725e87c37a5a87c78a789341f57410fc7794c8ce6978e1b5a0f81" || goto fail
set "MODLIST=%EV%\modules.txt"
set "TARGETS=%EV%\audit-targets.txt"
set "SOURCE_PINS=%EV%\source-pins.txt"
findstr /x /l /c:"%TOP%" "%TARGETS%" >nul || goto fail
findstr /x /l /c:"%TOPMODULE%" "%MODLIST%" >nul || goto fail
if not exist "%CACHE%\index" mkdir "%CACHE%\index"
if not exist "%CACHE%\index" goto fail
if not exist "%CACHE%\objects" mkdir "%CACHE%\objects"
if not exist "%CACHE%\objects" goto fail
set "STAGE=compiler"
"%LEAN_EXE%" --version >"%EV%\lean-version.log" 2>&1 || goto fail
type "%EV%\lean-version.log"
findstr /l /c:"version 4.33.0," "%EV%\lean-version.log" >nul || goto fail
pushd "%EV%\src" || goto fail
set "PUSHED=1"
>MathlibProbe.lean echo import Mathlib
set "ML="
set "STAGE=mathlib_cache"
if defined EXPLICIT_MATH (
  call :tryMath "%EXPLICIT_MATH%"
  goto math_selected
)
if defined INFERRED_MATH call :tryMath "%INFERRED_MATH%"
if defined ML goto math_selected
if exist "%USERPROFILE%\lean-native" for /f "delims=" %%F in ('where /r "%USERPROFILE%\lean-native" Mathlib.olean 2^>nul') do if not defined ML call :tryMath "%%~dpF."
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
if exist "%EV%\%TOPMODULE%.dep" (
  call :auditRoot
  if errorlevel 1 goto fail
)
if defined BUILD_FAILED (
  set "STAGE=see_failed-modules.txt"
  goto fail
)
if not exist "%EV%\root-result.txt" (
  set "STAGE=root_audit_missing"
  goto fail
)
set "STAGE=package_audit_prepare"
call :auditHeader "FreshAudit.lean" "ALL_MODULES" || goto fail
for /f "usebackq delims=" %%T in ("%TARGETS%") do (
  >>FreshAudit.lean echo #check %%T
  >>FreshAudit.lean echo #print axioms %%T
  >>FreshAudit.lean echo assert_standard_axioms %%T
)
set "STAGE=package_audit_lean"
call :runAudit "FreshAudit.lean" "%EV%\audit.log" || goto fail
set "STAGE=package_audit_receipts"
for /f "usebackq delims=" %%T in ("%TARGETS%") do (
  call :checkAudit "%%T" "%EV%\audit.log"
  if errorlevel 1 goto fail
)
> "%EV%\result.txt" echo RUN=PASS
>>"%EV%\result.txt" echo LEAN=4.33.0
>>"%EV%\result.txt" echo THEOREM=%TOP%
>>"%EV%\result.txt" echo THEOREM_AXIOM_AUDIT=STANDARD_ONLY
>>"%EV%\result.txt" echo SCOPE=CONDITIONAL_ON_EXPLICIT_LITERATURE_COROLLARY
>>"%EV%\result.txt" echo AMPLITUDE_INTERVAL=ZERO_LT_C_LT_ONE
>>"%EV%\result.txt" echo OPEN_INPUT=CondFeffA.Literature.LiteratureSchwartzSlabRegularity
>>"%EV%\result.txt" echo FULL_PREMISE_FREE_ROOT=OPEN
>>"%EV%\result.txt" echo JET_ORDERS=ALL_NATURAL_NUMBERS
>>"%EV%\result.txt" echo LITERATURE_INPUT=UNFORMALIZED_EXPLICIT_HYPOTHESIS
>>"%EV%\result.txt" echo UNCONDITIONAL_CLOSURE=OPEN
type "%EV%\result.txt"
echo GOODWORKFLOWFRONTIER::%VERSION%::FINAL=CONDITIONAL_THEOREM_AUDITED
popd
exit /b 0

:auditRoot
set "STAGE=root_audit_prepare"
call :auditHeader "RootAudit.lean" "%TOPMODULE%" || exit /b 1
>>RootAudit.lean echo #print CondFeffA.Literature.LiteratureSchwartzSlabRegularity
>>RootAudit.lean echo #check %TOP%
>>RootAudit.lean echo #print axioms %TOP%
>>RootAudit.lean echo assert_standard_axioms %TOP%
set "STAGE=root_audit_lean"
call :runAudit "RootAudit.lean" "%EV%\root-audit.log" || exit /b 1
set "STAGE=root_audit_receipt"
call :checkAudit "%TOP%" "%EV%\root-audit.log" || exit /b 1
copy /b /y "%EV%\root-audit.log" "%EV%\audit.log" >nul || exit /b 1
>"%EV%\root-result.txt" echo EXACT_ROOT=PASS
>>"%EV%\root-result.txt" echo THEOREM=%TOP%
>>"%EV%\root-result.txt" echo SCOPE=CONDITIONAL_ON_EXPLICIT_LITERATURE_COROLLARY
>>"%EV%\root-result.txt" echo AXIOM_AUDIT=STANDARD_ONLY
>>"%EV%\root-result.txt" echo LITERATURE_INPUT=UNFORMALIZED_EXPLICIT_HYPOTHESIS
>>"%EV%\root-result.txt" echo UNCONDITIONAL_CLOSURE=OPEN
type "%EV%\root-result.txt"
exit /b 0

:auditHeader
if not exist "%EV%\audit-header.lean" (
  copy /b /y "%ROOT%deps\tools\CheckAxioms.lean" "%EV%\audit-header.lean" >nul || exit /b 1
)
call :hash "%EV%\audit-header.lean" || exit /b 1
if /i not "%HEX%"=="60683e8a88af47ff71ccfb8ae16bf9518cc61ae0906b58a23f802a898f9e33d0" (
  echo AUDIT_CHECKER_HASH_MISMATCH
  exit /b 1
)
if /i "%~2"=="ALL_MODULES" (
  type nul >"%~1" || exit /b 1
  for /f "usebackq delims=" %%M in ("%MODLIST%") do (
    call :writeImport "%~1" "%%M"
    if errorlevel 1 exit /b 1
  )
) else (
  >"%~1" echo import %~2|| exit /b 1
)
type "%EV%\audit-header.lean" >>"%~1" || exit /b 1
exit /b 0

:writeImport
set "IMPORT_NAME=%~2"
>>"%~1" echo import %IMPORT_NAME:\=.%|| exit /b 1
exit /b 0

:snapshot
copy /b /y "%ROOT%deps\%~1" "%EV%\%~1" >nul || exit /b 1
call :hash "%EV%\%~1" || exit /b 1
if /i not "%HEX%"=="%~2" (
  echo MANIFEST_HASH_MISMATCH=%~1
  exit /b 1
)
exit /b 0

:useEvidence
if not exist "%~1\cache-root.txt" exit /b 1
set "PRIOR_CACHE="
set /p "PRIOR_CACHE="<"%~1\cache-root.txt"
if not defined PRIOR_CACHE exit /b 1
if not exist "%PRIOR_CACHE%\index\." exit /b 1
call :addReadCache "%PRIOR_CACHE%" || exit /b 1
if defined EXPLICIT_MATH exit /b 0
if defined INFERRED_MATH exit /b 0
if not exist "%~1\mathlib-root.txt" exit /b 0
set "PRIOR_MATH="
set /p "PRIOR_MATH="<"%~1\mathlib-root.txt"
if defined PRIOR_MATH if exist "%PRIOR_MATH%\Mathlib.olean" set "INFERRED_MATH=%PRIOR_MATH%"
exit /b 0

:addReadCache
for %%D in ("%~1") do set "NEW_READ_CACHE=%%~fD"
if not exist "%NEW_READ_CACHE%\index\." exit /b 1
if /i "%NEW_READ_CACHE%"=="%CACHE%" exit /b 0
findstr /x /l /c:"%NEW_READ_CACHE%" "%READ_CACHES%" >nul
if not errorlevel 1 exit /b 0
>>"%READ_CACHES%" <nul set /p "=%NEW_READ_CACHE%"
>>"%READ_CACHES%" echo(
exit /b 0

:discoverCaches
if not exist "%~1\." exit /b 0
for /d %%P in ("%~1\WJI_SMALL_AMPLITUDE_GEVREY_TWO_433*" "%~1\WJI_UNIFORM_MIXED_JET_BOUND_433*" "%~1\WITNESS_JET_IDENTIFICATION_ONE*" "%~1\COND_FEFF_A_OBSTRUCT*" "%~1\WJI_CROSS_BRANCH_ASSEMBLY_433*" "%~1\WJI_DIRECT_JET_ASSEMBLY_433*" "%~1\WJI_LITERATURE_CONDITIONAL_433*") do call :findBranchCaches "%%~fP"
exit /b 0

:findBranchCaches
for %%D in ("%~1") do set "BRANCH_DIR=%%~fD"
if not exist "%BRANCH_DIR%\." exit /b 0
if exist "%BRANCH_DIR%\cache\index\." call :addReadCache "%BRANCH_DIR%\cache"
if not exist "%BRANCH_DIR%\evidence\." exit /b 0
rem A failed overall run may contain individually verified successful modules.
rem Every reused object must still pass its current full key and byte receipt.
for /f "delims=" %%R in ('dir /ad /b /o:-d "%BRANCH_DIR%\evidence\r-*" 2^>nul') do call :useEvidence "%BRANCH_DIR%\evidence\%%R"
exit /b 0

:runAudit
set "LEAN_PATH=%IMPORT_ROOT%;%NATIVE_PATHS%"
"%LEAN_EXE%" "%~1" >"%~2" 2>&1
if errorlevel 1 (
  >>"%EV%\compiler-errors.txt" echo AUDIT_FILE=%~1
  type "%~2" >>"%EV%\compiler-errors.txt"
  echo AUDIT_FILE=%~1
  echo AUDIT_LOG="%~2"
  type "%~2"
  exit /b 1
)
exit /b 0

:tryMath
set "CAND="
if exist "%~1\Mathlib.olean" for %%D in ("%~1") do set "CAND=%%~fD"
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
set "MOD_SOURCE=%ROOT%deps\%MOD%.lean"
if /i "%MOD%"=="%TOPMODULE%" set "MOD_SOURCE=%ROOT%%MOD%.lean"
if not exist "%MOD_SOURCE%" exit /b 1
for %%D in ("%EV%\src\%MOD%.lean") do if not exist "%%~dpD" mkdir "%%~dpD"
copy /y "%MOD_SOURCE%" "%EV%\src\%MOD%.lean" >nul || exit /b 1
call :hash "%EV%\src\%MOD%.lean" || exit /b 1
set "SOURCE_PIN_FOUND="
for /f "usebackq tokens=1,2 delims==" %%U in ("%SOURCE_PINS%") do (
  if /i "%MOD%"=="%%U" (
    set "SOURCE_PIN_FOUND=1"
    if /i not "%HEX%"=="%%V" (
      echo SOURCE_HASH_MISMATCH=%MOD%
      exit /b 1
    )
  )
)
if not defined SOURCE_PIN_FOUND (
  echo SOURCE_PIN_MISSING=%MOD%
  exit /b 1
)
>"%EV%\module-%ORD%.key" echo ENVIRONMENT=%BASEKEY%
>>"%EV%\module-%ORD%.key" echo MODULE=%MOD%
>>"%EV%\module-%ORD%.key" echo SOURCE=%HEX%
for /f "tokens=2" %%D in ('findstr /b /c:"import " "%EV%\src\%MOD%.lean"') do (
  call :addImport "%%D"
  if errorlevel 1 exit /b 1
)
call :hash "%EV%\module-%ORD%.key" || exit /b 1
set "CHAIN=%HEX%"
set "INDEX=%CACHE%\index\%CHAIN%.txt"
call :verifiedObject "%INDEX%"
if not errorlevel 1 goto moduleHit
set "EXTERNAL_HIT="
for /f "usebackq delims=" %%C in ("%READ_CACHES%") do if not defined EXTERNAL_HIT call :tryReadObject "%%C"
if not defined EXTERNAL_HIT goto buildModule
rem Store only a local pointer to this verified immutable external cache object.
call :publishIndex || exit /b 1
:moduleHit
echo GOODWORKFLOWFRONTIER::%VERSION%::CACHE_HIT_%ORD%=%MOD%
goto moduleReady

:verifiedObject
set "OBJ="
if not exist "%~1" exit /b 1
set /p "OBJ="<"%~1"
if not defined OBJ exit /b 1
if not exist "%OBJ%\receipt.txt" exit /b 1
call :receipt "%EV%\receipt-%ORD%.txt" || exit /b 1
fc /b "%EV%\receipt-%ORD%.txt" "%OBJ%\receipt.txt" >nul || exit /b 1
exit /b 0

:tryReadObject
call :verifiedObject "%~1\index\%CHAIN%.txt"
if errorlevel 1 exit /b 0
set "EXTERNAL_HIT=1"
exit /b 0

:buildModule
set "OBJ=%CACHE%\objects\%RUNID%-%ORD%"
if exist "%OBJ%" exit /b 1
for %%D in ("%OBJ%\%MOD%.olean") do mkdir "%%~dpD" || exit /b 1
set "LEAN_PATH=%IMPORT_ROOT%;%NATIVE_PATHS%"
echo GOODWORKFLOWFRONTIER::%VERSION%::COMPILE_%ORD%=%MOD%
"%LEAN_EXE%" -j8 -o "%OBJ%\%MOD%.olean" "%MOD%.lean" >"%EV%\module-%ORD%.log" 2>&1
if errorlevel 1 (
  >>"%EV%\compiler-errors.txt" echo MODULE=%MOD%
  type "%EV%\module-%ORD%.log" >>"%EV%\compiler-errors.txt"
  type "%EV%\module-%ORD%.log"
  exit /b 1
)
call :receipt "%OBJ%\receipt.txt" || exit /b 1
call :publishIndex || exit /b 1
goto moduleReady

:publishIndex
> "%CACHE%\index\%RUNID%-%ORD%.tmp" <nul set /p "=%OBJ%"
>>"%CACHE%\index\%RUNID%-%ORD%.tmp" echo(
move /y "%CACHE%\index\%RUNID%-%ORD%.tmp" "%INDEX%" >nul || exit /b 1
exit /b 0

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
call :hash "%OBJ%\receipt.txt" || exit /b 1
>"%EV%\%MODNAME%.dep.tmp" echo %CHAIN% %HEX%
move /y "%EV%\%MODNAME%.dep.tmp" "%EV%\%MODNAME%.dep" >nul || exit /b 1
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
if not exist "%ROOT%deps\%DEP_SRC%.lean" exit /b 0
if not exist "%EV%\%DEP%.dep" exit /b 1
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
findstr /l /c:"AXIOM_AUDIT_PASS=[%~1]" "%~2" >nul
if errorlevel 1 (
  echo MISSING_AUDIT_RECEIPT=%~1
  echo AUDIT_LOG="%~2"
  type "%~2"
  exit /b 1
)
echo AXIOM_AUDIT_PASS=%~1
exit /b 0

:fail
echo RUN=FAIL
echo STAGE=%STAGE%
if defined EV (
  >"%EV%\result.txt" echo RUN=FAIL
  >>"%EV%\result.txt" echo STAGE=%STAGE%
  echo EVIDENCE="%EV%"
  if exist "%EV%\compiler-errors.txt" echo COMPILER_ERRORS="%EV%\compiler-errors.txt"
)
if defined PUSHED popd
exit /b 1
