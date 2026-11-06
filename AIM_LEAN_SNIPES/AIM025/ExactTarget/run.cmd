@echo off
setlocal EnableExtensions DisableDelayedExpansion
echo STAGE=CMD_RUNNER_ENTERED
echo PACKAGE=AIM025_EXACT_FORMALIZATION_433_v0_1_0
set "AIM_STAGE=BOOTSTRAP"
set "AIM_FAILURE="
set "AIM_EXIT=1"
set "AIM_LOG="
set "AIM_EVIDENCE="
set "AIM_PACKAGE=%~dp0"
for %%D in ("%AIM_PACKAGE%.") do set "AIM_PACKAGE=%%~fD"
set "AIM_CERTUTIL=%SystemRoot%\System32\certutil.exe"
set "AIM_FINDSTR=%SystemRoot%\System32\findstr.exe"
set "AIM_TAR=%SystemRoot%\System32\tar.exe"
set "AIM_LEAN=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
if not exist "%AIM_CERTUTIL%" set "AIM_FAILURE=CERTUTIL_NOT_FOUND"
if not exist "%AIM_FINDSTR%" set "AIM_FAILURE=FINDSTR_NOT_FOUND"
if defined AIM_FAILURE goto finish

:new_evidence
set "AIM_EVIDENCE=%AIM_PACKAGE%\evidence\r-%RANDOM%-%RANDOM%-%RANDOM%"
if exist "%AIM_EVIDENCE%" goto new_evidence
md "%AIM_EVIDENCE%\source" "%AIM_EVIDENCE%\build\lib\lean" 2>nul
if errorlevel 1 set "AIM_FAILURE=EVIDENCE_DIRECTORY_CREATE_FAILED"
if defined AIM_FAILURE goto finish
set "AIM_LOG=%AIM_EVIDENCE%\run.log"
set "AIM_SOURCE=%AIM_EVIDENCE%\source"
set "AIM_BUILD=%AIM_EVIDENCE%\build\lib\lean"
call :log "PACKAGE=AIM025_EXACT_FORMALIZATION_433_v0_1_0"
call :log "EVIDENCE=%AIM_EVIDENCE%"
call :log "RUNNER=NATIVE_CMD_ONLY"
call :log "CACHE_ACQUISITION=DISABLED"
call :log "DEPENDENCY_REBUILD=DISABLED"
call :log "CANDIDATE_OBJECT_REUSE=DISABLED"
call :log "NEW_SOURCE_STATUS=A_TIER_CANDIDATE"
call :log "BASELINE_CORE=UNCHANGED_ACCEPTED_SOURCE"
call :log "EXACT_TARGET_PROOF=NOT_SUPPLIED"
call :log "DEPENDENCY_OBJECT_HASH_CENSUS=DISABLED"
call :log "A_TIER_PROMOTION=REVIEW_REQUIRED"
call :log "ORIGINAL_AIM025_CLOSURE=OPEN"

set "AIM_STAGE=SOURCE_SNAPSHOT"
call :log "STAGE=%AIM_STAGE%"
if not exist "%AIM_PACKAGE%\SHA256SUMS" set "AIM_FAILURE=SHA256SUMS_MISSING"
if defined AIM_FAILURE goto finish
copy /b /y "%AIM_PACKAGE%\SHA256SUMS" "%AIM_SOURCE%\SHA256SUMS" >nul
if errorlevel 1 set "AIM_FAILURE=MANIFEST_COPY_FAILED"
if defined AIM_FAILURE goto finish
set /a AIM_HASH_COUNT=0 >nul
for /f "usebackq tokens=1,*" %%H in ("%AIM_SOURCE%\SHA256SUMS") do call :snapshot_one "%%H" "%%I"
if defined AIM_FAILURE goto finish
if not exist "%AIM_SOURCE%\AIM025CholletNonnegative.lean" set "AIM_FAILURE=CORE_SOURCE_MISSING"
if not exist "%AIM_SOURCE%\Audit.lean" set "AIM_FAILURE=AUDIT_SOURCE_MISSING"
if not exist "%AIM_SOURCE%\audit-theorems.txt" set "AIM_FAILURE=AUDIT_TARGETS_MISSING"
if not exist "%AIM_SOURCE%\package.json" set "AIM_FAILURE=PACKAGE_JSON_MISSING"
if not exist "%AIM_SOURCE%\modules.txt" set "AIM_FAILURE=MODULE_LIST_MISSING"
if not exist "%AIM_SOURCE%\AIM025Exact.lean" set "AIM_FAILURE=EXACT_TARGET_SOURCE_MISSING"
if not exist "%AIM_SOURCE%\AIM025Bridge.lean" set "AIM_FAILURE=BRIDGE_SOURCE_MISSING"
if defined AIM_FAILURE goto finish
call :get_hash "%AIM_SOURCE%\SHA256SUMS"
if errorlevel 1 set "AIM_FAILURE=MANIFEST_HASH_FAILED"
if defined AIM_FAILURE goto finish
set "AIM_MANIFEST_SHA=%AIM_SHA256%"
call :log "SOURCE_MANIFEST_SHA256=%AIM_MANIFEST_SHA%"
call :get_hash "%AIM_SOURCE%\AIM025CholletNonnegative.lean"
if errorlevel 1 set "AIM_FAILURE=CORE_HASH_FAILED"
if defined AIM_FAILURE goto finish
set "AIM_CORE_SHA=%AIM_SHA256%"
if /i not "%AIM_CORE_SHA%"=="8d6371fb72c496f43400bb93ba73a9df96c9e1cdac3b9aa35b384197d47acd17" set "AIM_FAILURE=PINNED_CORE_HASH_MISMATCH"
if defined AIM_FAILURE goto finish
call :get_hash "%AIM_SOURCE%\Audit.lean"
if errorlevel 1 set "AIM_FAILURE=AUDIT_HASH_FAILED"
if defined AIM_FAILURE goto finish
set "AIM_AUDIT_SHA=%AIM_SHA256%"
call :log "BASELINE_CORE_SOURCE_SHA256=%AIM_CORE_SHA%"
call :log "AUDIT_SOURCE_SHA256=%AIM_AUDIT_SHA%"
call :log "SOURCE_SNAPSHOT_HASHES=PASS"

set "AIM_STAGE=NATIVE_TOOLCHAIN"
call :log "STAGE=%AIM_STAGE%"
if not exist "%AIM_LEAN%" set "AIM_FAILURE=NATIVE_LEAN_4_33_0_NOT_FOUND"
if defined AIM_FAILURE goto finish
call :log "LEAN_EXE=%AIM_LEAN%"
"%AIM_LEAN%" --version >"%AIM_EVIDENCE%\native-version.txt" 2>&1
set "AIM_NATIVE_CODE=%ERRORLEVEL%"
type "%AIM_EVIDENCE%\native-version.txt"
call :log "NATIVE_EXIT=VERSION:%AIM_NATIVE_CODE%"
if not "%AIM_NATIVE_CODE%"=="0" set "AIM_FAILURE=NATIVE_VERSION_COMMAND_FAILED"
if defined AIM_FAILURE goto finish
"%AIM_FINDSTR%" /l /c:"Lean (version 4.33.0," "%AIM_EVIDENCE%\native-version.txt" >nul
if errorlevel 1 set "AIM_FAILURE=NATIVE_VERSION_MISMATCH"
"%AIM_FINDSTR%" /l /c:"x86_64-w64-windows-gnu" "%AIM_EVIDENCE%\native-version.txt" >nul
if errorlevel 1 set "AIM_FAILURE=NATIVE_TARGET_MISMATCH"
"%AIM_FINDSTR%" /l /c:"d8b18978322de05a8f3dba51ef03cf5461676c17" "%AIM_EVIDENCE%\native-version.txt" >nul
if errorlevel 1 set "AIM_FAILURE=NATIVE_COMMIT_MISMATCH"
if defined AIM_FAILURE goto finish
call :record_hash "%AIM_LEAN%" "LEAN_EXE"
if defined AIM_FAILURE goto finish

set "AIM_STAGE=CACHED_DEPENDENCIES"
call :log "STAGE=%AIM_STAGE%"
set "AIM_CACHE_PROBE=%~1"
if not defined AIM_CACHE_PROBE set "AIM_CACHE_PROBE=%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1"
for %%D in ("%AIM_CACHE_PROBE%") do set "AIM_CACHE_PROBE=%%~fD"
set "AIM_CACHE_PROJECT=%AIM_CACHE_PROBE%"
set "AIM_MATHLIB=%AIM_CACHE_PROBE%\.lake\packages\mathlib"
if exist "%AIM_MATHLIB%\lean-toolchain" goto cache_root_found
set "AIM_MATHLIB=%AIM_CACHE_PROBE%"
for %%D in ("%AIM_MATHLIB%\..\..\..") do set "AIM_CACHE_PROJECT=%%~fD"

:cache_root_found
if not exist "%AIM_MATHLIB%\lean-toolchain" set "AIM_FAILURE=CACHED_MATHLIB_ROOT_NOT_FOUND"
if defined AIM_FAILURE goto finish
"%AIM_FINDSTR%" /l /x /c:"leanprover/lean4:v4.33.0" /c:"v4.33.0" "%AIM_MATHLIB%\lean-toolchain" >nul
if errorlevel 1 set "AIM_FAILURE=CACHED_MATHLIB_TOOLCHAIN_MISMATCH"
if defined AIM_FAILURE goto finish
set "AIM_MATHLIB_BUILD=%AIM_MATHLIB%\.lake\build\lib\lean"
call :cache_import "Mathlib\LinearAlgebra\Matrix\Permanent"
call :cache_import "Mathlib\LinearAlgebra\Matrix\Hadamard"
call :cache_import "Mathlib\Data\Real\Basic"
call :cache_import "Mathlib\Algebra\Order\BigOperators\Group\Finset"
call :cache_import "Mathlib\Algebra\Order\BigOperators\GroupWithZero\Finset"
call :cache_import "Mathlib\Algebra\BigOperators\Field"
call :cache_import "Mathlib\Algebra\Star\BigOperators"
call :cache_import "Mathlib\Analysis\Complex\Order"
call :cache_import "Mathlib\LinearAlgebra\Matrix\PosDef"
if exist "%AIM_SOURCE%\required-cache-imports.txt" for /f "usebackq delims=" %%M in ("%AIM_SOURCE%\required-cache-imports.txt") do call :cache_import "%%M"
if defined AIM_FAILURE goto finish
call :log "CACHED_PROJECT=%AIM_CACHE_PROJECT%"
call :log "CACHED_MATHLIB=%AIM_MATHLIB%"
set "AIM_METADATA=%AIM_EVIDENCE%\dependency-metadata"
md "%AIM_METADATA%" 2>nul
if errorlevel 1 set "AIM_FAILURE=DEPENDENCY_METADATA_DIRECTORY_CREATE_FAILED"
if defined AIM_FAILURE goto finish
call :log "REFERENCE_MATHLIB_REVISION=db584cd6d46c92f209a44c0f1c829460d327499d"
call :log "CACHE_SOURCE_OBJECT_CORRESPONDENCE=EXTERNALLY_TRUSTED"
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "REFERENCE_MATHLIB_REVISION=db584cd6d46c92f209a44c0f1c829460d327499d"
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "CACHE_SOURCE_OBJECT_CORRESPONDENCE=EXTERNALLY_TRUSTED"
call :snapshot_dependency_metadata "%AIM_MATHLIB%\lean-toolchain" "mathlib-lean-toolchain.txt" "MATHLIB_TOOLCHAIN"
call :snapshot_dependency_metadata "%AIM_MATHLIB%\lake-manifest.json" "mathlib-lake-manifest.json" "MATHLIB_MANIFEST"
call :snapshot_dependency_metadata "%AIM_CACHE_PROJECT%\lake-manifest.json" "project-lake-manifest.json" "PROJECT_MANIFEST"
if defined AIM_FAILURE goto finish
call :record_mathlib_git
type nul >"%AIM_EVIDENCE%\cached-build-paths.txt"
type nul >"%AIM_EVIDENCE%\visited-cache-roots.txt"
set "AIM_LEAN_PATH=%AIM_BUILD%"
set /a AIM_VISIT_COUNT=0 >nul
call :add_build "%AIM_MATHLIB_BUILD%"
call :visit_packages "%AIM_CACHE_PROJECT%" "0"
call :visit_packages "%AIM_MATHLIB%" "0"
if defined AIM_FAILURE goto finish
set "LEAN_PATH=%AIM_LEAN_PATH%"
set "LEAN_SRC_PATH="
call :append_line "%AIM_EVIDENCE%\LEAN_PATH.txt" "%LEAN_PATH%"

set "AIM_STAGE=COMPILE_MODULES"
call :log "STAGE=%AIM_STAGE%"
call :append_line "%AIM_EVIDENCE%\run-build.log" "SOURCE_MANIFEST_SHA256=%AIM_MANIFEST_SHA%"
call :append_line "%AIM_EVIDENCE%\run-build.log" "BASELINE_CORE_SOURCE_SHA256=%AIM_CORE_SHA%"
set /a AIM_MODULE_COUNT=0 >nul
for /f "usebackq delims=" %%M in ("%AIM_SOURCE%\modules.txt") do call :compile_module "%%M"
if defined AIM_FAILURE goto finish
if %AIM_MODULE_COUNT% LSS 3 set "AIM_FAILURE=REQUIRED_MODULES_NOT_COMPILED"
if defined AIM_FAILURE goto finish
if not exist "%AIM_BUILD%\AIM025CholletNonnegative.olean" set "AIM_FAILURE=BASELINE_CORE_OBJECT_MISSING"
if not exist "%AIM_BUILD%\AIM025Exact.olean" set "AIM_FAILURE=EXACT_TARGET_OBJECT_MISSING"
if not exist "%AIM_BUILD%\AIM025Bridge.olean" set "AIM_FAILURE=BRIDGE_OBJECT_MISSING"
if defined AIM_FAILURE goto finish
call :log "COMPILED_MODULE_COUNT=%AIM_MODULE_COUNT%"

set /a AIM_AUDIT_EXPECTED=0 >nul
for /f "usebackq delims=" %%T in ("%AIM_SOURCE%\audit-theorems.txt") do set /a AIM_AUDIT_EXPECTED+=1 >nul
if %AIM_AUDIT_EXPECTED% LSS 1 set "AIM_FAILURE=EMPTY_AUDIT_TARGET_LIST"
if defined AIM_FAILURE goto finish
call :log "EXPECTED_AUDIT_COUNT=%AIM_AUDIT_EXPECTED%"

set "AIM_STAGE=COMPILE_NATIVE_AUDIT"
call :log "STAGE=%AIM_STAGE%"
call :append_line "%AIM_EVIDENCE%\run-audit.log" "SOURCE_MANIFEST_SHA256=%AIM_MANIFEST_SHA%"
call :append_line "%AIM_EVIDENCE%\run-audit.log" "AUDIT_SOURCE_SHA256=%AIM_AUDIT_SHA%"
pushd "%AIM_SOURCE%"
if errorlevel 1 set "AIM_FAILURE=AUDIT_DIRECTORY_ENTER_FAILED"
if defined AIM_FAILURE goto finish
"%AIM_LEAN%" -o "%AIM_BUILD%\Audit.olean" -i "%AIM_BUILD%\Audit.ilean" "Audit.lean" >>"%AIM_EVIDENCE%\run-audit.log" 2>&1
set "AIM_NATIVE_CODE=%ERRORLEVEL%"
popd
type "%AIM_EVIDENCE%\run-audit.log"
call :log "NATIVE_EXIT=AUDIT:%AIM_NATIVE_CODE%"
if not "%AIM_NATIVE_CODE%"=="0" set "AIM_FAILURE=NATIVE_AUDIT_COMPILATION_FAILED"
if not exist "%AIM_BUILD%\Audit.olean" set "AIM_FAILURE=AUDIT_OBJECT_MISSING"
if defined AIM_FAILURE goto finish
"%AIM_FINDSTR%" /l /c:"AIM025_EXACT_NATIVE_AXIOM_AUDIT=PASS_STANDARD_ONLY" "%AIM_EVIDENCE%\run-audit.log" >nul
if errorlevel 1 set "AIM_FAILURE=NATIVE_AUDIT_SUCCESS_MARKER_MISSING"
"%AIM_FINDSTR%" /l /c:"AIM025_EXACT_NATIVE_AXIOM_AUDIT_COUNT=%AIM_AUDIT_EXPECTED%" "%AIM_EVIDENCE%\run-audit.log" >nul
if errorlevel 1 set "AIM_FAILURE=NATIVE_AUDIT_COUNT_MARKER_MISSING"
if defined AIM_FAILURE goto finish
set /a AIM_AUDIT_COUNT=0 >nul
for /f "usebackq delims=" %%T in ("%AIM_SOURCE%\audit-theorems.txt") do call :check_report "%%T"
if defined AIM_FAILURE goto finish
if not "%AIM_AUDIT_COUNT%"=="%AIM_AUDIT_EXPECTED%" set "AIM_FAILURE=AUDIT_TARGET_COUNT_MISMATCH"
if defined AIM_FAILURE goto finish
call :log "COMPILE_PASS=Audit.lean"
call :log "EXTERNAL_COMPILER=PASS"
call :log "NATIVE_THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY"
call :log "AUDITED_THEOREM_COUNT=%AIM_AUDIT_COUNT%"
call :log "EXACT_STATEMENT_AND_TRANSFER_EVIDENCE=READY_FOR_REVIEW"
set "AIM_STAGE=COMPLETE"
set "AIM_EXIT=0"

:finish
if defined AIM_FAILURE call :log "FAIL_STAGE=%AIM_STAGE%"
if defined AIM_FAILURE call :log "FAIL_REASON=%AIM_FAILURE%"
call :log "A_TIER_PROMOTION=REVIEW_REQUIRED"
call :log "ORIGINAL_AIM025_CLOSURE=OPEN"
call :log "FINAL_EXIT=%AIM_EXIT%"
if not defined AIM_EVIDENCE goto end
if not exist "%AIM_EVIDENCE%\source" goto end
copy /b /y "%AIM_LOG%" "%AIM_EVIDENCE%\run-result.txt" >nul 2>&1
if not exist "%AIM_TAR%" goto evidence_folder
"%AIM_TAR%" -a -cf "%AIM_EVIDENCE%.zip" -C "%AIM_EVIDENCE%" --exclude build --exclude archive.log . >"%AIM_EVIDENCE%\archive.log" 2>&1
if errorlevel 1 goto evidence_folder
echo EVIDENCE_ZIP="%AIM_EVIDENCE%.zip"
goto end

:evidence_folder
echo EVIDENCE_FOLDER="%AIM_EVIDENCE%"

:end
exit /b %AIM_EXIT%

:snapshot_one
if defined AIM_FAILURE exit /b 1
set "AIM_EXPECTED=%~1"
set "AIM_REL=%~2"
if not defined AIM_REL set "AIM_FAILURE=MALFORMED_MANIFEST_ENTRY"
if not "%AIM_REL:..=%"=="%AIM_REL%" set "AIM_FAILURE=INVALID_MANIFEST_PATH"
if not "%AIM_REL::=%"=="%AIM_REL%" set "AIM_FAILURE=INVALID_MANIFEST_PATH"
if "%AIM_REL:~0,1%"=="/" set "AIM_FAILURE=INVALID_MANIFEST_PATH"
if "%AIM_REL:~0,1%"=="\" set "AIM_FAILURE=INVALID_MANIFEST_PATH"
if defined AIM_FAILURE exit /b 1
set "AIM_REL=%AIM_REL:/=\%"
set "AIM_DEST=%AIM_SOURCE%\%AIM_REL%"
for %%D in ("%AIM_DEST%") do if not exist "%%~dpD" md "%%~dpD" 2>nul
copy /b /y "%AIM_PACKAGE%\%AIM_REL%" "%AIM_DEST%" >nul
if errorlevel 1 set "AIM_FAILURE=SNAPSHOT_COPY_FAILED:%AIM_REL%"
if defined AIM_FAILURE exit /b 1
call :get_hash "%AIM_DEST%"
if errorlevel 1 set "AIM_FAILURE=SNAPSHOT_HASH_FAILED:%AIM_REL%"
if defined AIM_FAILURE exit /b 1
if /i not "%AIM_SHA256%"=="%AIM_EXPECTED%" set "AIM_FAILURE=SNAPSHOT_HASH_MISMATCH:%AIM_REL%"
if defined AIM_FAILURE exit /b 1
call :append_line "%AIM_EVIDENCE%\source-hashes.txt" "%AIM_SHA256%  %AIM_REL%"
set /a AIM_HASH_COUNT+=1 >nul
exit /b 0

:get_hash
set "AIM_SHA256="
"%AIM_CERTUTIL%" -hashfile "%~1" SHA256 >"%AIM_EVIDENCE%\hash-last.log" 2>&1
if errorlevel 1 exit /b 1
for /f "usebackq delims=" %%H in ("%AIM_EVIDENCE%\hash-last.log") do call :hash_line "%%H"
if not defined AIM_SHA256 exit /b 1
exit /b 0

:hash_line
set "AIM_HASH_LINE=%~1"
set "AIM_HASH_LINE=%AIM_HASH_LINE: =%"
if "%AIM_HASH_LINE:~63,1%"=="" exit /b 0
if not "%AIM_HASH_LINE:~64,1%"=="" exit /b 0
set "AIM_NONHEX="
for /f "delims=0123456789abcdefABCDEF" %%Z in ("%AIM_HASH_LINE%") do set "AIM_NONHEX=%%Z"
if defined AIM_NONHEX exit /b 0
set "AIM_SHA256=%AIM_HASH_LINE%"
exit /b 0

:record_hash
if defined AIM_FAILURE exit /b 1
call :get_hash "%~1"
if errorlevel 1 set "AIM_FAILURE=IDENTITY_HASH_FAILED:%~2"
if defined AIM_FAILURE exit /b 1
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "%~2_SHA256=%AIM_SHA256%"
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "%~2_PATH=%~1"
exit /b 0

:snapshot_dependency_metadata
if defined AIM_FAILURE exit /b 1
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "%~3_SOURCE_PATH=%~1"
if not exist "%~1" goto dependency_metadata_missing
copy /b /y "%~1" "%AIM_METADATA%\%~2" >nul
if errorlevel 1 set "AIM_FAILURE=DEPENDENCY_METADATA_COPY_FAILED:%~3"
if defined AIM_FAILURE exit /b 1
call :record_hash "%AIM_METADATA%\%~2" "%~3"
if defined AIM_FAILURE exit /b 1
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "%~3_SNAPSHOT=dependency-metadata\%~2"
exit /b 0

:dependency_metadata_missing
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "%~3=NOT_PRESENT"
exit /b 0

:record_mathlib_git
set "AIM_GIT="
set "AIM_GIT_METADATA_REASON=GIT_EXE_NOT_FOUND"
for %%G in (git.exe) do set "AIM_GIT=%%~$PATH:G"
if not defined AIM_GIT goto git_metadata_unavailable
set "AIM_GIT_METADATA_REASON=MATHLIB_GIT_DIRECTORY_NOT_PRESENT"
if not exist "%AIM_MATHLIB%\.git" goto git_metadata_unavailable
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "GIT_EXE=%AIM_GIT%"
"%AIM_GIT%" --no-optional-locks -C "%AIM_MATHLIB%" rev-parse --verify HEAD >"%AIM_METADATA%\mathlib-git-head.txt" 2>&1
set "AIM_GIT_HEAD_CODE=%ERRORLEVEL%"
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "MATHLIB_GIT_HEAD_EXIT=%AIM_GIT_HEAD_CODE%"
"%AIM_GIT%" --no-optional-locks -C "%AIM_MATHLIB%" status --porcelain --untracked-files=no >"%AIM_METADATA%\mathlib-git-status.txt" 2>&1
set "AIM_GIT_STATUS_CODE=%ERRORLEVEL%"
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "MATHLIB_GIT_STATUS_EXIT=%AIM_GIT_STATUS_CODE%"
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "MATHLIB_GIT_STATUS_SCOPE=TRACKED_WORKTREE_ONLY"
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "MATHLIB_GIT_METADATA=RECORDED_WITH_EXIT_CODES"
exit /b 0

:git_metadata_unavailable
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "MATHLIB_GIT_METADATA=UNAVAILABLE"
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "MATHLIB_GIT_METADATA_REASON=%AIM_GIT_METADATA_REASON%"
call :append_line "%AIM_EVIDENCE%\dependency-identity.txt" "MATHLIB_CHECKOUT_IDENTITY=NOT_CONFIRMED"
exit /b 0

:cache_import
if defined AIM_FAILURE exit /b 1
set "AIM_IMPORT_REL=%~1"
set "AIM_IMPORT_REL=%AIM_IMPORT_REL:.=\%"
if not exist "%AIM_MATHLIB_BUILD%\%AIM_IMPORT_REL%.olean" set "AIM_FAILURE=CACHED_IMPORT_MISSING:%~1"
if defined AIM_FAILURE exit /b 1
call :append_line "%AIM_EVIDENCE%\cached-imports.txt" "%AIM_IMPORT_REL%"
exit /b 0

:add_build
if defined AIM_FAILURE exit /b 1
if not exist "%~1\" exit /b 0
"%AIM_FINDSTR%" /i /l /x /c:"%~f1" "%AIM_EVIDENCE%\cached-build-paths.txt" >nul
if not errorlevel 1 exit /b 0
set "AIM_LEAN_PATH=%AIM_LEAN_PATH%;%~f1"
call :append_line "%AIM_EVIDENCE%\cached-build-paths.txt" "%~f1"
exit /b 0

:visit_packages
if defined AIM_FAILURE exit /b 1
if "%~2"=="4" exit /b 0
if not exist "%~1\.lake\packages\" exit /b 0
"%AIM_FINDSTR%" /i /l /x /c:"%~f1" "%AIM_EVIDENCE%\visited-cache-roots.txt" >nul
if not errorlevel 1 exit /b 0
set /a AIM_VISIT_COUNT+=1 >nul
if %AIM_VISIT_COUNT% GTR 300 set "AIM_FAILURE=CACHED_PACKAGE_DISCOVERY_LIMIT"
if defined AIM_FAILURE exit /b 1
call :append_line "%AIM_EVIDENCE%\visited-cache-roots.txt" "%~f1"
for /d %%D in ("%~1\.lake\packages\*") do call :visit_package "%%~fD" "%~2"
exit /b 0

:visit_package
if defined AIM_FAILURE exit /b 1
call :add_build "%~1\.lake\build\lib\lean"
set /a AIM_NEXT_DEPTH=%~2+1 >nul
call :visit_packages "%~1" "%AIM_NEXT_DEPTH%"
exit /b 0

:compile_module
if defined AIM_FAILURE exit /b 1
set "AIM_MODULE=%~1"
if not defined AIM_MODULE set "AIM_FAILURE=EMPTY_MODULE_NAME"
if not "%AIM_MODULE:..=%"=="%AIM_MODULE%" set "AIM_FAILURE=INVALID_MODULE_PATH"
if not "%AIM_MODULE::=%"=="%AIM_MODULE%" set "AIM_FAILURE=INVALID_MODULE_PATH"
if "%AIM_MODULE:~0,1%"=="/" set "AIM_FAILURE=INVALID_MODULE_PATH"
if "%AIM_MODULE:~0,1%"=="\" set "AIM_FAILURE=INVALID_MODULE_PATH"
if defined AIM_FAILURE exit /b 1
set "AIM_MODULE=%AIM_MODULE:/=\%"
if not "%AIM_MODULE:~-5%"==".lean" set "AIM_FAILURE=MODULE_EXTENSION_NOT_LEAN"
if defined AIM_FAILURE exit /b 1
if not exist "%AIM_SOURCE%\%AIM_MODULE%" set "AIM_FAILURE=MODULE_SOURCE_MISSING:%AIM_MODULE%"
if defined AIM_FAILURE exit /b 1
set "AIM_MODULE_STEM=%AIM_MODULE:~0,-5%"
set "AIM_MODULE_LOG=%AIM_EVIDENCE%\compile\%AIM_MODULE_STEM%.log"
for %%D in ("%AIM_MODULE_LOG%") do if not exist "%%~dpD" md "%%~dpD" 2>nul
for %%D in ("%AIM_BUILD%\%AIM_MODULE_STEM%.olean") do if not exist "%%~dpD" md "%%~dpD" 2>nul
set "AIM_STAGE=COMPILE:%AIM_MODULE%"
call :log "STAGE=%AIM_STAGE%"
pushd "%AIM_SOURCE%"
if errorlevel 1 set "AIM_FAILURE=SOURCE_DIRECTORY_ENTER_FAILED"
if defined AIM_FAILURE exit /b 1
"%AIM_LEAN%" -o "%AIM_BUILD%\%AIM_MODULE_STEM%.olean" -i "%AIM_BUILD%\%AIM_MODULE_STEM%.ilean" "%AIM_MODULE%" >"%AIM_MODULE_LOG%" 2>&1
set "AIM_NATIVE_CODE=%ERRORLEVEL%"
popd
type "%AIM_MODULE_LOG%"
call :append_line "%AIM_EVIDENCE%\run-build.log" "MODULE=%AIM_MODULE%"
type "%AIM_MODULE_LOG%" >>"%AIM_EVIDENCE%\run-build.log"
call :append_line "%AIM_EVIDENCE%\run-build.log" "NATIVE_EXIT=%AIM_NATIVE_CODE%"
call :log "NATIVE_EXIT=%AIM_MODULE%:%AIM_NATIVE_CODE%"
if not "%AIM_NATIVE_CODE%"=="0" set "AIM_FAILURE=MODULE_COMPILATION_FAILED:%AIM_MODULE%"
if not exist "%AIM_BUILD%\%AIM_MODULE_STEM%.olean" set "AIM_FAILURE=MODULE_OBJECT_MISSING:%AIM_MODULE%"
if defined AIM_FAILURE exit /b 1
set /a AIM_MODULE_COUNT+=1 >nul
call :log "COMPILE_PASS=%AIM_MODULE%"
exit /b 0

:check_report
if defined AIM_FAILURE exit /b 1
"%AIM_FINDSTR%" /l /c:"AXIOM_AUDIT_PASS=[%~1]" "%AIM_EVIDENCE%\run-audit.log" >nul
if errorlevel 1 set "AIM_FAILURE=THEOREM_AUDIT_MARKER_MISSING:%~1"
"%AIM_FINDSTR%" /l /c:"'%~1' depends on axioms:" /c:"'%~1' does not depend on any axioms" "%AIM_EVIDENCE%\run-audit.log" >nul
if errorlevel 1 set "AIM_FAILURE=THEOREM_AXIOM_REPORT_MISSING:%~1"
if defined AIM_FAILURE exit /b 1
set /a AIM_AUDIT_COUNT+=1 >nul
exit /b 0

:log
set "AIM_MESSAGE=%~1"
setlocal EnableDelayedExpansion
echo(!AIM_MESSAGE!
if defined AIM_LOG >>"!AIM_LOG!" echo(!AIM_MESSAGE!
endlocal
exit /b 0

:append_line
set "AIM_APPEND_PATH=%~1"
set "AIM_APPEND_TEXT=%~2"
setlocal EnableDelayedExpansion
>>"!AIM_APPEND_PATH!" echo(!AIM_APPEND_TEXT!
endlocal
exit /b 0

