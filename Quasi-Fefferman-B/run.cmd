@echo off
setlocal EnableExtensions
rem External native Windows Lean 4.33.0 only. This file is never executed locally by Codex.
set "QFB_AUDIT_SELECTION="
if "%~1"=="" goto :options_ready
if not "%~1"=="--target" exit /b 2
if not "%~2"=="QuasiFeffermanB.Endpoints.Root" exit /b 2
if not "%~3"=="" exit /b 2
set "QFB_AUDIT_SELECTION=--target QuasiFeffermanB.Endpoints.Root"
:options_ready
set "QFB_PROJECT=%~dp0"
for %%I in ("%QFB_PROJECT%..") do set "QFB_REPOSITORY=%%~fI"
set "QFB_NATIVE_PACKAGE=%TEMP%\qfb-native-%RANDOM%-%RANDOM%"
set "MATHLIB_NO_CACHE_ON_UPDATE=1"
set "PYTHONUTF8=1"
git -C "%QFB_REPOSITORY%" cat-file -e 09dfe94a1ef150e21d09df3013fbe09002ef139c^{commit}
if errorlevel 1 exit /b 1
py -3 "%QFB_PROJECT%scripts\prepare.py" --repository "%QFB_REPOSITORY%" --output "%QFB_NATIVE_PACKAGE%"
if errorlevel 1 exit /b 1
pushd "%QFB_NATIVE_PACKAGE%"
call lean --version > evidence\lean-version.txt 2>&1
findstr /c:"version 4.33.0," evidence\lean-version.txt >nul
if errorlevel 1 goto :fail
rem lake cache downloads native-platform Mathlib objects at the pinned revision.
call lake exe cache get > evidence\mathlib-cache.log 2>&1
if errorlevel 1 goto :fail
git -C .lake\packages\mathlib rev-parse HEAD > evidence\mathlib-revision.txt
findstr /x /c:"db584cd6d46c92f209a44c0f1c829460d327499d" evidence\mathlib-revision.txt >nul
if errorlevel 1 goto :fail
py -3 qfb\scripts\audit.py --self-test
if errorlevel 1 goto :fail
call lake env py -3 qfb\scripts\audit.py --package . %QFB_AUDIT_SELECTION% > evidence\external-driver.log 2>&1
if errorlevel 1 goto :fail
echo EXTERNAL_EXACT_DECLARATION_AUDIT_PASS
echo Evidence: %QFB_NATIVE_PACKAGE%\evidence
echo Root and uncompleted Q/A contracts remain pending.
popd
exit /b 0
:fail
echo EXTERNAL_EXACT_DECLARATION_AUDIT_FAIL
echo Evidence: %QFB_NATIVE_PACKAGE%\evidence
popd
exit /b 1

