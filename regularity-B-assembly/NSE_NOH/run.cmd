@echo off
setlocal EnableExtensions EnableDelayedExpansion
cd /d "%~dp0"
if errorlevel 1 (echo PROJECT_DIR=NOT_ACCESSIBLE & exit /b 2)

rem NSE_NOH FIX21 native FAST16 offline cached runner; requires compiler installed by user.
rem Never runs Lake, elan toolchain install, PowerShell, Python, git or network.
rem Optional explicit overrides: NOH_LEAN_EXE, NOH_CACHE_ROOT.
set "NOH_PROJECT=%~dp0"
set "NOH_SOURCE=%NOH_PROJECT%NSE_NOH.lean"
set "NOH_AUDIT_SOURCE=%NOH_PROJECT%NSE_NOH_Audit.lean"
set "NOH_GEOMETRY_SOURCE=%NOH_PROJECT%NSE_NOH_Geometry.lean"
set "NOH_MODES_SOURCE=%NOH_PROJECT%NSE_NOH_Modes.lean"
set "NOH_JET_SOURCE=%NOH_PROJECT%NSE_NOH_Jet.lean"
set "NOH_DERIVATIVE_SOURCE=%NOH_PROJECT%NSE_NOH_Derivative.lean"
set "NOH_LAPLACIAN_SOURCE=%NOH_PROJECT%NSE_NOH_Laplacian.lean"
set "NOH_CLASSICAL_SOURCE=%NOH_PROJECT%NSE_NOH_Classical.lean"
set "NOH_ENERGY_SOURCE=%NOH_PROJECT%NSE_NOH_Energy.lean"
set "NOH_TORUS_MASS_SOURCE=%NOH_PROJECT%NSE_NOH_TorusMass.lean"
set "NOH_L2_SOURCE=%NOH_PROJECT%NSE_NOH_L2Pullback.lean"
set "NOH_L2_CLOSURE_SOURCE=%NOH_PROJECT%NSE_NOH_L2Closure.lean"
set "NOH_FOURIER_SOURCE=%NOH_PROJECT%NSE_NOH_FourierSpectral.lean"
set "NOH_FOURIER_TEST_SOURCE=%NOH_PROJECT%NSE_NOH_FourierWeakTest.lean"
set "NOH_OUT=%NOH_PROJECT%.native-build"
if not exist "%NOH_OUT%" mkdir "%NOH_OUT%"
if not exist "%NOH_OUT%" (echo OUTPUT_DIR=ACCESS_DENIED & exit /b 3)
if not exist "%NOH_SOURCE%" (echo SOURCE=NOT_FOUND & exit /b 4)
if not exist "%NOH_AUDIT_SOURCE%" (echo AUDIT_SOURCE=NOT_FOUND & exit /b 5)
if not exist "%NOH_GEOMETRY_SOURCE%" (echo GEOMETRY_SOURCE=NOT_FOUND & exit /b 5)
if not exist "%NOH_MODES_SOURCE%" (echo MODES_SOURCE=NOT_FOUND & exit /b 5)
if not exist "%NOH_JET_SOURCE%" (echo JET_SOURCE=NOT_FOUND & exit /b 5)
if not exist "%NOH_DERIVATIVE_SOURCE%" (echo DERIVATIVE_SOURCE=NOT_FOUND & exit /b 5)
if not exist "%NOH_LAPLACIAN_SOURCE%" (echo LAPLACIAN_SOURCE=NOT_FOUND & exit /b 5)
if not exist "%NOH_CLASSICAL_SOURCE%" (echo CLASSICAL_SOURCE=NOT_FOUND & exit /b 5)
if not exist "%NOH_ENERGY_SOURCE%" (echo ENERGY_SOURCE=NOT_FOUND & exit /b 5)
if not exist "%NOH_TORUS_MASS_SOURCE%" (echo TORUS_MASS_SOURCE=NOT_FOUND & exit /b 5)
if not exist "%NOH_L2_SOURCE%" (echo L2_PULLBACK_SOURCE=NOT_FOUND & exit /b 5)
if not exist "%NOH_L2_CLOSURE_SOURCE%" (echo L2_CLOSURE_SOURCE=NOT_FOUND & exit /b 5)
if not exist "%NOH_FOURIER_SOURCE%" (echo FOURIER_SOURCE=NOT_FOUND & exit /b 5)
if not exist "%NOH_FOURIER_TEST_SOURCE%" (echo FOURIER_TEST_SOURCE=NOT_FOUND & exit /b 5)

set "NOH_COMPILER="
set "NOH_COMPILER_VERSION="
set "NOH_MATHLIB="
set "NOH_CACHE="

if defined NOH_LEAN_EXE (
  call :tryCompiler "%NOH_LEAN_EXE%"
) else (
  rem Native direct compiler, then installed native elan toolchains, then PATH.
  call :tryCompiler "%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
  call :tryCompiler "%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.34.0-rc1\bin\lean.exe"
  for /d %%D in ("%USERPROFILE%\.elan\toolchains\*") do call :tryCompiler "%%~fD\bin\lean.exe"
  for /d %%D in ("%USERPROFILE%\lean-native\*") do call :tryCompiler "%%~fD\bin\lean.exe"
  for /d %%D in ("%USERPROFILE%\Downloads\*") do call :tryCompiler "%%~fD\bin\lean.exe"
  for /f "delims=" %%F in ('where.exe lean.exe 2^>nul') do call :tryCompiler "%%~fF"
)
if not defined NOH_COMPILER (
  echo NATIVE_LEAN=NOT_FOUND
  echo Attempted installed native Lean 4.33.0 and 4.34.0-rc1 compiler locations.
  echo Set "NOH_LEAN_EXE=C:\full\path\to\lean.exe" and rerun.
  echo PATH_DIAGNOSTIC_BEGIN
  where.exe lean.exe 2>nul
  echo PATH_DIAGNOSTIC_END
  exit /b 6
)

echo NATIVE_LEAN=FOUND
echo LEAN_EXE="%NOH_COMPILER%"
echo LEAN_VERSION=%NOH_COMPILER_VERSION%
"%NOH_COMPILER%" --version > "%NOH_OUT%\lean-version.log" 2>&1
if errorlevel 1 (echo NATIVE_LEAN=VERSION_PROBE_FAILED & exit /b 7)
type "%NOH_OUT%\lean-version.log"

if defined NOH_CACHE_ROOT (
  call :tryCache "%NOH_CACHE_ROOT%"
) else (
  rem Prefer previously used cached Mathlib workspaces; discovery is read-only.
  call :tryCache "%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1"
  call :tryCache "%USERPROFILE%\Downloads\awpi_nse_fourier_to_gp_lean_v0_1_5"
  call :tryCache "%USERPROFILE%\Downloads\awpi_nse_fourier_gp_m7_one_go_lean_v0_1_1"
  call :tryCache "%USERPROFILE%\Downloads\Methlib"
  for /d %%D in ("%USERPROFILE%\lean-native\*") do call :tryCache "%%~fD"
  for /d %%D in ("%USERPROFILE%\Downloads\*") do call :tryCache "%%~fD"
)
if not defined NOH_CACHE (
  echo MATHLIB_CACHE=NOT_FOUND_FOR_LEAN_%NOH_COMPILER_VERSION%
  echo No cached precompiled Mathlib.olean was selected.
  echo Set "NOH_CACHE_ROOT=C:\full\path\to\cached\LeanWorkspace" and rerun.
  echo Required file usually at .lake\packages\mathlib\.lake\build\lib\lean\Mathlib.olean
  echo OFFLINE_ONLY=YES
  exit /b 8
)
echo MATHLIB_CACHE=FOUND
echo CACHE_ROOT="%NOH_CACHE%"
echo MATHLIB_OLEAN_DIR="%NOH_MATHLIB%"

rem Use only cached libraries. No Lake, git or download operations.
set "LEAN_PATH=%NOH_OUT%;%NOH_MATHLIB%"
if exist "%NOH_CACHE%\.lake\build\lib\lean" set "LEAN_PATH=!LEAN_PATH!;%NOH_CACHE%\.lake\build\lib\lean"
if exist "%NOH_CACHE%\build\lib\lean" set "LEAN_PATH=!LEAN_PATH!;%NOH_CACHE%\build\lib\lean"
for /d %%D in ("%NOH_CACHE%\.lake\packages\*") do (
  if exist "%%~fD\.lake\build\lib\lean" set "LEAN_PATH=!LEAN_PATH!;%%~fD\.lake\build\lib\lean"
)
for /d %%D in ("%NOH_CACHE%\.lake\packages\mathlib\.lake\packages\*") do (
  if exist "%%~fD\.lake\build\lib\lean" set "LEAN_PATH=!LEAN_PATH!;%%~fD\.lake\build\lib\lean"
)

(
  echo PACKAGE=NSE_NOH_CACHED_FIX21
  echo MODE=EXTERNAL_NATIVE_WINDOWS_OFFLINE_CACHE
  echo SOURCE=%NOH_SOURCE%
  echo GEOMETRY_SOURCE=%NOH_GEOMETRY_SOURCE%
  echo MODES_SOURCE=%NOH_MODES_SOURCE%
  echo JET_SOURCE=%NOH_JET_SOURCE%
  echo DERIVATIVE_SOURCE=%NOH_DERIVATIVE_SOURCE%
  echo LAPLACIAN_SOURCE=%NOH_LAPLACIAN_SOURCE%
  echo CLASSICAL_SOURCE=%NOH_CLASSICAL_SOURCE%
  echo ENERGY_SOURCE=%NOH_ENERGY_SOURCE%
  echo TORUS_MASS_SOURCE=%NOH_TORUS_MASS_SOURCE%
  echo L2_PULLBACK_SOURCE=%NOH_L2_SOURCE%
  echo L2_CLOSURE_SOURCE=%NOH_L2_CLOSURE_SOURCE%
  echo FOURIER_SOURCE=%NOH_FOURIER_SOURCE%
  echo FOURIER_TEST_SOURCE=%NOH_FOURIER_TEST_SOURCE%
  echo COMPILER=%NOH_COMPILER%
  echo COMPILER_VERSION=%NOH_COMPILER_VERSION%
  echo CACHE_ROOT=%NOH_CACHE%
  echo PREBUILT_MATHLIB=%NOH_MATHLIB%
  echo THREADS=16
  echo NO_LAKE_NO_NETWORK=YES
  echo UNCONDITIONAL_NSE_NOH=OPEN
) > "%NOH_OUT%\build-context.txt"
type "%NOH_OUT%\build-context.txt"
if exist "%SystemRoot%\System32\certutil.exe" (
 "%SystemRoot%\System32\certutil.exe" -hashfile "%NOH_SOURCE%" SHA256 > "%NOH_OUT%\source-sha256.log" 2>&1
 "%SystemRoot%\System32\certutil.exe" -hashfile "%NOH_MATHLIB%\Mathlib.olean" SHA256 > "%NOH_OUT%\mathlib-olean-sha256.log" 2>&1
)

rem Static placeholder scan is NOT an axiom audit.
findstr.exe /N /I /R /C:"^[ ]*axiom " /C:"^[ ]*sorry" /C:"^[ ]*admit" /C:":= sorry" "%NOH_SOURCE%" "%NOH_GEOMETRY_SOURCE%" "%NOH_MODES_SOURCE%" "%NOH_JET_SOURCE%" "%NOH_DERIVATIVE_SOURCE%" "%NOH_LAPLACIAN_SOURCE%" "%NOH_CLASSICAL_SOURCE%" "%NOH_ENERGY_SOURCE%" "%NOH_TORUS_MASS_SOURCE%" "%NOH_L2_SOURCE%" "%NOH_L2_CLOSURE_SOURCE%" "%NOH_FOURIER_SOURCE%" "%NOH_FOURIER_TEST_SOURCE%" > "%NOH_OUT%\source-scan.log"
if not errorlevel 1 (
  type "%NOH_OUT%\source-scan.log"
  echo SOURCE_SCAN=FAIL
  exit /b 9
)
echo SOURCE_SCAN=PASS
if exist "%NOH_OUT%\run-audit.log" del /q "%NOH_OUT%\run-audit.log" >nul 2>&1
if exist "%NOH_OUT%\NSE_NOH.olean" del /q "%NOH_OUT%\NSE_NOH.olean" >nul 2>&1
"%NOH_COMPILER%" -j16 -o "%NOH_OUT%\NSE_NOH.olean" "%NOH_SOURCE%" > "%NOH_OUT%\run-build.log" 2>&1
set "NOH_BUILD_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-build.log"
if not "%NOH_BUILD_EXIT%"=="0" (
  echo PROJECT_BUILD=FAIL
  echo BUILD_LOG="%NOH_OUT%\run-build.log"
  echo UNCONDITIONAL_NSE_NOH=OPEN
  exit /b %NOH_BUILD_EXIT%
)
if not exist "%NOH_OUT%\NSE_NOH.olean" (
  echo PROJECT_BUILD=FAIL_NO_OLEAN
  exit /b 10
)
echo ROOT_MODULE_BUILD=PASS

rem Independent geometry module imports the compiled NSE_NOH module.
if exist "%NOH_OUT%\NSE_NOH_Geometry.olean" del /q "%NOH_OUT%\NSE_NOH_Geometry.olean" >nul 2>&1
"%NOH_COMPILER%" -j16 -o "%NOH_OUT%\NSE_NOH_Geometry.olean" "%NOH_GEOMETRY_SOURCE%" > "%NOH_OUT%\run-geometry.log" 2>&1
set "NOH_GEOM_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-geometry.log"
if not "%NOH_GEOM_EXIT%"=="0" (
  echo GEOMETRY_BUILD=FAIL
  echo GEOMETRY_LOG="%NOH_OUT%\run-geometry.log"
  echo UNCONDITIONAL_NSE_NOH=OPEN
  exit /b %NOH_GEOM_EXIT%
)
if not exist "%NOH_OUT%\NSE_NOH_Geometry.olean" (
  echo GEOMETRY_BUILD=FAIL_NO_OLEAN
  exit /b 13
)
echo GEOMETRY_BUILD=PASS

rem Rank-two mode subgroup and triad closure: independent geometric edge.
if exist "%NOH_OUT%\NSE_NOH_Modes.olean" del /q "%NOH_OUT%\NSE_NOH_Modes.olean" >nul 2>&1
"%NOH_COMPILER%" -j16 -o "%NOH_OUT%\NSE_NOH_Modes.olean" "%NOH_MODES_SOURCE%" > "%NOH_OUT%\run-modes.log" 2>&1
set "NOH_MODES_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-modes.log"
if not "%NOH_MODES_EXIT%"=="0" (
  echo MODES_BUILD=FAIL
  echo MODES_LOG="%NOH_OUT%\run-modes.log"
  exit /b %NOH_MODES_EXIT%
)
if not exist "%NOH_OUT%\NSE_NOH_Modes.olean" (
  echo MODES_BUILD=FAIL_NO_OLEAN
  exit /b 15
)
echo MODES_BUILD=PASS

rem Algebraic 2D3C nonlinear PDE-jet reduction.
if exist "%NOH_OUT%\NSE_NOH_Jet.olean" del /q "%NOH_OUT%\NSE_NOH_Jet.olean" >nul 2>&1
"%NOH_COMPILER%" -j16 -o "%NOH_OUT%\NSE_NOH_Jet.olean" "%NOH_JET_SOURCE%" > "%NOH_OUT%\run-jet.log" 2>&1
set "NOH_JET_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-jet.log"
if not "%NOH_JET_EXIT%"=="0" (
  echo JET_BUILD=FAIL
  echo JET_LOG="%NOH_OUT%\run-jet.log"
  exit /b %NOH_JET_EXIT%
)
if not exist "%NOH_OUT%\NSE_NOH_Jet.olean" (
  echo JET_BUILD=FAIL_NO_OLEAN
  exit /b 16
)
echo JET_BUILD=PASS

rem Actual differentiable-function chain rule edge for the 2D3C spatial lift.
if exist "%NOH_OUT%\NSE_NOH_Derivative.olean" del /q "%NOH_OUT%\NSE_NOH_Derivative.olean" >nul 2>&1
"%NOH_COMPILER%" -j16 -o "%NOH_OUT%\NSE_NOH_Derivative.olean" "%NOH_DERIVATIVE_SOURCE%" > "%NOH_OUT%\run-derivative.log" 2>&1
set "NOH_DERIVATIVE_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-derivative.log"
if not "%NOH_DERIVATIVE_EXIT%"=="0" (
  echo DERIVATIVE_BUILD=FAIL
  echo DERIVATIVE_LOG="%NOH_OUT%\run-derivative.log"
  echo UNCONDITIONAL_NSE_NOH=OPEN
  exit /b %NOH_DERIVATIVE_EXIT%
)
if not exist "%NOH_OUT%\NSE_NOH_Derivative.olean" (
  echo DERIVATIVE_BUILD=FAIL_NO_OLEAN
  exit /b 19
)
echo DERIVATIVE_BUILD=PASS

rem Second-order derivatives and actual Laplacian transfer.
if exist "%NOH_OUT%\NSE_NOH_Laplacian.olean" del /q "%NOH_OUT%\NSE_NOH_Laplacian.olean" >nul 2>&1
"%NOH_COMPILER%" -j16 -o "%NOH_OUT%\NSE_NOH_Laplacian.olean" "%NOH_LAPLACIAN_SOURCE%" > "%NOH_OUT%\run-laplacian.log" 2>&1
set "NOH_LAPLACIAN_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-laplacian.log"
if not "%NOH_LAPLACIAN_EXIT%"=="0" (
  echo LAPLACIAN_BUILD=FAIL
  echo LAPLACIAN_LOG="%NOH_OUT%\run-laplacian.log"
  echo UNCONDITIONAL_NSE_NOH=OPEN
  exit /b %NOH_LAPLACIAN_EXIT%
)
if not exist "%NOH_OUT%\NSE_NOH_Laplacian.olean" (
  echo LAPLACIAN_BUILD=FAIL_NO_OLEAN
  exit /b 21
)
echo LAPLACIAN_BUILD=PASS

rem Actual pointwise classical 2D3C PDE lift, with explicit C2 hypotheses.
if exist "%NOH_OUT%\NSE_NOH_Classical.olean" del /q "%NOH_OUT%\NSE_NOH_Classical.olean" >nul 2>&1
"%NOH_COMPILER%" -j16 -o "%NOH_OUT%\NSE_NOH_Classical.olean" "%NOH_CLASSICAL_SOURCE%" > "%NOH_OUT%\run-classical.log" 2>&1
set "NOH_CLASSICAL_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-classical.log"
if not "%NOH_CLASSICAL_EXIT%"=="0" (
  echo CLASSICAL_BUILD=FAIL
  echo CLASSICAL_LOG="%NOH_OUT%\run-classical.log"
  echo UNCONDITIONAL_NSE_NOH=OPEN
  exit /b %NOH_CLASSICAL_EXIT%
)
if not exist "%NOH_OUT%\NSE_NOH_Classical.olean" (
  echo CLASSICAL_BUILD=FAIL_NO_OLEAN
  exit /b 22
)
echo CLASSICAL_BUILD=PASS

rem FIX15 physically relevant POINTWISE 2D3C mass and Dirichlet densities.
if exist "%NOH_OUT%\NSE_NOH_Energy.olean" del /q "%NOH_OUT%\NSE_NOH_Energy.olean" >nul 2>&1
"%NOH_COMPILER%" -j16 -o "%NOH_OUT%\NSE_NOH_Energy.olean" "%NOH_ENERGY_SOURCE%" > "%NOH_OUT%\run-energy.log" 2>&1
set "NOH_ENERGY_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-energy.log"
if not "%NOH_ENERGY_EXIT%"=="0" (
  echo ENERGY_BUILD=FAIL
  echo ENERGY_LOG="%NOH_OUT%\run-energy.log"
  echo UNCONDITIONAL_NSE_NOH=OPEN
  exit /b %NOH_ENERGY_EXIT%
)
if not exist "%NOH_OUT%\NSE_NOH_Energy.olean" (
  echo ENERGY_BUILD=FAIL_NO_OLEAN
  exit /b 25
)
echo ENERGY_BUILD=PASS

rem FIX15 actual Haar projection and integrated 2D3C kinetic mass.
if exist "%NOH_OUT%\NSE_NOH_TorusMass.olean" del /q "%NOH_OUT%\NSE_NOH_TorusMass.olean" >nul 2>&1
"%NOH_COMPILER%" -j16 -o "%NOH_OUT%\NSE_NOH_TorusMass.olean" "%NOH_TORUS_MASS_SOURCE%" > "%NOH_OUT%\run-torus-mass.log" 2>&1
set "NOH_TORUS_MASS_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-torus-mass.log"
if not "%NOH_TORUS_MASS_EXIT%"=="0" (
  echo TORUS_MASS_BUILD=FAIL
  echo TORUS_MASS_LOG="%NOH_OUT%\run-torus-mass.log"
  echo UNCONDITIONAL_NSE_NOH=OPEN
  exit /b %NOH_TORUS_MASS_EXIT%
)
if not exist "%NOH_OUT%\NSE_NOH_TorusMass.olean" (
  echo TORUS_MASS_BUILD=FAIL_NO_OLEAN
  exit /b 27
)
echo TORUS_MASS_BUILD=PASS

rem FIX16 rough L2 pullback isometries and strong trace transfer.
if exist "%NOH_OUT%\NSE_NOH_L2Pullback.olean" del /q "%NOH_OUT%\NSE_NOH_L2Pullback.olean" >nul 2>&1
"%NOH_COMPILER%" -j16 -o "%NOH_OUT%\NSE_NOH_L2Pullback.olean" "%NOH_L2_SOURCE%" > "%NOH_OUT%\run-l2-pullback.log" 2>&1
set "NOH_L2_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-l2-pullback.log"
if not "%NOH_L2_EXIT%"=="0" (
  echo L2_PULLBACK_BUILD=FAIL
  echo L2_PULLBACK_LOG="%NOH_OUT%\run-l2-pullback.log"
  echo UNCONDITIONAL_NSE_NOH=OPEN
  exit /b %NOH_L2_EXIT%
)
if not exist "%NOH_OUT%\NSE_NOH_L2Pullback.olean" (
  echo L2_PULLBACK_BUILD=FAIL_NO_OLEAN
  exit /b 29
)
echo L2_PULLBACK_BUILD=PASS

rem FIX17 closed-range proof and L2-limits of planar lifts.
if exist "%NOH_OUT%\NSE_NOH_L2Closure.olean" del /q "%NOH_OUT%\NSE_NOH_L2Closure.olean" >nul 2>&1
"%NOH_COMPILER%" -j16 -o "%NOH_OUT%\NSE_NOH_L2Closure.olean" "%NOH_L2_CLOSURE_SOURCE%" > "%NOH_OUT%\run-l2-closure.log" 2>&1
set "NOH_L2_CLOSURE_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-l2-closure.log"
if not "%NOH_L2_CLOSURE_EXIT%"=="0" (
  echo L2_CLOSURE_BUILD=FAIL
  echo L2_CLOSURE_LOG="%NOH_OUT%\run-l2-closure.log"
  echo UNCONDITIONAL_NSE_NOH=OPEN
  exit /b %NOH_L2_CLOSURE_EXIT%
)
if not exist "%NOH_OUT%\NSE_NOH_L2Closure.olean" (
  echo L2_CLOSURE_BUILD=FAIL_NO_OLEAN
  exit /b 31
)
echo L2_CLOSURE_BUILD=PASS
rem FIX20 complex Fourier plane factorization using Mathlib genuine mFourier L2 basis.
if exist "%NOH_OUT%\NSE_NOH_FourierSpectral.olean" del /q "%NOH_OUT%\NSE_NOH_FourierSpectral.olean" >nul 2>&1
"%NOH_COMPILER%" -j16 -o "%NOH_OUT%\NSE_NOH_FourierSpectral.olean" "%NOH_FOURIER_SOURCE%" > "%NOH_OUT%\run-fourier-spectral.log" 2>&1
set "NOH_FOURIER_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-fourier-spectral.log"
if not "%NOH_FOURIER_EXIT%"=="0" (
  echo FOURIER_SPECTRAL_BUILD=FAIL
  echo FOURIER_SPECTRAL_LOG="%NOH_OUT%\run-fourier-spectral.log"
  echo UNCONDITIONAL_NSE_NOH=OPEN
  exit /b %NOH_FOURIER_EXIT%
)
if not exist "%NOH_OUT%\NSE_NOH_FourierSpectral.olean" (
  echo FOURIER_SPECTRAL_BUILD=FAIL_NO_OLEAN
  exit /b 33
)
echo FOURIER_SPECTRAL_BUILD=PASS

rem FIX21 independent actual-torus Fourier weak-mode integral test.
if exist "%NOH_OUT%\NSE_NOH_FourierWeakTest.olean" del /q "%NOH_OUT%\NSE_NOH_FourierWeakTest.olean" >nul 2>&1
"%NOH_COMPILER%" -j16 -o "%NOH_OUT%\NSE_NOH_FourierWeakTest.olean" "%NOH_FOURIER_TEST_SOURCE%" > "%NOH_OUT%\run-fourier-weak-test.log" 2>&1
set "NOH_FOURIER_TEST_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-fourier-weak-test.log"
if not "%NOH_FOURIER_TEST_EXIT%"=="0" (
  echo FOURIER_WEAK_TEST_BUILD=FAIL
  echo FOURIER_WEAK_TEST_LOG="%NOH_OUT%\run-fourier-weak-test.log"
  echo UNCONDITIONAL_NSE_NOH=OPEN
  exit /b %NOH_FOURIER_TEST_EXIT%
)
if not exist "%NOH_OUT%\NSE_NOH_FourierWeakTest.olean" (
  echo FOURIER_WEAK_TEST_BUILD=FAIL_NO_OLEAN
  exit /b 35
)
echo FOURIER_WEAK_TEST_BUILD=PASS
echo PROJECT_BUILD=PASS

"%NOH_COMPILER%" -j16 "%NOH_AUDIT_SOURCE%" > "%NOH_OUT%\run-audit.log" 2>&1
set "NOH_AUDIT_EXIT=%ERRORLEVEL%"
type "%NOH_OUT%\run-audit.log"
if not "%NOH_AUDIT_EXIT%"=="0" (
  echo AUDIT_ELABORATION=FAIL
  echo AUDIT_LOG="%NOH_OUT%\run-audit.log"
  exit /b %NOH_AUDIT_EXIT%
)
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-audit.log" >nul
if not errorlevel 1 (
  echo AXIOM_AUDIT=FAIL_SORRYAX
  exit /b 11
)
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-modes.log" >nul
if not errorlevel 1 (echo AXIOM_AUDIT=FAIL_SORRYAX_IN_MODES & exit /b 17)
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-jet.log" >nul
if not errorlevel 1 (echo AXIOM_AUDIT=FAIL_SORRYAX_IN_JET & exit /b 18)
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-derivative.log" >nul
if not errorlevel 1 (echo AXIOM_AUDIT=FAIL_SORRYAX_IN_DERIVATIVE & exit /b 20)
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-laplacian.log" >nul
if not errorlevel 1 (echo AXIOM_AUDIT=FAIL_SORRYAX_IN_LAPLACIAN & exit /b 23)
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-classical.log" >nul
if not errorlevel 1 (echo AXIOM_AUDIT=FAIL_SORRYAX_IN_CLASSICAL & exit /b 24)
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-energy.log" >nul
if not errorlevel 1 (echo AXIOM_AUDIT=FAIL_SORRYAX_IN_ENERGY & exit /b 26)
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-torus-mass.log" >nul
if not errorlevel 1 (echo AXIOM_AUDIT=FAIL_SORRYAX_IN_TORUS_MASS & exit /b 28)
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-l2-pullback.log" >nul
if not errorlevel 1 (echo AXIOM_AUDIT=FAIL_SORRYAX_IN_L2_PULLBACK & exit /b 30)
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-l2-closure.log" >nul
if not errorlevel 1 (echo AXIOM_AUDIT=FAIL_SORRYAX_IN_L2_CLOSURE & exit /b 32)
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-fourier-spectral.log" >nul
if not errorlevel 1 (echo AXIOM_AUDIT=FAIL_SORRYAX_IN_FOURIER_SPECTRAL & exit /b 34)
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-fourier-weak-test.log" >nul
if not errorlevel 1 (echo AXIOM_AUDIT=FAIL_SORRYAX_IN_FOURIER_WEAK_TEST & exit /b 36)
rem Raw no-sorryAx is not equivalent to a closed theorem or to a full axiom whitelist.
echo CONDITIONAL_THEOREM_AUDIT=RECORDED
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-build.log" >nul
if not errorlevel 1 (
  echo AXIOM_AUDIT=FAIL_SORRYAX_IN_BUILD
  exit /b 12
)
findstr.exe /I /C:"sorryAx" "%NOH_OUT%\run-geometry.log" >nul
if not errorlevel 1 (
  echo AXIOM_AUDIT=FAIL_SORRYAX_IN_GEOMETRY
  exit /b 14
)
echo AXIOM_AUDIT_NO_SORRYAX=PASS

findstr.exe /I /C:"does not depend on any axioms" "%NOH_OUT%\run-audit.log" >nul
if not errorlevel 1 (
  echo CONDITIONAL_THEOREM_NO_AXIOMS=PASS
) else (
  echo CONDITIONAL_THEOREM_AXIOMS=REVIEW_run-audit.log
)
echo THEOREM_LEVEL_AXIOM_WHITELIST=INSPECT_run-audit.log
echo RUN=PASS_GEOMETRY_MODES_JET_DERIVATIVE_LAPLACIAN_CLASSICAL_ENERGY_TORUS_MASS_L2_PULLBACK_L2_CLOSURE_FOURIER_SPECTRAL_FOURIER_WEAK_TEST_AND_CONDITIONAL_ASSEMBLY_ONLY
echo GEOMETRY_ENDPOINTS=CHECKED_IF_AUDIT_STANDARD_ONLY
 echo MODE_AND_JET_ENDPOINTS=CHECKED_IF_AUDIT_STANDARD_ONLY
echo DERIVATIVE_ENDPOINTS=CHECKED_IF_AUDIT_STANDARD_ONLY
echo LAPLACIAN_ENDPOINTS=CHECKED_IF_AUDIT_STANDARD_ONLY
echo CLASSICAL_PDE_LIFT_ENDPOINT=CHECKED_IF_AUDIT_STANDARD_ONLY
echo ENERGY_DENSITY_ENDPOINTS=CHECKED_IF_AUDIT_STANDARD_ONLY
echo TORUS_MASS_ENDPOINTS=CHECKED_IF_AUDIT_STANDARD_ONLY
echo L2_PULLBACK_ENDPOINTS=CHECKED_IF_AUDIT_STANDARD_ONLY
echo L2_CLOSURE_ENDPOINTS=CHECKED_IF_AUDIT_STANDARD_ONLY
echo FOURIER_SPECTRAL_ENDPOINTS=CHECKED_IF_AUDIT_STANDARD_ONLY
echo FOURIER_WEAK_TEST_ENDPOINTS=CHECKED_IF_AUDIT_STANDARD_ONLY
echo ANALYTIC_PDE_PORTS=OPEN
echo UNCONDITIONAL_NSE_NOH=OPEN
echo A_TIER=NOT_ESTABLISHED
exit /b 0

:tryCompiler
if defined NOH_COMPILER exit /b 0
set "NOH_TRY=%~1"
if not exist "%NOH_TRY%" exit /b 0
"%NOH_TRY%" --version > "%NOH_OUT%\probe-version.log" 2>&1
if errorlevel 1 exit /b 0
findstr.exe /L /C:"Lean (version 4.33.0" "%NOH_OUT%\probe-version.log" >nul
if not errorlevel 1 set "NOH_COMPILER_VERSION=4.33.0"
if not defined NOH_COMPILER_VERSION (
  findstr.exe /L /C:"Lean (version 4.34.0-rc1" "%NOH_OUT%\probe-version.log" >nul
  if not errorlevel 1 set "NOH_COMPILER_VERSION=4.34.0-rc1"
)
if not defined NOH_COMPILER_VERSION exit /b 0
findstr.exe /L /C:"x86_64-w64-windows-gnu" "%NOH_OUT%\probe-version.log" >nul
if errorlevel 1 (
  set "NOH_COMPILER_VERSION="
  exit /b 0
)
set "NOH_COMPILER=%NOH_TRY%"
exit /b 0

:tryCache
if defined NOH_CACHE exit /b 0
set "NOH_TRY_CACHE=%~1"
if not exist "%NOH_TRY_CACHE%\" exit /b 0
set "NOH_CACHE_PIN=%NOH_TRY_CACHE%\lean-toolchain"
if not exist "%NOH_CACHE_PIN%" set "NOH_CACHE_PIN=%NOH_TRY_CACHE%\.lake\packages\mathlib\lean-toolchain"
if exist "%NOH_CACHE_PIN%" (
  findstr.exe /L /C:"v%NOH_COMPILER_VERSION%" "%NOH_CACHE_PIN%" >nul
  if errorlevel 1 exit /b 0
)
set "NOH_TRY_LIB=%NOH_TRY_CACHE%\.lake\packages\mathlib\.lake\build\lib\lean"
if not exist "%NOH_TRY_LIB%\Mathlib.olean" set "NOH_TRY_LIB=%NOH_TRY_CACHE%\.lake\build\lib\lean"
if not exist "%NOH_TRY_LIB%\Mathlib.olean" set "NOH_TRY_LIB=%NOH_TRY_CACHE%\build\lib\lean"
if not exist "%NOH_TRY_LIB%\Mathlib.olean" exit /b 0
set "NOH_CACHE=%NOH_TRY_CACHE%"
set "NOH_MATHLIB=%NOH_TRY_LIB%"
exit /b 0
