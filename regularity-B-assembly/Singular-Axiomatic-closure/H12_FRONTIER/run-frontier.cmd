@echo off
setlocal EnableExtensions
cd /d "%~dp0"
set PYTHONUTF8=1
set PYTHONIOENCODING=utf-8
set MATHLIB_NO_CACHE_ON_UPDATE=1
where lake >nul 2>nul
if errorlevel 1 (
  echo ERROR: elan and Lake are required.
  exit /b 1
)
where python >nul 2>nul
if errorlevel 1 (
  echo ERROR: Python 3 is required.
  exit /b 1
)
where git >nul 2>nul
if errorlevel 1 (
  echo ERROR: Git is required for the pinned dependency audit.
  exit /b 1
)
if not exist evidence mkdir evidence
python -c "import hashlib,pathlib; pathlib.Path('evidence/lockfile-before.sha256').write_text(hashlib.sha256(pathlib.Path('lake-manifest.json').read_bytes()).hexdigest())"
if errorlevel 1 goto fail
call lake env lean --version > evidence\lean-version.txt 2>&1
if errorlevel 1 goto fail
type evidence\lean-version.txt
findstr /C:"version 4.33.0," evidence\lean-version.txt >nul
if errorlevel 1 goto fail
python ci\test_check_axioms.py > evidence\audit-checker-tests.log 2>&1
if errorlevel 1 goto fail
call lake exe cache get > evidence\cache.log 2>&1
if errorlevel 1 goto fail
git -C .lake\packages\mathlib rev-parse HEAD > evidence\mathlib-revision.txt
if errorlevel 1 goto fail
set /p FRONTIER_MATHLIB_REV=<evidence\mathlib-revision.txt
if not "%FRONTIER_MATHLIB_REV%"=="db584cd6d46c92f209a44c0f1c829460d327499d" goto fail
python -c "import hashlib,pathlib; assert hashlib.sha256(pathlib.Path('lake-manifest.json').read_bytes()).hexdigest()==pathlib.Path('evidence/lockfile-before.sha256').read_text().strip(), 'lockfile changed'"
if errorlevel 1 goto fail
python ci\assemble_frontier_replay.py
if errorlevel 1 goto fail
python ci\build_frontier.py
if errorlevel 1 goto fail
call lake build SingularClosure.SmallDataClosure > evidence\base-build.log 2>&1
if errorlevel 1 goto fail
call lake env lean ci\critical_audits\SmallDataClosure.lean > evidence\base-axioms.log 2>&1
if errorlevel 1 goto fail
python ci\check_axioms.py evidence\base-axioms.log ci\critical_audits\SmallDataClosure.json > evidence\base-audit.json 2>&1
if errorlevel 1 goto fail
type evidence\base-audit.json
echo PASS: frontier compiler, exact-type and axiom audits; base regression PASS.
echo Evidence: evidence\frontier\results.json and per-declaration transcripts.
echo No cache directory was deleted. No GitHub token or publication is required.
exit /b 0
:fail
echo FAIL: inspect evidence and evidence\frontier.
exit /b 1
