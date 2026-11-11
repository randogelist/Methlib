@echo off
setlocal
where gh >nul 2>nul
if errorlevel 1 (
  echo GitHub CLI is required to dispatch the external CI run.
  exit /b 1
)
gh workflow run singular-axiomatic-closure.yml --repo randogelist/Methlib --ref main
if errorlevel 1 exit /b 1
echo CI workflow dispatched. No Lean execution occurred on this computer.
gh run list --repo randogelist/Methlib --workflow singular-axiomatic-closure.yml --branch main --limit 3
exit /b %ERRORLEVEL%
