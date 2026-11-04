@echo off
setlocal
echo STAGE_START=canonical_theta_root
call "%~dp0HILBERT-SUPERIORITY-PNT\run.cmd"
if errorlevel 1 exit /b 1
echo STAGE_START=zetahyperbolic_integration
call "%~dp0HILBERT-SUPERIORITY-PNT\zetahyperbolic-integration\run.cmd"
if errorlevel 1 exit /b 1
echo COMBINED_RESULT=PASS
exit /b 0

