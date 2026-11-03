param(
  [string]$MathlibCacheRoot = $env:MATHLIB_CACHE_ROOT,
  [string]$LeanExe = $env:LEAN_EXE
)
$ErrorActionPreference = 'Stop'
$nativeModules = Join-Path $env:SystemRoot 'System32\WindowsPowerShell\v1.0\Modules'
if (Test-Path -LiteralPath $nativeModules -PathType Container) {
  $env:PSModulePath = "$nativeModules;$env:PSModulePath"
}
$pkg = $PSScriptRoot
$tag = (Get-Date -Format 'yyyyMMdd-HHmmss-fff') + '-' + [Guid]::NewGuid().ToString('N').Substring(0,8)
$ev = Join-Path $pkg ('evidence\' + $tag)
$ol = Join-Path $ev 'olean'
New-Item -ItemType Directory -Force -Path $ol | Out-Null
Write-Host "EVIDENCE=$ev"
function Fail([string]$why) {
  @('RESULT=FAIL', "REASON=$why") | Set-Content -LiteralPath (Join-Path $ev 'result.txt') -Encoding UTF8
  Write-Host 'RESULT=FAIL'
  Write-Host "REASON=$why"
  exit 1
}
try {
  $planFile = Join-Path $pkg 'audit-plan.json'
  $checksumFile = Join-Path $pkg 'sources.sha256'
  if (-not (Test-Path -LiteralPath $planFile -PathType Leaf)) { Fail 'Missing_audit_plan' }
  if (-not (Test-Path -LiteralPath $checksumFile -PathType Leaf)) { Fail 'Missing_source_hash_manifest' }
  $plan = @(Get-Content -LiteralPath $planFile -Raw -Encoding UTF8 | ConvertFrom-Json)
  if ($plan.Count -eq 0) { Fail 'Empty_audit_plan' }
  $checks = @{}
  foreach ($line in @(Get-Content -LiteralPath $checksumFile -Encoding UTF8)) {
    if ([string]::IsNullOrWhiteSpace($line)) { continue }
    if ($line -notmatch '^([0-9a-fA-F]{64})\s+([A-Za-z0-9_.-]+)$') { Fail 'Malformed_source_hash_manifest' }
    $hash = $Matches[1].ToLowerInvariant(); $name = $Matches[2]
    if ($checks.ContainsKey($name)) { Fail 'Duplicate_source_hash' }
    $checks[$name] = $hash
    $path = Join-Path $pkg $name
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) { Fail ('Source_missing_' + $name) }
    if ((Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $hash) { Fail ('Source_hash_mismatch_' + $name) }
    Add-Content -LiteralPath (Join-Path $ev 'source-hashes.txt') -Value ($hash + '  ' + $name)
  }
  foreach ($required in @('run.cmd', 'run.ps1', 'audit-plan.json')) {
    if (-not $checks.ContainsKey($required)) { Fail ('Required_hash_missing_' + $required) }
  }
  $seen = @{}
  foreach ($entry in $plan) {
    $module = [string]$entry.module
    if ($module -notmatch '^[A-Za-z][A-Za-z0-9_]*$' -or $seen.ContainsKey($module)) { Fail 'Invalid_or_duplicate_plan_module' }
    $seen[$module] = $true
    if (-not $checks.ContainsKey($module + '.lean')) { Fail ('Required_hash_missing_' + $module) }
    $names = @($entry.names)
    if ($names.Count -eq 0) { Fail ('Empty_named_audit_' + $module) }
    foreach ($name in $names) {
      if ([string]$name -notmatch '^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)+$') { Fail 'Invalid_audit_declaration' }
    }
  }
  Write-Host 'SOURCE_HASHES=PASS'
  $candidates = [System.Collections.Generic.List[string]]::new()
  if (-not [string]::IsNullOrWhiteSpace($LeanExe)) { $candidates.Add($LeanExe) }
  $roots = [System.Collections.Generic.List[string]]::new()
  if (-not [string]::IsNullOrWhiteSpace($env:ELAN_HOME)) { $roots.Add((Join-Path $env:ELAN_HOME 'toolchains')) }
  if (-not [string]::IsNullOrWhiteSpace($env:USERPROFILE)) {
    $defaultRoot = Join-Path $env:USERPROFILE '.elan\toolchains'
    if (-not $roots.Contains($defaultRoot)) { $roots.Add($defaultRoot) }
  }
  foreach ($root in $roots) {
    if (Test-Path -LiteralPath $root -PathType Container) {
      foreach ($dir in @(Get-ChildItem -LiteralPath $root -Directory | Sort-Object Name)) {
        $c = Join-Path $dir.FullName 'bin\lean.exe'
        if ((Test-Path -LiteralPath $c -PathType Leaf) -and -not $candidates.Contains($c)) { $candidates.Add($c) }
      }
    }
  }
  $selected = $null
  foreach ($candidate in $candidates) {
    if (-not (Test-Path -LiteralPath $candidate -PathType Leaf)) { continue }
    $c = (Resolve-Path -LiteralPath $candidate).Path
    if ($c -match '(?i)[\\/]\.elan[\\/]bin[\\/]lean\.exe$') { continue }
    if (-not [string]::IsNullOrWhiteSpace($env:ELAN_HOME)) {
      $shim = Join-Path $env:ELAN_HOME 'bin\lean.exe'
      if ((Test-Path -LiteralPath $shim -PathType Leaf) -and $c -ieq (Resolve-Path -LiteralPath $shim).Path) { continue }
    }
    try {
      $version = (& $c --version 2>&1 | Out-String).Trim()
      if ($LASTEXITCODE -eq 0 -and $version -match '^Lean \(version 4\.34\.0-rc1,') { $selected = $c; break }
    } catch { continue }
  }
  if (-not $selected) { Fail 'Lean_4_34_0_rc1_not_found_set_LEAN_EXE' }
  $version | Set-Content -LiteralPath (Join-Path $ev 'lean-version.txt') -Encoding UTF8
  Write-Host "LEAN_EXE=$selected"
  Write-Host $version
  if ([string]::IsNullOrWhiteSpace($MathlibCacheRoot)) { Fail 'Set_MATHLIB_CACHE_ROOT_to_cached_Mathlib_project' }
  if (-not (Test-Path -LiteralPath $MathlibCacheRoot -PathType Container)) { Fail 'MATHLIB_CACHE_ROOT_not_found' }
  $root = (Resolve-Path -LiteralPath $MathlibCacheRoot).Path
  $ml = $null
  foreach ($c in @($root, (Join-Path $root '.lake\build\lib\lean'), (Join-Path $root '.lake\packages\mathlib\.lake\build\lib\lean'))) {
    if (Test-Path -LiteralPath (Join-Path $c 'Mathlib\Analysis\SpecialFunctions\Trigonometric\Basic.olean') -PathType Leaf) {
      $ml = (Resolve-Path -LiteralPath $c).Path; break
    }
  }
  if (-not $ml) { Fail 'Mathlib_cached_olean_not_found' }
  $paths = [System.Collections.Generic.List[string]]::new()
  $paths.Add($ol); $paths.Add($ml)
  $parents = [System.Collections.Generic.List[string]]::new()
  foreach ($initial in @($root, $ml)) {
    $d = Get-Item -LiteralPath $initial
    while ($null -ne $d) {
      if (-not $parents.Contains($d.FullName)) { $parents.Add($d.FullName) }
      $d = $d.Parent
    }
  }
  foreach ($parent in $parents) {
    $packages = Join-Path $parent '.lake\packages'
    if (Test-Path -LiteralPath $packages -PathType Container) {
      foreach ($dep in @(Get-ChildItem -LiteralPath $packages -Directory | Sort-Object Name)) {
        $lib = Join-Path $dep.FullName '.lake\build\lib\lean'
        if ((Test-Path -LiteralPath $lib -PathType Container) -and -not $paths.Contains($lib)) { $paths.Add($lib) }
      }
    }
  }
  $env:LEAN_PATH = $paths -join ';'
  $paths | Set-Content -LiteralPath (Join-Path $ev 'lean-path.txt') -Encoding UTF8
  @(
    "COMPILER_SHA256=$((Get-FileHash -LiteralPath $selected -Algorithm SHA256).Hash.ToLowerInvariant())"
    "MATHLIB_WITNESS_SHA256=$((Get-FileHash -LiteralPath (Join-Path $ml 'Mathlib\Analysis\SpecialFunctions\Trigonometric\Basic.olean') -Algorithm SHA256).Hash.ToLowerInvariant())"
    "MATHLIB_ROOT=$ml"
    'MATHLIB_CACHE_PROVENANCE=USER_SUPPLIED_NOT_FULLY_VERIFIED'
    'PROJECT_OLEANS=BUILT_FROM_SOURCE_IN_FRESH_EVIDENCE_DIRECTORY'
  ) | Set-Content -LiteralPath (Join-Path $ev 'provenance.txt') -Encoding UTF8
  Write-Host 'CACHE_REUSE=MATHLIB_USER_SUPPLIED_SOURCE_OBJECT_PROVENANCE_UNVERIFIED'
  function Invoke-Lean([string[]]$arguments, [string]$stage) {
    $stdout = Join-Path $ev ($stage + '.stdout.log')
    $stderr = Join-Path $ev ($stage + '.stderr.log')
    Write-Host "STAGE_START=$stage"
    Push-Location $pkg
    try { & $selected @arguments 1> $stdout 2> $stderr; $code = $LASTEXITCODE }
    finally { Pop-Location }
    if ($code -ne 0) {
      Write-Host "STAGE_FAIL=$stage"
      Get-Content -LiteralPath $stdout -ErrorAction SilentlyContinue | ForEach-Object { Write-Host $_ }
      Get-Content -LiteralPath $stderr -ErrorAction SilentlyContinue | ForEach-Object { Write-Host $_ }
      return $false
    }
    Write-Host "STAGE_PASS=$stage"
    return $true
  }
  $state = @{}
  $allOk = $true
  foreach ($entry in $plan) {
    $module = [string]$entry.module
    $object = Join-Path $ol ($module + '.olean')
    $blocked = $false
    foreach ($dep in @($entry.deps)) {
      if ($state[[string]$dep] -ne 'PASS') { Write-Host "BLOCKED=$module DEPENDENCY=$dep"; $blocked = $true }
    }
    if ($blocked) { $state[$module] = 'BLOCKED'; $allOk = $false; continue }
    if (-not (Invoke-Lean @('-o', $object, ($module + '.lean')) ('build_' + $module)) -or -not (Test-Path -LiteralPath $object -PathType Leaf)) {
      $state[$module] = 'FAIL'; $allOk = $false; continue
    }
    $state[$module] = 'PASS'
    Add-Content -LiteralPath (Join-Path $ev 'provenance.txt') -Value ("OBJECT_${module}_SHA256=" + (Get-FileHash -LiteralPath $object -Algorithm SHA256).Hash.ToLowerInvariant())
  }
  foreach ($entry in $plan) {
    $module = [string]$entry.module
    if ($state[$module] -ne 'PASS') { Write-Host "AUDIT_SKIPPED=$module BUILD=$($state[$module])"; $allOk = $false; continue }
    $audit = Join-Path $ev ('Audit_' + $module + '.lean')
    $auditLines = @('import ' + $module)
    foreach ($name in @($entry.names)) { $auditLines += '#check ' + [string]$name; $auditLines += '#print axioms ' + [string]$name }
    [System.IO.File]::WriteAllLines($audit, [string[]]$auditLines, [System.Text.UTF8Encoding]::new($false))
    Add-Content -LiteralPath (Join-Path $ev 'provenance.txt') -Value ("AUDIT_SOURCE_${module}_SHA256=" + (Get-FileHash -LiteralPath $audit -Algorithm SHA256).Hash.ToLowerInvariant())
    $stage = 'audit_' + $module
    if (-not (Invoke-Lean @($audit) $stage)) { $allOk = $false; continue }
    $log = Get-Content -LiteralPath (Join-Path $ev ($stage + '.stdout.log')) -Raw
    $auditOk = $true
    foreach ($name in @($entry.names)) {
      $pattern = "(?s)'" + [regex]::Escape([string]$name) + "' (?:depends on axioms: \[(?<axs>[^\]]*)\]|(?<none>does not depend on any axioms))"
      $reports = [regex]::Matches($log, $pattern)
      if ($reports.Count -ne 1) { Write-Host "MISSING_OR_DUPLICATE_AXIOM_REPORT=$name COUNT=$($reports.Count)"; $auditOk = $false; continue }
      $report = $reports[0]
      if (-not $report.Groups['none'].Success) {
        foreach ($ax in @($report.Groups['axs'].Value -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ })) {
          if ($ax -notin @('propext', 'Classical.choice', 'Quot.sound')) { Write-Host "UNAPPROVED_AXIOM=$name AXIOM=$ax"; $auditOk = $false }
        }
      }
      if ($auditOk) { Write-Host "AXIOM_AUDIT_STANDARD_ONLY=$name" }
    }
    if (-not $auditOk) { $allOk = $false; Write-Host "AXIOM_AUDIT_FAIL=$module" }
  }
  if (-not $allOk) { Fail 'One_or_more_build_or_audit_stages_failed' }
  @('RESULT=PASS', 'SCOPE=AMENDMENT_NAMED_THEOREMS_ONLY', 'AXIOM_AUDIT=STANDARD_ONLY', 'MATHLIB_CACHE_PROVENANCE=USER_SUPPLIED_NOT_FULLY_VERIFIED', 'INTEGRATION_WITH_PNT=NOT_ATTEMPTED') |
    Set-Content -LiteralPath (Join-Path $ev 'result.txt') -Encoding UTF8
  Write-Host 'RESULT=PASS'
  Write-Host 'SCOPE=AMENDMENT_NAMED_THEOREMS_ONLY'
  Write-Host 'AXIOM_AUDIT=STANDARD_ONLY'
  Write-Host 'INTEGRATION_WITH_PNT=NOT_ATTEMPTED'
  exit 0
} catch {
  ($_ | Out-String) | Set-Content -LiteralPath (Join-Path $ev 'runner-error.txt') -Encoding UTF8
  Write-Host ($_ | Out-String)
  Fail 'Runner_exception_see_runner-error.txt'
}
