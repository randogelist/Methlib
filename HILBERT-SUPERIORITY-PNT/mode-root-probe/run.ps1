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
$objects = Join-Path $ev 'olean'
New-Item -ItemType Directory -Force -Path $objects | Out-Null
Write-Host "EVIDENCE=$ev"
function Fail([string]$reason) {
  @('RESULT=FAIL', ('REASON=' + $reason), 'SCOPE=NAMED_THEOREMS_ONLY',
    'DEPENDENCY_COVERAGE=UNVERIFIED') |
    Set-Content -LiteralPath (Join-Path $ev 'result.txt') -Encoding UTF8
  Write-Host 'RESULT=FAIL'
  Write-Host ('REASON=' + $reason)
  exit 1
}
function Write-Utf8([string]$path, [string]$value) {
  [IO.File]::WriteAllText($path, $value, [Text.UTF8Encoding]::new($false))
}
try {
  $planPath = Join-Path $pkg 'plan.json'
  $manifest = Join-Path $pkg 'sources.sha256'
  if (-not (Test-Path -LiteralPath $planPath -PathType Leaf) -or
      -not (Test-Path -LiteralPath $manifest -PathType Leaf)) { Fail 'Missing_plan_or_manifest' }
  $plan = @(Get-Content -LiteralPath $planPath -Raw -Encoding UTF8 | ConvertFrom-Json)
  if ($plan.Count -eq 0) { Fail 'Empty_plan' }
  $checks = @{}
  foreach ($line in @(Get-Content -LiteralPath $manifest -Encoding UTF8)) {
    if ($line -notmatch '^([0-9a-f]{64})  (plan\.json|sources/[A-Za-z_][A-Za-z0-9_]*\.lean)$') {
      Fail 'Malformed_source_manifest'
    }
    $expected = $Matches[1]; $relative = $Matches[2]
    if ($checks.ContainsKey($relative)) { Fail 'Duplicate_manifest_entry' }
    $checks[$relative] = $expected
    $src = Join-Path $pkg ($relative.Replace('/', '\'))
    if (-not (Test-Path -LiteralPath $src -PathType Leaf)) { Fail ('Missing_source_' + $relative) }
    if ((Get-FileHash -LiteralPath $src -Algorithm SHA256).Hash.ToLowerInvariant() -ne $expected) {
      Fail ('Source_hash_mismatch_' + $relative)
    }
  }
  $mods = @{}; $theoremNames = @{}
  if (-not $checks.ContainsKey('plan.json')) { Fail 'Missing_plan_hash' }
  foreach ($entry in $plan) {
    $keys = @($entry.PSObject.Properties.Name | Sort-Object)
    if (($keys -join ',') -ne 'module,theorems') { Fail 'Invalid_plan_entry_keys' }
    $module = [string]$entry.module
    if ($module -notmatch '^[A-Za-z_][A-Za-z0-9_]*$' -or $mods.ContainsKey($module)) {
      Fail 'Invalid_or_duplicate_module'
    }
    $mods[$module] = $true
    if (-not $checks.ContainsKey(('sources/' + $module + '.lean'))) { Fail ('Missing_module_hash_' + $module) }
    if ($null -eq $entry.theorems -or $entry.theorems -isnot [System.Array]) {
      Fail ('Invalid_theorems_array_' + $module)
    }
    foreach ($n in $entry.theorems) {
      $name = [string]$n
      if ($name -notmatch '^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)+$' -or
          $theoremNames.ContainsKey($name)) { Fail 'Invalid_or_duplicate_theorem' }
      $theoremNames[$name] = $true
    }
  }
  if ($theoremNames.Count -eq 0 -or $checks.Count -ne ($mods.Count + 1)) {
    Fail 'Empty_theorems_or_unexpected_manifest_entries'
  }
  $sourceFiles = @(Get-ChildItem -LiteralPath (Join-Path $pkg 'sources') -Filter '*.lean' -File)
  if ($sourceFiles.Count -ne $mods.Count) { Fail 'Source_files_do_not_match_plan' }
  Write-Host "SOURCE_HASHES=PASS MODULES=$($mods.Count) NAMED_THEOREMS=$($theoremNames.Count)"

  $leanCandidates = [Collections.Generic.List[string]]::new()
  if (-not [string]::IsNullOrWhiteSpace($LeanExe)) { $leanCandidates.Add($LeanExe) }
  $toolroots = [Collections.Generic.List[string]]::new()
  if (-not [string]::IsNullOrWhiteSpace($env:ELAN_HOME)) { $toolroots.Add((Join-Path $env:ELAN_HOME 'toolchains')) }
  if (-not [string]::IsNullOrWhiteSpace($env:USERPROFILE)) {
    $defaultRoot = Join-Path $env:USERPROFILE '.elan\toolchains'
    if (-not $toolroots.Contains($defaultRoot)) { $toolroots.Add($defaultRoot) }
  }
  foreach ($base in $toolroots) {
    if (Test-Path -LiteralPath $base -PathType Container) {
      foreach ($dir in @(Get-ChildItem -LiteralPath $base -Directory | Sort-Object Name)) {
        $bin = Join-Path $dir.FullName 'bin\lean.exe'
        if ((Test-Path -LiteralPath $bin -PathType Leaf) -and -not $leanCandidates.Contains($bin)) {
          $leanCandidates.Add($bin)
        }
      }
    }
  }
  $selected = $null
  foreach ($candidate in $leanCandidates) {
    if (-not (Test-Path -LiteralPath $candidate -PathType Leaf)) { continue }
    $resolved = (Resolve-Path -LiteralPath $candidate).Path
    if ($resolved -match '(?i)[\\/]\.elan[\\/]bin[\\/]lean\.exe$') { continue }
    try {
      $version = (& $resolved --version 2>&1 | Out-String).Trim()
      if ($LASTEXITCODE -eq 0 -and $version -match '^Lean \(version 4\.34\.0-rc1,') {
        $selected = $resolved
        break
      }
    } catch { }
  }
  if (-not $selected) { Fail 'Native_Lean_4_34_0_rc1_not_found_set_LEAN_EXE' }
  $LeanExe = $selected
  Write-Host "LEAN_EXE=$LeanExe"
  Write-Host $version
  Set-Content -LiteralPath (Join-Path $ev 'lean-version.txt') -Value $version -Encoding UTF8

  if ([string]::IsNullOrWhiteSpace($MathlibCacheRoot)) {
    Fail 'Set_MATHLIB_CACHE_ROOT_to_existing_cached_Mathlib'
  }
  if (-not (Test-Path -LiteralPath $MathlibCacheRoot -PathType Container)) {
    Fail 'MATHLIB_CACHE_ROOT_not_found'
  }
  $cache = (Resolve-Path -LiteralPath $MathlibCacheRoot).Path
  $tries = @($cache, (Join-Path $cache '.lake\build\lib\lean'),
    (Join-Path $cache '.lake\packages\mathlib\.lake\build\lib\lean'))
  $mathlib = $null
  $witnessRel = 'Mathlib\Analysis\SpecialFunctions\Trigonometric\Basic.olean'
  foreach ($candidate in $tries) {
    if (Test-Path -LiteralPath (Join-Path $candidate $witnessRel) -PathType Leaf) {
      $mathlib = (Resolve-Path -LiteralPath $candidate).Path
      break
    }
  }
  if (-not $mathlib) { Fail 'Cached_Mathlib_olean_not_found' }
  $paths = [Collections.Generic.List[string]]::new()
  $paths.Add($objects); $paths.Add($mathlib)
  $parents = [Collections.Generic.List[string]]::new()
  foreach ($start in @($cache, $mathlib)) {
    $d = Get-Item -LiteralPath $start
    while ($null -ne $d) {
      if (-not $parents.Contains($d.FullName)) { $parents.Add($d.FullName) }
      $d = $d.Parent
    }
  }
  foreach ($p in $parents) {
    $packages = Join-Path $p '.lake\packages'
    if (Test-Path -LiteralPath $packages -PathType Container) {
      foreach ($dep in @(Get-ChildItem -LiteralPath $packages -Directory)) {
        $lib = Join-Path $dep.FullName '.lake\build\lib\lean'
        if ((Test-Path -LiteralPath $lib -PathType Container) -and -not $paths.Contains($lib)) {
          $paths.Add($lib)
        }
      }
    }
  }
  $env:LEAN_PATH = $paths -join ';'
  $paths | Set-Content -LiteralPath (Join-Path $ev 'lean-path.txt') -Encoding UTF8
  @(
    "COMPILER_SHA256=$((Get-FileHash -LiteralPath $LeanExe -Algorithm SHA256).Hash.ToLowerInvariant())",
    "MANIFEST_SHA256=$((Get-FileHash -LiteralPath $manifest -Algorithm SHA256).Hash.ToLowerInvariant())",
    "MATHLIB_WITNESS_SHA256=$((Get-FileHash -LiteralPath (Join-Path $mathlib $witnessRel) -Algorithm SHA256).Hash.ToLowerInvariant())",
    'MATHLIB_FULL_CACHE_PROVENANCE=USER_SUPPLIED_NOT_INDEPENDENTLY_VERIFIED',
    'PROJECT_OBJECTS_REBUILT=YES',
    'DEPENDENCY_TRACE=NOT_REQUESTED',
    'DEPENDENCY_COVERAGE=UNVERIFIED'
  ) | Set-Content -LiteralPath (Join-Path $ev 'provenance.txt') -Encoding UTF8

  function Invoke-Lean([string[]]$arguments, [string]$name) {
    $stdout = Join-Path $ev ($name + '.stdout.log')
    $stderr = Join-Path $ev ($name + '.stderr.log')
    Write-Host "STAGE_START=$name"
    Push-Location (Join-Path $pkg 'sources')
    try { & $LeanExe @arguments 1> $stdout 2> $stderr; $code = $LASTEXITCODE }
    finally { Pop-Location }
    if ($code -ne 0) {
      Write-Host "STAGE_FAIL=$name"
      Get-Content -LiteralPath $stdout -ErrorAction SilentlyContinue | ForEach-Object { Write-Host $_ }
      Get-Content -LiteralPath $stderr -ErrorAction SilentlyContinue | ForEach-Object { Write-Host $_ }
      return $false
    }
    Write-Host "STAGE_PASS=$name"
    return $true
  }
  foreach ($entry in $plan) {
    $module = [string]$entry.module
    $obj = Join-Path $objects ($module + '.olean')
    if (-not (Invoke-Lean @('-o', $obj, ($module + '.lean')) ('build_' + $module)) -or
        -not (Test-Path -LiteralPath $obj -PathType Leaf)) { Fail ('Build_failed_' + $module) }
    Add-Content -LiteralPath (Join-Path $ev 'provenance.txt') -Value ("OBJECT_" + $module + "_SHA256=" + (Get-FileHash -LiteralPath $obj -Algorithm SHA256).Hash.ToLowerInvariant())
    if ($entry.theorems.Count -eq 0) { continue }
    $text = "import $module`n"
    foreach ($name in $entry.theorems) { $text += "#check $name`n#print axioms $name`n" }
    $audit = Join-Path $ev ('Audit_' + $module + '.lean')
    Write-Utf8 $audit $text
    if (-not (Invoke-Lean @($audit) ('audit_' + $module))) { Fail ('Audit_failed_' + $module) }
    $log = Get-Content -LiteralPath (Join-Path $ev ('audit_' + $module + '.stdout.log')) -Raw
    foreach ($name in $entry.theorems) {
      $pattern = "(?s)'" + [regex]::Escape([string]$name) +
        "' (?:depends on axioms: \[(?<axs>[^\]]*)\]|(?<none>does not depend on any axioms))"
      $match = [regex]::Match($log, $pattern)
      if (-not $match.Success) { Fail ('Missing_axiom_report_' + $name) }
      if (-not $match.Groups['none'].Success) {
        $axioms = @($match.Groups['axs'].Value -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ })
        $bad = @($axioms | Where-Object { $_ -notin @('propext','Classical.choice','Quot.sound') })
        if ($bad.Count -gt 0) { Fail ('Unapproved_axiom_' + $name + '_' + ($bad -join ',')) }
      }
      Write-Host "AXIOM_AUDIT_STANDARD_ONLY=$name"
    }
  }
  @('RESULT=PASS', 'SCOPE=NAMED_THEOREMS_ONLY', 'AXIOM_AUDIT=STANDARD_ONLY',
    'DEPENDENCY_TRACE=NOT_REQUESTED', 'DEPENDENCY_COVERAGE=UNVERIFIED',
    'MATHLIB_FULL_CACHE_PROVENANCE=USER_SUPPLIED_NOT_INDEPENDENTLY_VERIFIED') |
    Set-Content -LiteralPath (Join-Path $ev 'result.txt') -Encoding UTF8
  Write-Host 'RESULT=PASS'
  Write-Host 'SCOPE=NAMED_THEOREMS_ONLY'
  Write-Host 'DEPENDENCY_TRACE=NOT_REQUESTED'
  Write-Host 'DEPENDENCY_COVERAGE=UNVERIFIED'
  exit 0
} catch {
  ($_ | Out-String) | Set-Content -LiteralPath (Join-Path $ev 'exception.txt') -Encoding UTF8
  Write-Host ('RUNNER_ERROR=' + $_.Exception.Message)
  Fail 'Runner_exception_see_exception_txt'
}

