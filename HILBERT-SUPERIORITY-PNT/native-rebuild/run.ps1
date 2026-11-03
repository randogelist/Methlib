param(
  [string]$MathlibCacheRoot = $env:MATHLIB_CACHE_ROOT,
  [string]$LeanExe = $env:LEAN_EXE,
  [switch]$TraceDependencies
)
$ErrorActionPreference = 'Stop'
$nativeModules = Join-Path $env:SystemRoot 'System32\WindowsPowerShell\v1.0\Modules'
if (Test-Path -LiteralPath $nativeModules -PathType Container) { $env:PSModulePath = "$nativeModules;$env:PSModulePath" }
$pkg = $PSScriptRoot
$tag = (Get-Date -Format 'yyyyMMdd-HHmmss-fff') + '-' + [Guid]::NewGuid().ToString('N').Substring(0,8)
$ev = Join-Path $pkg ('evidence\' + $tag)
$ol = Join-Path $ev 'olean'
New-Item -ItemType Directory -Force -Path $ol | Out-Null
Write-Host "EVIDENCE=$ev"
function Fail([string]$why) {
  @('RESULT=FAIL', ('REASON=' + $why)) | Set-Content -LiteralPath (Join-Path $ev 'result.txt') -Encoding UTF8
  Write-Host 'RESULT=FAIL'; Write-Host ('REASON=' + $why); exit 1
}
function Write-Utf8([string]$path, [string]$value) {
  [IO.File]::WriteAllText($path, $value, [System.Text.UTF8Encoding]::new($false))
}
try {
  $manifest = Join-Path $pkg 'sources.sha256'
  if (-not (Test-Path -LiteralPath $manifest -PathType Leaf)) { Fail 'Missing_source_hash_manifest' }
  $checks = @{}
  foreach ($line in @(Get-Content -LiteralPath $manifest -Encoding UTF8)) {
    if ([string]::IsNullOrWhiteSpace($line)) { continue }
    if ($line -notmatch '^([0-9a-fA-F]{64})  (plan\.json|candidates/[A-Za-z_][A-Za-z0-9_]*\.lean)$') { Fail 'Malformed_source_hash_manifest' }
    $expected = $Matches[1].ToLowerInvariant(); $name = $Matches[2]
    if ($checks.ContainsKey($name)) { Fail 'Duplicate_source_manifest_entry' }
    $checks[$name] = $expected
    $file = Join-Path $pkg ($name.Replace('/', '\'))
    if (-not (Test-Path -LiteralPath $file -PathType Leaf)) { Fail ('Missing_source_' + $name) }
    if ((Get-FileHash -LiteralPath $file -Algorithm SHA256).Hash.ToLowerInvariant() -ne $expected) { Fail ('Source_hash_mismatch_' + $name) }
  }
  if (-not $checks.ContainsKey('plan.json')) { Fail 'Plan_hash_missing' }
  $plan = Get-Content -LiteralPath (Join-Path $pkg 'plan.json') -Raw -Encoding UTF8 | ConvertFrom-Json
  if ($null -eq $plan -or $plan -isnot [System.Array] -or $plan.Count -eq 0) { Fail 'Plan_must_be_nonempty_array' }
  $mods = @{}; $theorems = @{}
  foreach ($entry in $plan) {
    $module = [string]$entry.module
    if ($module -notmatch '^[A-Za-z_][A-Za-z0-9_]*$' -or $mods.ContainsKey($module)) { Fail 'Invalid_or_duplicate_module' }
    $mods[$module] = $true
    if (-not $checks.ContainsKey(('candidates/' + $module + '.lean'))) { Fail ('Source_hash_missing_' + $module) }
    if (@($entry.names).Count -eq 0 -or @($entry.banned).Count -eq 0) { Fail ('Plan_names_or_bans_empty_' + $module) }
    foreach ($nm in @($entry.names)) {
      $name = [string]$nm
      if ($name -notmatch '^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)+$' -or $theorems.ContainsKey($name)) { Fail ('Invalid_or_duplicate_theorem_' + $name) }
      $theorems[$name] = $true
    }
    foreach ($nm in @($entry.banned)) {
      if ([string]$nm -notmatch '^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$') { Fail ('Invalid_forbidden_name_' + $nm) }
    }
  }
  if ($checks.Count -ne ($plan.Count + 1)) { Fail 'Unexpected_source_manifest_entry' }
  Copy-Item -LiteralPath $manifest -Destination (Join-Path $ev 'sources.sha256')
  Copy-Item -LiteralPath (Join-Path $pkg 'plan.json') -Destination (Join-Path $ev 'plan.json')
  Write-Host "SOURCE_HASHES=PASS CANDIDATE_COUNT=$($plan.Count) NAMED_THEOREMS=$($theorems.Count)"
  # Search only existing actual Lean binaries, not an elan shim.
  $leanCandidates = [System.Collections.Generic.List[string]]::new()
  if (-not [string]::IsNullOrWhiteSpace($LeanExe)) { $leanCandidates.Add($LeanExe) }
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
        if ((Test-Path -LiteralPath $c -PathType Leaf) -and -not $leanCandidates.Contains($c)) { $leanCandidates.Add($c) }
      }
    }
  }
  $selected = $null
  foreach ($c in $leanCandidates) {
    if (-not (Test-Path -LiteralPath $c -PathType Leaf)) { continue }
    $cPath = (Resolve-Path -LiteralPath $c).Path
    if ($cPath -match '(?i)[\\/]\.elan[\\/]bin[\\/]lean\.exe$') { continue }
    if (-not [string]::IsNullOrWhiteSpace($env:ELAN_HOME)) {
      $shim = Join-Path $env:ELAN_HOME 'bin\lean.exe'
      if ((Test-Path -LiteralPath $shim -PathType Leaf) -and $cPath -ieq (Resolve-Path -LiteralPath $shim).Path) { continue }
    }
    try {
      $v = (& $cPath --version 2>&1 | Out-String).Trim()
      if ($LASTEXITCODE -eq 0 -and $v -match '^Lean \(version 4\.34\.0-rc1,') { $selected = $cPath; $version = $v; break }
    } catch { }
  }
  if (-not $selected) { Fail 'Lean_4_34_0_rc1_not_runnable_set_LEAN_EXE' }
  $LeanExe = $selected; Write-Host "LEAN_EXE=$LeanExe"; Write-Host $version
  Set-Content -LiteralPath (Join-Path $ev 'lean-version.txt') -Value $version -Encoding UTF8
  if ([string]::IsNullOrWhiteSpace($MathlibCacheRoot)) { Fail 'Set_MATHLIB_CACHE_ROOT_to_cached_Mathlib_project_or_lib_lean' }
  if (-not (Test-Path -LiteralPath $MathlibCacheRoot -PathType Container)) { Fail 'MATHLIB_CACHE_ROOT_not_found' }
  $root = (Resolve-Path -LiteralPath $MathlibCacheRoot).Path
  $pathsToTry = @($root, (Join-Path $root '.lake\build\lib\lean'), (Join-Path $root '.lake\packages\mathlib\.lake\build\lib\lean'))
  $mathlib = $null
  foreach ($c in $pathsToTry) {
    if (Test-Path -LiteralPath (Join-Path $c 'Mathlib\Analysis\SpecialFunctions\Trigonometric\Basic.olean') -PathType Leaf) { $mathlib = (Resolve-Path $c).Path; break }
  }
  if (-not $mathlib) { Fail 'Cached_Mathlib_olean_not_found' }
  $paths = [System.Collections.Generic.List[string]]::new(); $paths.Add($ol); $paths.Add($mathlib)
  $parents = [System.Collections.Generic.List[string]]::new()
  foreach ($initial in @($root, $mathlib)) {
    $d = Get-Item -LiteralPath $initial
    while ($null -ne $d) { if (-not $parents.Contains($d.FullName)) { $parents.Add($d.FullName) }; $d = $d.Parent }
  }
  foreach ($p in $parents) {
    $packages = Join-Path $p '.lake\packages'
    if (Test-Path -LiteralPath $packages -PathType Container) {
      foreach ($dep in Get-ChildItem -LiteralPath $packages -Directory) {
        $lib = Join-Path $dep.FullName '.lake\build\lib\lean'
        if ((Test-Path -LiteralPath $lib -PathType Container) -and -not $paths.Contains($lib)) { $paths.Add($lib) }
      }
    }
  }
  $env:LEAN_PATH = $paths -join ';'; $paths | Set-Content -LiteralPath (Join-Path $ev 'lean-path.txt') -Encoding UTF8
  @("COMPILER_SHA256=$((Get-FileHash -LiteralPath $LeanExe -Algorithm SHA256).Hash.ToLowerInvariant())", "MANIFEST_SHA256=$((Get-FileHash -LiteralPath $manifest -Algorithm SHA256).Hash.ToLowerInvariant())", "MATHLIB_ROOT=$mathlib", "MATHLIB_WITNESS_SHA256=$((Get-FileHash -LiteralPath (Join-Path $mathlib 'Mathlib\Analysis\SpecialFunctions\Trigonometric\Basic.olean') -Algorithm SHA256).Hash.ToLowerInvariant())", 'MATHLIB_FULL_CACHE_PROVENANCE=USER_SUPPLIED_NOT_INDEPENDENTLY_VERIFIED', 'PROJECT_CACHE_REUSE=DISABLED') | Set-Content -LiteralPath (Join-Path $ev 'provenance.txt') -Encoding UTF8
  function Invoke-Lean([string[]]$arguments, [string]$name) {
    $stdout = Join-Path $ev ($name + '.stdout.log'); $stderr = Join-Path $ev ($name + '.stderr.log')
    Write-Host "STAGE_START=$name"
    Push-Location (Join-Path $pkg 'candidates')
    try { & $LeanExe @arguments 1> $stdout 2> $stderr; $code = $LASTEXITCODE } finally { Pop-Location }
    if ($code -ne 0) {
      Write-Host "STAGE_FAIL=$name"
      Get-Content -LiteralPath $stdout -ErrorAction SilentlyContinue | ForEach-Object { Write-Host $_ }
      Get-Content -LiteralPath $stderr -ErrorAction SilentlyContinue | ForEach-Object { Write-Host $_ }
      return $false
    }
    Write-Host "STAGE_PASS=$name"; return $true
  }
  $allOk = $true
  foreach ($entry in $plan) {
    $module = [string]$entry.module; $obj = Join-Path $ol ($module + '.olean')
    $sourceHash = $checks['candidates/' + $module + '.lean']
    Add-Content -LiteralPath (Join-Path $ev 'provenance.txt') -Value ("SOURCE_${module}_SHA256=" + $sourceHash)
    Write-Host "SOURCE_SHA256=$module $sourceHash"
    foreach ($nm in @($entry.names)) { Write-Host "THEOREM_ALIAS=$module $nm" }
    foreach ($target in @($entry.banned)) { Write-Host "TARGET_ALIAS=$module $target" }
    $built = Invoke-Lean @('-o', $obj, ($module + '.lean')) ('build_' + $module)
    if (-not $built -or -not (Test-Path -LiteralPath $obj -PathType Leaf)) { $allOk = $false; Write-Host "AUDIT_SKIPPED=$module"; continue }
    Add-Content -LiteralPath (Join-Path $ev 'provenance.txt') -Value ("OBJECT_${module}_SHA256=" + (Get-FileHash -LiteralPath $obj -Algorithm SHA256).Hash.ToLowerInvariant())
    $auditText = "import $module`n"
    foreach ($nm in @($entry.names)) { $auditText += "#check $nm`n#print axioms $nm`n" }
    $audit = Join-Path $ev ('Audit_' + $module + '.lean'); Write-Utf8 $audit $auditText
    $auditOk = Invoke-Lean @($audit) ('audit_' + $module)
    if (-not $auditOk) { $allOk = $false; continue }
    $log = Get-Content -LiteralPath (Join-Path $ev ('audit_' + $module + '.stdout.log')) -Raw
    foreach ($nm in @($entry.names)) {
      $pattern = "(?s)'" + [regex]::Escape([string]$nm) + "' (?:depends on axioms: \[(?<axs>[^\]]*)\]|(?<none>does not depend on any axioms))"
      $match = [regex]::Match($log, $pattern)
      if (-not $match.Success) { Write-Host "MISSING_AXIOM_REPORT=$nm"; $allOk = $false; continue }
      if (-not $match.Groups['none'].Success) {
        $axs = @($match.Groups['axs'].Value -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ })
        $bad = @($axs | Where-Object { $_ -notin @('propext','Classical.choice','Quot.sound') })
        if ($bad.Count -gt 0) { Write-Host "UNAPPROVED_AXIOM=$nm AXIOMS=$($bad -join ',')"; $allOk = $false; continue }
      }
      Write-Host "AXIOM_AUDIT_STANDARD_ONLY=$nm"
    }
    if ($TraceDependencies) {
      $idx = 0
      foreach ($nm in @($entry.names)) {
        $trace = Join-Path $ev ("Trace_${module}_${idx}.lean"); $idx++
        $quoted = @($entry.banned | ForEach-Object { '`' + [string]$_ }) -join ', '
        $text = "import $module`nimport ImportGraph.Imports.RequiredModules`nopen Lean Elab Command`nset_option maxHeartbeats 0 in`nrun_cmd do`n"
        $text += '  let root : Name := `' + [string]$nm + "`n"
        $text += '  let banned : Array Name := #[' + $quoted + "]`n"
        $text += '  let deps ← liftCoreM root.transitivelyUsedConstants' + "`n"
        $text += '  let env ← getEnv' + "`n"
        $text += '  for target in banned do' + "`n"
        $text += '    if (env.find? target).isNone then' + "`n"
        $text += '      IO.println s!"TARGET_UNKNOWN={target}"' + "`n"
        $text += '    else if root == target || deps.contains target then' + "`n"
        $text += '      IO.println s!"TARGET_FOUND={target}"' + "`n"
        $text += '    else' + "`n"
        $text += '      IO.println s!"TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={target}"' + "`n"
        Write-Utf8 $trace $text
        $traceStage = "trace_${module}_$($idx - 1)"
        if (Invoke-Lean @($trace) $traceStage) {
          $traceLog = Get-Content -LiteralPath (Join-Path $ev ($traceStage + '.stdout.log')) -Raw
          foreach ($line in @($traceLog -split "`r?`n")) {
            if ($line -match '^TARGET_(FOUND|UNKNOWN|NOT_SEEN_COVERAGE_UNVERIFIED)=') { Write-Host "DEPENDENCY_DIAGNOSTIC=$nm $line" }
            if ($line -match '^TARGET_FOUND=') { $allOk = $false }
          }
        } else { Write-Host "DEPENDENCY_TRACE_UNAVAILABLE=$nm" }
      }
    }
  }
  if (-not $TraceDependencies) { Write-Host 'DEPENDENCY_TRACE=NOT_REQUESTED' }
  Write-Host 'DEPENDENCY_COVERAGE=UNVERIFIED'
  if (-not $allOk) { Fail 'One_or_more_candidate_build_or_audit_stages_failed' }
  @('RESULT=PASS','SCOPE=NAMED_CANDIDATES_ONLY','AXIOM_AUDIT=STANDARD_ONLY','DEPENDENCY_COVERAGE=UNVERIFIED','MATHLIB_FULL_CACHE_PROVENANCE=USER_SUPPLIED_NOT_INDEPENDENTLY_VERIFIED') | Set-Content -LiteralPath (Join-Path $ev 'result.txt') -Encoding UTF8
  Write-Host 'RESULT=PASS'; Write-Host 'SCOPE=NAMED_CANDIDATES_ONLY'; Write-Host 'DEPENDENCY_COVERAGE=UNVERIFIED'; exit 0
} catch {
  ($_ | Out-String) | Set-Content -LiteralPath (Join-Path $ev 'exception.txt') -Encoding UTF8
  Write-Host ('RUNNER_ERROR=' + $_.Exception.Message)
  Fail 'Runner_exception_see_exception_txt'
}
