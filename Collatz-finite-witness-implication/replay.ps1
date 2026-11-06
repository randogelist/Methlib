param(
  [Parameter(Mandatory=$true, Position=0)][string]$WitnessPath,
  [string]$MathlibCacheRoot = $env:MATHLIB_CACHE_ROOT,
  [string]$LeanExe = $env:LEAN_EXE,
  [ValidateRange(1,64)][int]$Threads = 16
)
$ErrorActionPreference = 'Stop'
$pkg = $PSScriptRoot
$src = Join-Path $pkg 'src'
$tag = (Get-Date -Format 'yyyyMMdd-HHmmss-fff') + '-' + [Guid]::NewGuid().ToString('N').Substring(0,8)
$ev = Join-Path $pkg ('evidence\' + $tag)
$ol = Join-Path $ev 'olean'
$logs = Join-Path $ev 'logs'
New-Item -ItemType Directory -Force -Path $ol,$logs | Out-Null
Write-Host "EVIDENCE=$ev"
function Write-Text([string]$path, [string]$text) {
  [IO.File]::WriteAllText($path, $text, [Text.UTF8Encoding]::new($false))
}
function Fail([string]$why) {
  Write-Text (Join-Path $ev 'result.txt') "RESULT=FAIL`r`nREASON=$why`r`nC_EQUIVALENCE=NOT_ESTABLISHED`r`nWITNESS_VERIFICATION=NOT_COMPLETED`r`n"
  Write-Host 'RESULT=FAIL'
  Write-Host "REASON=$why"
  Write-Host "EVIDENCE=$ev"
  exit 1
}
function Hash([string]$path) {
  (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant()
}
function Invoke-Lean([string[]]$arguments, [string]$stage, [string]$workingDir = $src) {
  $stdout = Join-Path $logs ($stage + '.stdout.log')
  $stderr = Join-Path $logs ($stage + '.stderr.log')
  Write-Host "BUILD_START=$stage"
  Push-Location $workingDir
  try {
    & $script:SelectedLean @arguments 1> $stdout 2> $stderr
    $code = $LASTEXITCODE
  } finally { Pop-Location }
  if ($code -ne 0) {
    Write-Host "BUILD_FAIL=$stage EXIT=$code"
    Get-Content -LiteralPath $stdout -ErrorAction SilentlyContinue | ForEach-Object { Write-Host $_ }
    Get-Content -LiteralPath $stderr -ErrorAction SilentlyContinue | ForEach-Object { Write-Host $_ }
    return $false
  }
  $allText = (Get-Content -LiteralPath $stdout -Raw -ErrorAction SilentlyContinue) + "`n" + (Get-Content -LiteralPath $stderr -Raw -ErrorAction SilentlyContinue)
  if ($allText -match '(?i)declaration uses .sorry.|\bsorryAx\b|\berror:') {
    Write-Host "BUILD_FAIL=$stage ERROR_OR_ADMISSION_OUTPUT"
    Write-Host $allText
    return $false
  }
  Write-Host "BUILD_PASS=$stage"
  return $true
}
function Check-SourceManifest {
  $manifestFile = Join-Path $pkg 'source-manifest.json'
  if (-not (Test-Path -LiteralPath $manifestFile -PathType Leaf)) { Fail 'MISSING_SOURCE_MANIFEST' }
  $manifest = Get-Content -LiteralPath $manifestFile -Raw | ConvertFrom-Json
  $needed = @('FiniteAffine','RankToCollatz','BinaryAdapter','Main','CollatzIntegerBridge','major_lean_collatz')
  foreach ($module in $needed) {
    $file = Join-Path $src ($module + '.lean')
    if (-not (Test-Path -LiteralPath $file -PathType Leaf)) { Fail "MISSING_SOURCE_$module" }
    $entry = $manifest.PSObject.Properties[$module]
    if ($null -eq $entry -or [string]$entry.Value -notmatch '^[0-9a-fA-F]{64}$') { Fail "MISSING_MANIFEST_HASH_$module" }
    $observed = Hash $file
    if ($observed -ine ([string]$entry.Value)) { Fail "SOURCE_HASH_MISMATCH_$module" }
  }
  # These four are the exact original Lean 4.33 source bytes identified by inspection.
  $pinned = @{
    FiniteAffine='21e0b371d9445b9e95eb9621f1917f7e5ec8f63177a4a7b54a0972e79bb7eeb9'
    RankToCollatz='8ddcca1ccebeadc1ce6cb10622e09f44962c20b9d93097d0b9fca616a0a30411'
    BinaryAdapter='e8724aea01feda038bf65f712d2e33db94916a44c6cfe05710664435f6a72596'
    Main='857404e50b3084ef96c556b813b2afc9ce941640b07bb97616487c72d6af97ce'
    CollatzIntegerBridge='fb0f96a4ef837245209b5568c11a26767e489c247e42e12a8888650c7a52d95b'
  }
  foreach ($module in $pinned.Keys) {
    if ((Hash (Join-Path $src ($module+'.lean'))) -ne $pinned[$module]) { Fail "ORIGINAL_SOURCE_MISMATCH_$module" }
  }
  return $needed
}
try {
  $modules = @(Check-SourceManifest)
  $manifestSnapshot = Get-Content -LiteralPath (Join-Path $pkg 'source-manifest.json') -Raw
  Write-Text (Join-Path $ev 'source-manifest.json') $manifestSnapshot
  Write-Host 'SOURCE_HASHES=PASS'
  $candidates = [Collections.Generic.List[string]]::new()
  if (-not [string]::IsNullOrWhiteSpace($LeanExe)) { $candidates.Add($LeanExe) }
  foreach ($homeDir in @($env:ELAN_HOME, $(if ($env:USERPROFILE) { Join-Path $env:USERPROFILE '.elan' }))) {
    if (-not [string]::IsNullOrWhiteSpace($homeDir)) {
      $exactLean=Join-Path $homeDir 'toolchains\leanprover--lean4---v4.34.0-rc1\bin\lean.exe'
      if (-not $candidates.Contains($exactLean)) { $candidates.Add($exactLean) }
    }
  }
  $script:SelectedLean = $null
  $selection = [Collections.Generic.List[string]]::new()
  foreach ($c in $candidates) {
    if (-not (Test-Path -LiteralPath $c -PathType Leaf)) { $selection.Add("MISSING=$c"); continue }
    $cp=(Resolve-Path -LiteralPath $c).Path
    if ($cp -match '(?i)[\\/]\.elan[\\/]bin[\\/]lean\.exe$') { $selection.Add("SKIPPED_SHIM=$cp"); continue }
    try {
      $v=(& $cp --version 2>&1 | Out-String).Trim()
      $code=$LASTEXITCODE
      $selection.Add("VERSION_CHECK=$cp EXIT=$code VERSION=$v")
      if ($code -eq 0 -and $v -match '^Lean \(version 4\.34\.0-rc1,') { $script:SelectedLean=$cp; $version=$v; break }
    } catch { $selection.Add("VERSION_ERROR=$cp $($_.Exception.Message)") }
  }
  Write-Text (Join-Path $ev 'lean-selection.txt') ($selection -join "`r`n")
  if (-not $script:SelectedLean) { Fail 'LEAN_4_34_0_RC1_NOT_FOUND_SET_LEAN_EXE' }
  Write-Host "LEAN_EXE=$script:SelectedLean"
  Write-Host $version
  Write-Text (Join-Path $ev 'lean-version.txt') $version
  if ([string]::IsNullOrWhiteSpace($MathlibCacheRoot)) { Fail 'SET_MATHLIB_CACHE_ROOT_TO_EXISTING_RC1_CACHE' }
  if (-not (Test-Path -LiteralPath $MathlibCacheRoot -PathType Container)) { Fail 'MATHLIB_CACHE_ROOT_NOT_FOUND' }
  $root=(Resolve-Path -LiteralPath $MathlibCacheRoot).Path
  $mathlib=$null
  foreach ($candidate in @($root,(Join-Path $root '.lake\build\lib\lean'),(Join-Path $root '.lake\packages\mathlib\.lake\build\lib\lean'),(Join-Path $root 'mathlib\.lake\build\lib\lean'))) {
    if (Test-Path -LiteralPath (Join-Path $candidate 'Mathlib.olean') -PathType Leaf) { $mathlib=(Resolve-Path -LiteralPath $candidate).Path; break }
  }
  if (-not $mathlib) { Fail 'MATHLIB_UMBRELLA_OLEAN_NOT_FOUND_IN_CACHE' }
  $pathList=[Collections.Generic.List[string]]::new()
  $pathList.Add($ol); $pathList.Add($mathlib)
  $parents=[Collections.Generic.List[string]]::new()
  foreach ($start in @($root,$mathlib)) {
    $item=Get-Item -LiteralPath $start
    while ($null -ne $item) {
      if (-not $parents.Contains($item.FullName)) { $parents.Add($item.FullName) }
      $item=$item.Parent
    }
  }
  foreach ($p in $parents) {
    $packages=Join-Path $p '.lake\packages'
    if (Test-Path -LiteralPath $packages -PathType Container) {
      foreach ($dep in @(Get-ChildItem -LiteralPath $packages -Directory | Sort-Object Name)) {
        $lib=Join-Path $dep.FullName '.lake\build\lib\lean'
        if ((Test-Path -LiteralPath $lib -PathType Container) -and -not $pathList.Contains($lib)) { $pathList.Add($lib) }
      }
    }
  }
  $env:LEAN_PATH=$pathList -join ';'
  $env:LEAN_NUM_THREADS=[string]$Threads
  Write-Text (Join-Path $ev 'lean-path.txt') ($pathList -join "`r`n")
  $provenance=@(
    "COMPILER_SHA256=$(Hash $script:SelectedLean)",
    "MANIFEST_SHA256=$(Hash (Join-Path $pkg 'source-manifest.json'))",
    "MATHLIB_ROOT=$mathlib",
    "MATHLIB_UMBRELLA_OLEAN_SHA256=$(Hash (Join-Path $mathlib 'Mathlib.olean'))",
    'MATHLIB_CACHE_PROVENANCE=USER_SUPPLIED_NOT_INDEPENDENTLY_VERIFIED',
    'LOCAL_SOURCE_MODULES=COMPILED_FRESH',
    'DEPENDENCIES=EXISTING_CACHE_ONLY',
    'C_SOURCE_EQUIVALENCE=NOT_ESTABLISHED',
    'WITNESS_INPUT_HASH_FILE=witness-hashes.txt'
  )
  Write-Text (Join-Path $ev 'provenance.txt') ($provenance -join "`r`n")
  Write-Host 'CACHE_REUSE=MATHLIB_USER_SUPPLIED_SOURCE_OBJECT_PROVENANCE_UNVERIFIED'
  foreach ($module in $modules) {
    $source=Join-Path $src ($module+'.lean')
    $object=Join-Path $ol ($module+'.olean')
    if (-not (Invoke-Lean -arguments @(('-j' + $Threads), '-o', $object, $source) -stage $module)) { Fail "MODULE_BUILD_$module" }
    if (-not (Test-Path -LiteralPath $object -PathType Leaf)) { Fail "MISSING_OLEAN_$module" }
  }
  # Freeze and hash the exact input before generating executable Lean syntax.
  if (-not (Test-Path -LiteralPath $WitnessPath -PathType Leaf)) { Fail 'WITNESS_INPUT_NOT_FOUND' }
  $frozenWitness = Join-Path $ev 'witness-input.txt'
  Copy-Item -LiteralPath $WitnessPath -Destination $frozenWitness
  $witnessHash = Hash $frozenWitness
  $generator = Join-Path $pkg 'generate-witness.ps1'
  if (-not (Test-Path -LiteralPath $generator -PathType Leaf)) { Fail 'WITNESS_GENERATOR_NOT_FOUND' }
  $generatorHash = Hash $generator
  $witnessLean = Join-Path $ev 'CollatzWitness.lean'
  $generatorOut = Join-Path $logs 'GenerateWitness.stdout.log'
  $generatorErr = Join-Path $logs 'GenerateWitness.stderr.log'
  Write-Host 'WITNESS_GENERATE=START'
  $powerShell = Join-Path $env:SystemRoot 'System32\WindowsPowerShell\v1.0\powershell.exe'
  & $powerShell -NoProfile -ExecutionPolicy Bypass -File $generator -InputPath $frozenWitness -OutputPath $witnessLean 1> $generatorOut 2> $generatorErr
  if ($LASTEXITCODE -ne 0) {
    Get-Content -LiteralPath $generatorOut -ErrorAction SilentlyContinue | ForEach-Object { Write-Host $_ }
    Get-Content -LiteralPath $generatorErr -ErrorAction SilentlyContinue | ForEach-Object { Write-Host $_ }
    Fail 'WITNESS_GENERATION_FAILED'
  }
  if (-not (Test-Path -LiteralPath $witnessLean -PathType Leaf)) { Fail 'GENERATED_LEAN_NOT_FOUND' }
  if ((Hash $generator) -ne $generatorHash -or (Hash $frozenWitness) -ne $witnessHash) { Fail 'GENERATION_INPUT_CHANGED' }
  $generatedHash = Hash $witnessLean
  Write-Text (Join-Path $ev 'witness-hashes.txt') "INPUT_SHA256=$witnessHash`r`nGENERATOR_SHA256=$generatorHash`r`nGENERATED_LEAN_SHA256=$generatedHash`r`n"
  Write-Host 'WITNESS_GENERATE=PASS'
  $witnessObject = Join-Path $ol 'CollatzWitness.olean'
  if (-not (Invoke-Lean -arguments @(('-j' + $Threads), '-o', $witnessObject, $witnessLean) -stage 'CollatzWitness' -workingDir $ev)) { Fail 'WITNESS_KERNEL_CHECK_FAILED_OR_RESOURCE_LIMIT' }
  if (-not (Test-Path -LiteralPath $witnessObject -PathType Leaf)) { Fail 'WITNESS_OLEAN_MISSING' }
  if ((Hash $witnessLean) -ne $generatedHash -or (Hash $frozenWitness) -ne $witnessHash) { Fail 'WITNESS_INPUT_OR_SOURCE_CHANGED' }
  # A fresh typed check verifies the exact mathematical conclusion, beyond a named audit.
  $typeCheck = Join-Path $ev 'ExactConclusion.lean'
  Write-Text $typeCheck "import CollatzWitness`nexample : forall n : Nat, 0 < n -> PoincareSecond.OrdinaryReachesOne n := CollatzWitness.collatz`n"
  if (-not (Invoke-Lean -arguments @(('-j' + $Threads), $typeCheck) -stage 'ExactConclusion' -workingDir $ev)) { Fail 'EXACT_CONCLUSION_TYPECHECK_FAILED' }
  # Fail closed on changed source or original source mismatch during build.
  $null=@(Check-SourceManifest)
  $auditTheorems=@(
    'PoincareSecond.Certificate.check_eq_true_iff',
    'PoincareSecond.CHECKER_SOUND',
    'PoincareSecond.FINITE_WITNESS_IMPLIES_COLLATZ',
    'CollatzIntegerBridge.integerValid_iff_original_check',
    'CollatzIntegerBridge.integerCheck_iff_original_check',
    'CollatzIntegerBridge.integerValid_implies_collatz',
    'MajorLeanCollatz.integer_check_iff_original',
    'MajorLeanCollatz.integer_check_implies_collatz',
    'MajorLeanCollatz.denominator_positive',
    'MajorLeanCollatz.b0_nonnegative',
    'MajorLeanCollatz.b1_nonnegative',
    'MajorLeanCollatz.seed_nonnegative',
    'MajorLeanCollatz.weight_nonnegative',
    'CollatzWitness.witness_valid',
    'CollatzWitness.collatz'
  )
  $axiomAllowed=@('propext','Classical.choice','Quot.sound')
  foreach ($name in $auditTheorems) {
    $safeName=$name.Replace('.','_')
    $auditFile=Join-Path $ev ('Audit_'+$safeName+'.lean')
    $auditText="import CollatzWitness`n#check $name`n#print axioms $name`n"
    Write-Text $auditFile $auditText
    if (-not (Invoke-Lean -arguments @(('-j' + $Threads), $auditFile) -stage ('Audit_'+$safeName) -workingDir $ev)) { Fail "AXIOM_AUDIT_COMPILE_$safeName" }
    $auditLog=Get-Content -LiteralPath (Join-Path $logs ('Audit_'+$safeName+'.stdout.log')) -Raw
    $escaped=[regex]::Escape($name)
    if ($auditLog -match ("(?s)'"+$escaped+"'\s+does not depend on any axioms")) {
      Write-Host "AXIOM_AUDIT_STANDARD_ONLY=$name"
      continue
    }
    $m=[regex]::Match($auditLog,("(?s)'"+$escaped+"'\s+depends on axioms:\s*\[([^\]]*)\]"))
    if (-not $m.Success) { Fail "AXIOM_AUDIT_MISSING_OR_UNPARSEABLE_$safeName" }
    $depText=$m.Groups[1].Value.Trim()
    if ($depText.Length -gt 0) {
      foreach ($dep in $depText.Split(',')) {
        $a=$dep.Trim()
        if ($a -notin $axiomAllowed) { Fail "AXIOM_AUDIT_UNAPPROVED_$safeName" }
      }
    }
    Write-Host "AXIOM_AUDIT_STANDARD_ONLY=$name"
  }
  if ((Hash $witnessLean) -ne $generatedHash -or (Hash $frozenWitness) -ne $witnessHash -or (Hash $generator) -ne $generatorHash) { Fail 'WITNESS_INPUT_OR_SOURCE_CHANGED_AFTER_BUILD' }
  $null=@(Check-SourceManifest)
  $objects=@{}
  foreach ($file in @(Get-ChildItem -LiteralPath $ol -File | Sort-Object Name)) { $objects[$file.Name]=Hash $file.FullName }
  Write-Text (Join-Path $ev 'object-hashes.json') (($objects | ConvertTo-Json) + "`r`n")
  $auditHashes=@{}
  foreach ($file in @(Get-ChildItem -LiteralPath $logs -File | Sort-Object Name)) { $auditHashes[$file.Name]=Hash $file.FullName }
  Write-Text (Join-Path $ev 'log-hashes.json') (($auditHashes | ConvertTo-Json) + "`r`n")
  $result=@(
    'Hypotehtical Candidate found',
    'BUILD_AND_NAMED_AXIOM_AUDITS=PASS',
    'RESULT_SCOPE=EXACT_ORDINARY_COLLATZ_FROM_REPLAYED_WITNESS',
    'C_SOURCE_EQUIVALENCE=NOT_ESTABLISHED',
    'WITNESS_KERNEL_CHECK=PASS',
    'EXACT_CONCLUSION_TYPECHECK=PASS',
    'C_SEARCH=NOT_INCLUDED',
    'MATHLIB_CACHE_PROVENANCE=USER_SUPPLIED_NOT_INDEPENDENTLY_VERIFIED',
    'RESULT=PASS'
  )
  Write-Text (Join-Path $ev 'result.txt') ($result -join "`r`n")
  foreach ($line in $result) { Write-Host $line }
  Write-Host "EVIDENCE=$ev"
  exit 0
} catch {
  Write-Host ("EXCEPTION=" + $_.Exception.ToString())
  Fail 'UNHANDLED_RUNNER_EXCEPTION'
}
