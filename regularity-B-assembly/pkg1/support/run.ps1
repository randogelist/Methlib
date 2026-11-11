[CmdletBinding()]
param(
  [Parameter(Position = 0)][string]$MathlibCache = $env:H12_MATHLIB_CACHE,
  [string]$LeanExe = $env:H12_LEAN_EXE
)
$ErrorActionPreference = 'Stop'
$package = Split-Path -Parent $PSScriptRoot
$pin = 'db584cd6d46c92f209a44c0f1c829460d327499d'
$toolchain = 'leanprover/lean4:v4.33.0'
$runId = (Get-Date).ToUniversalTime().ToString('yyyyMMdd-HHmmss') + '-' + [guid]::NewGuid().ToString('N').Substring(0, 8)
$evidence = Join-Path $package ('evidence\' + $runId)
New-Item -ItemType Directory -Force $evidence | Out-Null
$oldLeanPath = $env:LEAN_PATH
$originalLocation = Get-Location
function Stage([string]$name) {
  Write-Host "STAGE=$name"
  Add-Content -LiteralPath (Join-Path $evidence 'stages.log') -Value "STAGE=$name" -Encoding UTF8
}
function Digest([string]$value) {
  $sha = [Security.Cryptography.SHA256]::Create()
  try { return ([BitConverter]::ToString($sha.ComputeHash([Text.Encoding]::UTF8.GetBytes($value)))).Replace('-', '').ToLowerInvariant() }
  finally { $sha.Dispose() }
}
function Git-Revision([string]$Checkout) {
  $savedPreference = $ErrorActionPreference
  $ErrorActionPreference = 'Continue'
  try { $output = @(& $script:git -C $Checkout rev-parse HEAD 2>$null); $code = $LASTEXITCODE }
  finally { $ErrorActionPreference = $savedPreference }
  if ($code -eq 0) { return ($output -join "`n").Trim() }
  return $null
}
function Invoke-Lean([string[]]$LeanArguments, [string]$LogPath) {
  $savedPreference = $ErrorActionPreference
  $ErrorActionPreference = 'Continue'
  try { $output = @(& $script:compiler @LeanArguments 2>&1); $code = $LASTEXITCODE }
  finally { $ErrorActionPreference = $savedPreference }
  $lines = @($output | ForEach-Object { $_.ToString() })
  $lines | Out-File -LiteralPath $LogPath -Encoding UTF8 -Append
  $lines | ForEach-Object { Write-Host $_ }
  if ($code -ne 0) { throw "Lean failed with exit code $code; see $LogPath" }
  if (($lines -join "`n") -match "sorryAx|declaration uses 'sorry'") { throw "Unproved declaration detected; see $LogPath" }
  return ($lines -join "`n")
}
try {
  if ($MathlibCache) { $MathlibCache = (Resolve-Path -LiteralPath $MathlibCache).Path }
  if ($LeanExe) { $LeanExe = (Resolve-Path -LiteralPath $LeanExe).Path }
  Set-Location -LiteralPath $package
  Stage 'RESOLVE_NATIVE_COMPILER'
  $compilerCandidates = [Collections.Generic.List[string]]::new()
  if ($LeanExe) { $compilerCandidates.Add($LeanExe) }
  else {
    foreach ($elanRoot in @($env:ELAN_HOME, (Join-Path $env:USERPROFILE '.elan'))) {
      if ($elanRoot) { $compilerCandidates.Add((Join-Path $elanRoot 'toolchains\leanprover--lean4---v4.33.0\bin\lean.exe')) }
    }
    $pathLean = Get-Command lean.exe -ErrorAction SilentlyContinue
    if ($pathLean -and $pathLean.Source -notmatch '[\\/](\.elan[\\/]bin|shims)[\\/]') { $compilerCandidates.Add($pathLean.Source) }
    foreach ($nativeRoot in @((Join-Path $env:USERPROFILE 'lean-native'), 'C:\lean')) {
      if (Test-Path -LiteralPath $nativeRoot -PathType Container) {
        $compilerCandidates.Add((Join-Path $nativeRoot 'bin\lean.exe'))
        Get-ChildItem -LiteralPath $nativeRoot -Directory | ForEach-Object { $compilerCandidates.Add((Join-Path $_.FullName 'bin\lean.exe')) }
      }
    }
  }
  $script:compiler = $null
  foreach ($candidate in $compilerCandidates) {
    if (!(Test-Path -LiteralPath $candidate -PathType Leaf) -or $candidate -match '[\\/]\.elan[\\/]bin[\\/]') { continue }
    $version = (& $candidate --version 2>&1 | Out-String).Trim()
    if ($LASTEXITCODE -eq 0 -and $version -match 'version\s+4\.33\.0(?:,|\))') {
      $script:compiler = (Resolve-Path -LiteralPath $candidate).Path
      break
    }
  }
  if (!$script:compiler) { throw 'Native Lean 4.33.0 was not found. Set H12_LEAN_EXE to an existing direct lean.exe; no installation is attempted.' }
  "COMPILER=$script:compiler`n$version" | Set-Content -LiteralPath (Join-Path $evidence 'compiler.txt') -Encoding UTF8
  Write-Host $version

  Stage 'RESOLVE_PINNED_MATHLIB_CACHE'
  $script:git = (Get-Command git.exe -ErrorAction Stop).Source
  $cacheCandidates = [Collections.Generic.List[string]]::new()
  if ($MathlibCache) { $cacheCandidates.Add($MathlibCache) }
  else {
    foreach ($root in @($package, (Split-Path $package -Parent), (Split-Path (Split-Path $package -Parent) -Parent), (Join-Path $env:USERPROFILE 'mathlib4'), (Join-Path $env:USERPROFILE 'lean-native'), 'C:\lean\mathlib4')) {
      if (Test-Path -LiteralPath $root -PathType Container) {
        $cacheCandidates.Add($root)
        if ((Split-Path $root -Leaf) -eq 'lean-native') {
          Get-ChildItem -LiteralPath $root -Directory | ForEach-Object { $cacheCandidates.Add($_.FullName) }
        }
      }
    }
  }
  $mathlib = $null
  foreach ($candidate in $cacheCandidates) {
    foreach ($probe in @($candidate, (Join-Path $candidate '.lake\packages\mathlib'))) {
      if (!(Test-Path -LiteralPath (Join-Path $probe '.lake\build\lib\lean\Mathlib.olean') -PathType Leaf)) { continue }
      if (!(Test-Path -LiteralPath (Join-Path $probe 'lean-toolchain') -PathType Leaf)) { continue }
      if ((Get-Content -LiteralPath (Join-Path $probe 'lean-toolchain') -Raw).Trim() -ne $toolchain) { continue }
      $revision = Git-Revision $probe
      if ($revision -ne $pin) { continue }
      & $git -C $probe diff --quiet HEAD --
      if ($LASTEXITCODE -ne 0) { continue }
      $mathlib = (Resolve-Path -LiteralPath $probe).Path
      $cacheHost = (Resolve-Path -LiteralPath $candidate).Path
      break
    }
    if ($mathlib) { break }
  }
  if (!$mathlib) { throw "No clean cached Mathlib checkout at $pin with $toolchain and Mathlib.olean. Pass its checkout or containing project as the first argument. No downloads are attempted." }
  $dependencyRoots = [Collections.Generic.List[string]]::new()
  $dependencyRoots.Add((Join-Path $mathlib '.lake\build\lib\lean'))
  $manifest = Get-Content -LiteralPath (Join-Path $mathlib 'lake-manifest.json') -Raw | ConvertFrom-Json
  $fingerprint = @("LEAN=$version", "LEAN_EXE_SHA256=$((Get-FileHash -LiteralPath $script:compiler -Algorithm SHA256).Hash)", "MATHLIB=$pin")
  foreach ($dependency in $manifest.packages) {
    $depRoot = $null
    $packageDirs = @((Join-Path $mathlib '.lake\packages'), (Join-Path $cacheHost '.lake\packages'), (Split-Path $mathlib -Parent)) | Select-Object -Unique
    foreach ($packageDir in $packageDirs) {
      $probe = Join-Path $packageDir $dependency.name
      if (Test-Path -LiteralPath (Join-Path $probe '.lake\build\lib\lean') -PathType Container) {
        $depRevision = Git-Revision $probe
        if ($depRevision -eq $dependency.rev) {
          & $git -C $probe diff --quiet HEAD --
          if ($LASTEXITCODE -eq 0) { $depRoot = $probe; break }
        }
      }
    }
    if (!$depRoot) { throw "Missing clean pinned cached dependency: $($dependency.name) at $($dependency.rev)." }
    $dependencyRoots.Add((Join-Path $depRoot '.lake\build\lib\lean'))
    $fingerprint += "$($dependency.name)=$($dependency.rev)"
  }
  $fingerprint += "MATHLIB_OLEAN=$((Get-FileHash -LiteralPath (Join-Path $mathlib '.lake\build\lib\lean\Mathlib.olean') -Algorithm SHA256).Hash)"
  $fingerprint | Set-Content -LiteralPath (Join-Path $evidence 'dependencies.txt') -Encoding UTF8
  Write-Host "ACCEPTED_CACHE=$mathlib"

  Stage 'SOURCE_MANIFEST'
  $audit = Join-Path $package 'ci\Audit.lean'
  $auditSpecPath = Join-Path $package 'ci\expected_axioms.json'
  $fixedFiles = @($audit, $auditSpecPath, $PSCommandPath, (Join-Path $package 'run.cmd'), (Join-Path $package 'lean-toolchain'), (Join-Path $package 'lake-manifest.json'), (Join-Path $package 'lakefile.toml'))
  foreach ($file in $fixedFiles) { if (!(Test-Path -LiteralPath $file -PathType Leaf)) { throw "Missing required package file: $file" } }
  if ((Get-Content -LiteralPath (Join-Path $package 'lean-toolchain') -Raw).Trim() -cne $toolchain) { throw 'Package toolchain differs from the pinned native compiler.' }
  $packageManifest = Get-Content -LiteralPath (Join-Path $package 'lake-manifest.json') -Raw | ConvertFrom-Json
  $packageMathlib = @($packageManifest.packages | Where-Object { $_.name -ceq 'mathlib' })
  if ($packageMathlib.Count -ne 1 -or $packageMathlib[0].rev -cne $pin) { throw 'Package manifest does not pin the required Mathlib revision.' }
  $sourceFiles = @(Get-ChildItem -LiteralPath $package -Filter '*.lean' -File | Sort-Object Name)
  if ($sourceFiles.Count -eq 0) { throw 'No Lean source modules found.' }
  $hashLines = @(@($sourceFiles.FullName) + $fixedFiles | ForEach-Object {
    "$((Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash)  $($_.Substring($package.Length + 1))"
  })
  $hashLines | Set-Content -LiteralPath (Join-Path $evidence 'SHA256_MANIFEST.txt') -Encoding UTF8
  $modules = @{}; $script:marks = @{}; $script:order = [Collections.Generic.List[string]]::new()
  foreach ($source in $sourceFiles) { $modules[$source.BaseName] = $source }
  $imports = @{}
  foreach ($name in $modules.Keys) {
    $imports[$name] = @([regex]::Matches((Get-Content -LiteralPath $modules[$name].FullName -Raw), '(?m)^\s*import\s+([^\r\n]+)') | ForEach-Object {
      (($_.Groups[1].Value -replace '--.*$', '').Trim() -split '\s+') | Where-Object { $modules.ContainsKey($_) }
    })
  }
  function Visit-Module([string]$name) {
    if ($script:marks[$name] -eq 2) { return }
    if ($script:marks[$name] -eq 1) { throw "Cyclic local import: $name" }
    $script:marks[$name] = 1
    foreach ($dependency in $imports[$name]) { Visit-Module $dependency }
    $script:marks[$name] = 2
    $script:order.Add($name)
  }
  foreach ($name in @($modules.Keys | Sort-Object)) { Visit-Module $name }
  $build = Join-Path $package '.lake\build\lib\lean'
  New-Item -ItemType Directory -Force $build | Out-Null
  $env:LEAN_PATH = (@($build) + @($dependencyRoots)) -join ';'
  $moduleHashes = @{}
  Stage 'CACHED_PROJECT_BUILD'
  foreach ($name in $script:order) {
    $key = Digest (($fingerprint + @((Get-FileHash -LiteralPath $modules[$name].FullName -Algorithm SHA256).Hash) + @($imports[$name] | ForEach-Object { $moduleHashes[$_] })) -join "`n")
    $moduleHashes[$name] = $key
    $olean = Join-Path $build ($name + '.olean')
    $stamp = Join-Path $build ($name + '.sha256')
    $cacheHit = $false
    if ((Test-Path -LiteralPath $olean -PathType Leaf) -and (Test-Path -LiteralPath $stamp -PathType Leaf)) {
      $stampParts = ((Get-Content -LiteralPath $stamp -Raw).Trim() -split '\s+')
      $cacheHit = $stampParts.Count -eq 2 -and $stampParts[0] -eq $key -and $stampParts[1] -eq (Get-FileHash -LiteralPath $olean -Algorithm SHA256).Hash
    }
    if ($cacheHit) {
      Write-Host "CACHE_HIT=$name"
      Add-Content -LiteralPath (Join-Path $evidence 'build.log') -Value "CACHE_HIT=$name" -Encoding UTF8
      continue
    }
    Write-Host "BUILD=$name"
    Add-Content -LiteralPath (Join-Path $evidence 'build.log') -Value "BUILD=$name" -Encoding UTF8
    Remove-Item -LiteralPath $stamp -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath @($olean, "${olean}.private", "${olean}.server") -ErrorAction SilentlyContinue
    $null = Invoke-Lean -LeanArguments @('-o', $olean, $modules[$name].Name) -LogPath (Join-Path $evidence 'build.log')
    "$key $((Get-FileHash -LiteralPath $olean -Algorithm SHA256).Hash)" | Set-Content -LiteralPath $stamp -Encoding ASCII
  }

  Stage 'FRESH_EXACT_TYPE_AND_AXIOM_AUDIT'
  $auditText = Get-Content -LiteralPath $audit -Raw
  $auditSpec = Get-Content -LiteralPath $auditSpecPath -Raw | ConvertFrom-Json
  $standardAxioms = @('propext', 'Classical.choice', 'Quot.sound')
  if (($auditSpec.schema_version -isnot [int] -and $auditSpec.schema_version -isnot [long]) -or
      $auditSpec.schema_version -ne 1 -or $auditSpec.standard_axioms -isnot [array] -or
      @($auditSpec.standard_axioms).Count -ne 3 -or
      ((@($auditSpec.standard_axioms | Sort-Object) -join "`n") -cne (@($standardAxioms | Sort-Object) -join "`n"))) {
    throw 'Audit specification must use schema 1 and exactly propext, Classical.choice, Quot.sound.'
  }
  if ($auditSpec.declarations -isnot [array]) { throw 'Audit declarations must be an array.' }
  $expected = @($auditSpec.declarations | ForEach-Object { $_.name })
  $printedNames = @([regex]::Matches($auditText, '(?m)^\s*#print\s+axioms\s+(\S+)') | ForEach-Object { $_.Groups[1].Value })
  if ($expected.Count -eq 0 -or @($expected | Select-Object -Unique).Count -ne $expected.Count -or
      $printedNames.Count -ne $expected.Count -or
      ((@($printedNames | Sort-Object) -join "`n") -cne (@($expected | Sort-Object) -join "`n"))) {
    throw 'Audit #print names must match the nonempty, duplicate-free expected declaration list exactly.'
  }
  $markers = @($auditSpec.declarations | ForEach-Object { $_.exact_type_marker })
  if (@($markers | Select-Object -Unique).Count -ne $expected.Count) { throw 'Exact-type markers must be distinct.' }
  foreach ($declaration in $auditSpec.declarations) {
    if ($declaration.name -isnot [string] -or !$declaration.name -or
        $declaration.exact_type_marker -cne ('EXACT_TYPE_PASS:' + $declaration.name) -or
        $declaration.additional_allowed_axioms -isnot [array] -or
        @($declaration.additional_allowed_axioms).Count -ne 0 -or
        $declaration.required_axioms -isnot [array]) {
      throw 'Each audit declaration requires a name, exact-type marker, and no additional allowed axioms.'
    }
    foreach ($required in $declaration.required_axioms) { if ($standardAxioms -cnotcontains $required) { throw "Nonstandard required axiom: $required" } }
  }
  $auditOutput = Invoke-Lean -LeanArguments @('ci\Audit.lean') -LogPath (Join-Path $evidence 'audit.log')
  $reports = [Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  $reportStarts = [Collections.Generic.HashSet[int]]::new()
  foreach ($match in [regex]::Matches($auditOutput, "(?m)^[ \t]*(?:'(?<quoted>[^'\r\n]+)'|(?<bare>[A-Za-z_][A-Za-z0-9_.]*))[ \t]+depends on axioms:\s*\[(?<axioms>[^\]]*)\][ \t]*\r?$")) {
    [void]$reportStarts.Add($match.Index)
    $name = if ($match.Groups['quoted'].Success) { $match.Groups['quoted'].Value } else { $match.Groups['bare'].Value }
    if ($reports.ContainsKey($name)) { throw "Duplicate axiom report: $name" }
    $axioms = @($match.Groups['axioms'].Value -split '[,\s]+' | Where-Object { $_ })
    foreach ($axiom in $axioms) { if ($standardAxioms -cnotcontains $axiom) { throw "Unapproved axiom for ${name}: $axiom" } }
    $reports[$name] = $axioms
  }
  foreach ($match in [regex]::Matches($auditOutput, "(?m)^[ \t]*(?:'(?<quoted>[^'\r\n]+)'|(?<bare>[A-Za-z_][A-Za-z0-9_.]*))[ \t]+does not depend on any axioms[ \t]*\r?$")) {
    [void]$reportStarts.Add($match.Index)
    $name = if ($match.Groups['quoted'].Success) { $match.Groups['quoted'].Value } else { $match.Groups['bare'].Value }
    if ($reports.ContainsKey($name)) { throw "Duplicate axiom report: $name" }
    $reports[$name] = @()
  }
  foreach ($match in [regex]::Matches($auditOutput, "(?m)^[ \t]*(?:'[^'\r\n]+'|[A-Za-z_][A-Za-z0-9_.]*)[ \t]+(?:depends on axioms:|does not depend on any axioms)")) {
    if (!$reportStarts.Contains($match.Index)) { throw 'Malformed axiom report.' }
  }
  foreach ($declaration in $auditSpec.declarations) {
    $name = $declaration.name
    if (!$reports.ContainsKey($name)) { throw "Missing axiom report: $name" }
    foreach ($required in $declaration.required_axioms) { if ($reports[$name] -cnotcontains $required) { throw "Missing required axiom for ${name}: $required" } }
    $escapedMarker = [regex]::Escape($declaration.exact_type_marker)
    $markerPattern = '(?m)^[ \t]*(?:"' + $escapedMarker + '"|' + $escapedMarker + ')[ \t]*\r?$'
    if ([regex]::Matches($auditOutput, $markerPattern).Count -ne 1) { throw "Missing or duplicate exact-type marker for $name" }
  }
  if ($reports.Count -ne $expected.Count) { throw 'Unexpected extra axiom reports.' }
  $finalSourceNames = @(Get-ChildItem -LiteralPath $package -Filter '*.lean' -File | Sort-Object Name | ForEach-Object { $_.Name })
  if (($sourceFiles.Name -join "`n") -cne ($finalSourceNames -join "`n")) { throw 'The Lean source file set changed during this run.' }
  $finalHashLines = @(@($sourceFiles.FullName) + $fixedFiles | ForEach-Object {
    "$((Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash)  $($_.Substring($package.Length + 1))"
  })
  if (($hashLines -join "`n") -ne ($finalHashLines -join "`n")) { throw 'Sources changed during this run; compiler evidence is not promotable.' }
  "SOURCE_MANIFEST=PASS`nCACHED_PROJECT_BUILD=PASS`nEXACT_TYPE_AUDIT=PASS`nAXIOM_AUDIT_STANDARD_ONLY=PASS`nTHEOREM_COUNT=$($expected.Count)`nSCOPE=Only the exact declarations and premises checked by ci/Audit.lean" | Set-Content -LiteralPath (Join-Path $evidence 'result.txt') -Encoding UTF8
  Stage 'PASS'
  Write-Host "EVIDENCE=$evidence"
  exit 0
} catch {
  $message = $_.Exception.Message
  "STATUS=FAIL`n$message" | Set-Content -LiteralPath (Join-Path $evidence 'result.txt') -Encoding UTF8
  Write-Host "FAIL=$message"
  Write-Host "EVIDENCE=$evidence"
  exit 1
} finally {
  $env:LEAN_PATH = $oldLeanPath
  Set-Location $originalLocation
}
