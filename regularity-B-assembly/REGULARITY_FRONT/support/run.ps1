param(
  [string]$MathlibProject,
  [switch]$Rebuild
)

$ErrorActionPreference = 'Stop'
$pkg = Split-Path -Parent $PSScriptRoot
$baseSrc = Join-Path $pkg 'NSE_ROUGH_SHEAR_L2_FAMILY.lean'
$spectralSrc = Join-Path $pkg 'S_DIR_L2_SPECTRAL.lean'
$rootSrc = Join-Path $pkg 'S_DIR_L2_GLOBAL_REGULARITY.lean'
$schurSrc = Join-Path $pkg 'S_DIR_L2_SCHUR_FRONTIER.lean'
$witnessSrc = Join-Path $pkg 'NSE_ROUGH_SHEAR_STRICT_NONEMPTY.lean'
$kernelSrc = Join-Path $pkg 'S_DIR_L2_SCHUR_KERNEL.lean'
$assemblySrc = Join-Path $pkg 'S_DIR_L2_PROOF_ASSEMBLY.lean'
$dyadicSrc = Join-Path $pkg 'S_DIR_L2_DYADIC_SCHUR.lean'
$rowSrc = Join-Path $pkg 'S_DIR_L2_DYADIC_ROW.lean'
$actualSrc = Join-Path $pkg 'S_DIR_L2_ACTUAL_SHELLS.lean'
$infiniteSchurSrc = Join-Path $pkg 'S_DIR_L2_INFINITE_SCHUR.lean'
$serrinFiniteSrc = Join-Path $pkg 'S_DIR_L2_SERRIN_FINITE.lean'
$serrinInfiniteSrc = Join-Path $pkg 'S_DIR_L2_SERRIN_INFINITE.lean'
$utf8 = New-Object Text.UTF8Encoding($false)

function Save([string]$Path, [object[]]$Lines) {
  [IO.File]::WriteAllLines($Path, [string[]]$Lines, $utf8)
}

function HashFile([string]$Path) {
  $sha = [Security.Cryptography.SHA256]::Create()
  try {
    $stream = [IO.File]::OpenRead($Path)
    try {
      return ([BitConverter]::ToString($sha.ComputeHash($stream))).Replace('-','').ToLowerInvariant()
    } finally {
      $stream.Dispose()
    }
  } finally {
    $sha.Dispose()
  }
}

function RunNative {
  param(
    [Parameter(Mandatory=$true)]
    [string[]]$LeanArgs,
    [Parameter(Mandatory=$true)]
    [string]$Dir,
    [Parameter(Mandatory=$true)]
    [string]$Log
  )

  Push-Location -LiteralPath $Dir
  try {
    $ErrorActionPreference = 'Continue'
    $out = @(& $script:lean @LeanArgs 2>&1 | ForEach-Object { $_.ToString() })
    $rc = $LASTEXITCODE
  } finally {
    Pop-Location
    $ErrorActionPreference = 'Stop'
  }

  Save $Log $out
  if ($rc -ne 0) {
    $out | Select-Object -First 160 | ForEach-Object { Write-Host $_ }
    throw "Lean exit $rc. Log: $Log"
  }
  if (($out -join "`n") -match "(?im)warning:.*declaration uses ['`"]sorry['`"]") {
    throw "Incomplete proof detected. Log: $Log"
  }
}

function GetLakeProjectRoots {
  param([string]$Project)
  $found = @()
  if (!$Project -or !(Test-Path -LiteralPath $Project -PathType Container)) {
    return @()
  }
  $selfRoot = Join-Path $Project '.lake\build\lib\lean'
  if (Test-Path -LiteralPath $selfRoot -PathType Container) {
    $found += (Get-Item -LiteralPath $selfRoot).FullName
  }
  $packages = Join-Path $Project '.lake\packages'
  if (Test-Path -LiteralPath $packages -PathType Container) {
    foreach ($dependency in @(Get-ChildItem -LiteralPath $packages -Directory | Sort-Object Name)) {
      $dependencyRoot = Join-Path $dependency.FullName '.lake\build\lib\lean'
      if (Test-Path -LiteralPath $dependencyRoot -PathType Container) {
        $found += (Get-Item -LiteralPath $dependencyRoot).FullName
      }
    }
  }
  return @($found | Select-Object -Unique)
}

function ResolveLeanEnvironment {
  param([string]$Candidate)
  if (!$Candidate) { return $null }
  try { $c = [IO.Path]::GetFullPath($Candidate) } catch { return $null }
  if (!(Test-Path -LiteralPath $c -PathType Container)) { return $null }

  $primary = $null
  $project = $null
  $projectMathlib = Join-Path $c '.lake\packages\mathlib\.lake\build\lib\lean'
  $selfMathlib = Join-Path $c '.lake\build\lib\lean'

  if (Test-Path -LiteralPath (Join-Path $projectMathlib 'Mathlib.olean') -PathType Leaf) {
    $primary = (Get-Item -LiteralPath $projectMathlib).FullName
    $project = (Get-Item -LiteralPath $c).FullName
  } elseif (Test-Path -LiteralPath (Join-Path $selfMathlib 'Mathlib.olean') -PathType Leaf) {
    $primary = (Get-Item -LiteralPath $selfMathlib).FullName
    $project = (Get-Item -LiteralPath $c).FullName
  } elseif (Test-Path -LiteralPath (Join-Path $c 'Mathlib.olean') -PathType Leaf) {
    $primary = (Get-Item -LiteralPath $c).FullName
  } else {
    return $null
  }

  $roots = @($primary)
  if ($project) { $roots += @(GetLakeProjectRoots -Project $project) }

  $libDir = Get-Item -LiteralPath $primary
  if ($libDir.Name -eq 'lean' -and
      $libDir.Parent -and $libDir.Parent.Name -eq 'lib' -and
      $libDir.Parent.Parent -and $libDir.Parent.Parent.Name -eq 'build' -and
      $libDir.Parent.Parent.Parent -and $libDir.Parent.Parent.Parent.Name -eq '.lake') {
    $repo = $libDir.Parent.Parent.Parent.Parent
    $roots += @(GetLakeProjectRoots -Project $repo.FullName)
    if ($repo.Parent -and $repo.Parent.Name -eq 'packages' -and
        $repo.Parent.Parent -and $repo.Parent.Parent.Name -eq '.lake' -and
        $repo.Parent.Parent.Parent) {
      $roots += @(GetLakeProjectRoots -Project $repo.Parent.Parent.Parent.FullName)
    }
  }

  $cleanRoots = @()
  foreach ($root in $roots) {
    if (!$root) { continue }
    if (!(Test-Path -LiteralPath $root -PathType Container)) { continue }
    $full = (Get-Item -LiteralPath $root).FullName
    if ($cleanRoots -notcontains $full) { $cleanRoots += $full }
  }
  if (!$cleanRoots.Count) { return $null }
  return [pscustomobject]@{ Primary = $primary; Roots = [string[]]$cleanRoots }
}

function BuildCached {
  param(
    [string]$Name,
    [string]$Source,
    [string]$CacheKey,
    [string]$Work,
    [string]$Evidence
  )
  $cached = Join-Path $CacheKey ($Name + '.olean')
  $workOlean = Join-Path $Work ($Name + '.olean')
  Copy-Item -LiteralPath $Source -Destination (Join-Path $Work ($Name + '.lean'))
  if (!$Rebuild -and (Test-Path -LiteralPath $cached -PathType Leaf)) {
    Copy-Item -LiteralPath $cached -Destination $workOlean
    Write-Host ("CACHE_HIT=" + $Name)
  } else {
    Write-Host ("BUILD=" + $Name)
    RunNative -LeanArgs @('-j4','-o',($Name + '.olean'),($Name + '.lean')) `
      -Dir $Work -Log (Join-Path $Evidence ($Name + '.log'))
    Copy-Item -LiteralPath $workOlean -Destination $cached -Force
  }
}

$stamp = Get-Date -Format 'yyyyMMdd-HHmmss'
$ev = Join-Path $pkg ("evidence\r-" + $stamp + "-" + [guid]::NewGuid().ToString('N').Substring(0,8))
$work = Join-Path $ev 'work'
[void][IO.Directory]::CreateDirectory($work)

try {
  foreach ($source in @($baseSrc, $spectralSrc, $rootSrc, $schurSrc, $witnessSrc, $kernelSrc, $assemblySrc, $dyadicSrc, $rowSrc, $actualSrc, $infiniteSchurSrc, $serrinFiniteSrc, $serrinInfiniteSrc)) {
    if (!(Test-Path -LiteralPath $source -PathType Leaf)) {
      throw "Missing source: $source"
    }
  }

  $elan = if ($env:ELAN_HOME) { $env:ELAN_HOME } else { Join-Path $env:USERPROFILE '.elan' }
  $bin = Join-Path $elan 'toolchains\leanprover--lean4---v4.33.0\bin'
  $lean = Join-Path $bin 'lean.exe'
  if (!(Test-Path -LiteralPath $lean -PathType Leaf)) {
    throw "Missing native Windows Lean 4.33.0: $lean"
  }
  $env:PATH = "$bin;$env:PATH"

  RunNative -LeanArgs @('--version') -Dir $ev -Log (Join-Path $ev 'version.txt')
  $version = [IO.File]::ReadAllText((Join-Path $ev 'version.txt')).Trim()
  if ($version -cnotmatch '^Lean \(version 4\.33\.0, x86_64-w64-windows-gnu,') {
    throw "Unexpected compiler: $version"
  }

  $candidates = @()
  if ($MathlibProject) { $candidates += $MathlibProject }
  if ($env:NSE_ROUGH_SHEAR_MATHLIB) { $candidates += $env:NSE_ROUGH_SHEAR_MATHLIB }
  if ($env:MATHLIB_PROJECT) { $candidates += $env:MATHLIB_PROJECT }
  if ($env:MATHLIB_DIR) { $candidates += $env:MATHLIB_DIR }
  $native = Join-Path $env:USERPROFILE 'lean-native'
  $candidates += $native
  if (Test-Path -LiteralPath $native -PathType Container) {
    $candidates += @(Get-ChildItem -LiteralPath $native -Directory |
      Sort-Object Name | ForEach-Object { $_.FullName })
  }

  $mathPrimary = $null
  $leanRoots = @()
  [IO.File]::WriteAllText((Join-Path $ev 'CacheProbe.lean'), "import Mathlib`n", $utf8)
  $probeIndex = 0
  foreach ($candidate in @($candidates | Where-Object { $_ } | Select-Object -Unique)) {
    $resolved = ResolveLeanEnvironment -Candidate $candidate
    if (!$resolved) { continue }
    $probeIndex++
    $env:LEAN_PATH = ($resolved.Roots -join ';')
    try {
      RunNative -LeanArgs @('-j4','CacheProbe.lean') -Dir $ev `
        -Log (Join-Path $ev ("cache-probe-" + $probeIndex + ".log"))
      $mathPrimary = $resolved.Primary
      $leanRoots = @($resolved.Roots)
      Write-Host ("ACCEPTED_CACHE=" + $candidate)
      Write-Host ("DEPENDENCY_ROOT_COUNT=" + $leanRoots.Count)
      foreach ($root in $leanRoots) { Write-Host ("LEAN_ROOT=" + $root) }
      break
    } catch {
      Write-Host ("REJECTED_CACHE=" + $candidate)
    }
  }
  if (!$mathPrimary -or !$leanRoots.Count) {
    throw 'No compatible complete cached Mathlib environment found.'
  }

  $cache = if ($env:NSE_ROUGH_SHEAR_CACHE) {
    [IO.Path]::GetFullPath($env:NSE_ROUGH_SHEAR_CACHE)
  } else {
    Join-Path $env:LOCALAPPDATA 'Methlib\nse-rough-shear-l2-433'
  }
  [void][IO.Directory]::CreateDirectory($cache)

  $mathHash = HashFile (Join-Path $mathPrimary 'Mathlib.olean')
  $rootIdentity = ($leanRoots -join "`n")
  $baseHash = HashFile $baseSrc
  $spectralHash = HashFile $spectralSrc
  $rootHash = HashFile $rootSrc
  $schurHash = HashFile $schurSrc
  $witnessHash = HashFile $witnessSrc
  $kernelHash = HashFile $kernelSrc
  $assemblyHash = HashFile $assemblySrc
  $dyadicHash = HashFile $dyadicSrc
  $rowHash = HashFile $rowSrc
  $actualHash = HashFile $actualSrc
  $infiniteSchurHash = HashFile $infiniteSchurSrc
  $serrinFiniteHash = HashFile $serrinFiniteSrc
  $serrinInfiniteHash = HashFile $serrinInfiniteSrc

  # Retain EXACT previous base cache key: the original source was native-pass audited.
  Save (Join-Path $ev 'base-key.txt') @(
    "nse-rough-shear-l2-433-fix5`n" + $version + "`n" +
    $baseHash + "`n" + $mathHash + "`n" + $rootIdentity
  )
  $baseBucket = Join-Path $cache (HashFile (Join-Path $ev 'base-key.txt'))
  [void][IO.Directory]::CreateDirectory($baseBucket)

  $env:LEAN_PATH = (@($work) + $leanRoots) -join ';'
  BuildCached -Name 'NSE_ROUGH_SHEAR_L2_FAMILY' -Source $baseSrc `
    -CacheKey $baseBucket -Work $work -Evidence $ev

  $baseOleanHash = HashFile (Join-Path $work 'NSE_ROUGH_SHEAR_L2_FAMILY.olean')
  Save (Join-Path $ev 'spectral-key.txt') @(
    "s-dir-l2-433-spectral-v0_1_0`n" + $version + "`n" +
    $spectralHash + "`n" + $baseOleanHash + "`n" +
    $mathHash + "`n" + $rootIdentity
  )
  $spectralBucket = Join-Path $cache (HashFile (Join-Path $ev 'spectral-key.txt'))
  [void][IO.Directory]::CreateDirectory($spectralBucket)

  BuildCached -Name 'S_DIR_L2_SPECTRAL' -Source $spectralSrc `
    -CacheKey $spectralBucket -Work $work -Evidence $ev


  # Reuse the exact native-audited FIX1 witness cache key.
  Save (Join-Path $ev 'witness-key.txt') @(
    "nse-rough-shear-strict-nonempty-433-v0_1_1-fix1`n" + $version + "`n" +
    $witnessHash + "`n" + $baseOleanHash + "`n" + $mathHash + "`n" + $rootIdentity
  )
  $witnessBucket = Join-Path $cache (HashFile (Join-Path $ev 'witness-key.txt'))
  [void][IO.Directory]::CreateDirectory($witnessBucket)
  BuildCached -Name 'NSE_ROUGH_SHEAR_STRICT_NONEMPTY' -Source $witnessSrc `
    -CacheKey $witnessBucket -Work $work -Evidence $ev

  $spectralOleanHash = HashFile (Join-Path $work 'S_DIR_L2_SPECTRAL.olean')
  Save (Join-Path $ev 'root-key.txt') @(
    "s-dir-l2-global-regularity-433-v0_1_0`n" + $version + "`n" +
    $rootHash + "`n" + $spectralOleanHash + "`n" +
    $mathHash + "`n" + $rootIdentity
  )
  $rootBucket = Join-Path $cache (HashFile (Join-Path $ev 'root-key.txt'))
  [void][IO.Directory]::CreateDirectory($rootBucket)

  BuildCached -Name 'S_DIR_L2_GLOBAL_REGULARITY' -Source $rootSrc `
    -CacheKey $rootBucket -Work $work -Evidence $ev

  $rootOleanHash = HashFile (Join-Path $work 'S_DIR_L2_GLOBAL_REGULARITY.olean')
  Save (Join-Path $ev 'schur-key.txt') @(
    "s-dir-l2-433-schur-v0_2_0`n" + $version + "`n" +
    $schurHash + "`n" + $rootOleanHash + "`n" +
    $mathHash + "`n" + $rootIdentity
  )
  $schurBucket = Join-Path $cache (HashFile (Join-Path $ev 'schur-key.txt'))
  [void][IO.Directory]::CreateDirectory($schurBucket)
  BuildCached -Name 'S_DIR_L2_SCHUR_FRONTIER' -Source $schurSrc `
    -CacheKey $schurBucket -Work $work -Evidence $ev


  $schurOleanHash = HashFile (Join-Path $work 'S_DIR_L2_SCHUR_FRONTIER.olean')
  Save (Join-Path $ev 'kernel-key.txt') @(
    "s-dir-l2-433-kernel-v0_3_0`n" + $version + "`n" +
    $kernelHash + "`n" + $schurOleanHash + "`n" +
    $mathHash + "`n" + $rootIdentity
  )
  $kernelBucket = Join-Path $cache (HashFile (Join-Path $ev 'kernel-key.txt'))
  [void][IO.Directory]::CreateDirectory($kernelBucket)
  BuildCached -Name 'S_DIR_L2_SCHUR_KERNEL' -Source $kernelSrc `
    -CacheKey $kernelBucket -Work $work -Evidence $ev

  $kernelOleanHash = HashFile (Join-Path $work 'S_DIR_L2_SCHUR_KERNEL.olean')
  Save (Join-Path $ev 'assembly-key.txt') @(
    "s-dir-l2-433-assembly-v0_3_0`n" + $version + "`n" +
    $assemblyHash + "`n" + $kernelOleanHash + "`n" +
    $mathHash + "`n" + $rootIdentity
  )
  $assemblyBucket = Join-Path $cache (HashFile (Join-Path $ev 'assembly-key.txt'))
  [void][IO.Directory]::CreateDirectory($assemblyBucket)
  BuildCached -Name 'S_DIR_L2_PROOF_ASSEMBLY' -Source $assemblySrc `
    -CacheKey $assemblyBucket -Work $work -Evidence $ev

  # The new dyadic module is compiled AFTER every native-audited old module.
  $assemblyOleanHash = HashFile (Join-Path $work 'S_DIR_L2_PROOF_ASSEMBLY.olean')
  Save (Join-Path $ev 'dyadic-key.txt') @(
    "s-dir-l2-433-dyadic-schur-v0_4_1-fix1`n" + $version + "`n" +
    $dyadicHash + "`n" + $assemblyOleanHash + "`n" +
    $mathHash + "`n" + $rootIdentity
  )
  $dyadicBucket = Join-Path $cache (HashFile (Join-Path $ev 'dyadic-key.txt'))
  [void][IO.Directory]::CreateDirectory($dyadicBucket)
  BuildCached -Name 'S_DIR_L2_DYADIC_SCHUR' -Source $dyadicSrc `
    -CacheKey $dyadicBucket -Work $work -Evidence $ev

  # The new row module is downstream of the exact native-passed v0.4.1 source.
  $dyadicOleanHash = HashFile (Join-Path $work 'S_DIR_L2_DYADIC_SCHUR.olean')
  Save (Join-Path $ev 'row-key.txt') @(
    "s-dir-l2-433-dyadic-row-v0_5_1-fix1`n" + $version + "`n" +
    $rowHash + "`n" + $dyadicOleanHash + "`n" +
    $mathHash + "`n" + $rootIdentity
  )
  $rowBucket = Join-Path $cache (HashFile (Join-Path $ev 'row-key.txt'))
  [void][IO.Directory]::CreateDirectory($rowBucket)
  BuildCached -Name 'S_DIR_L2_DYADIC_ROW' -Source $rowSrc `
    -CacheKey $rowBucket -Work $work -Evidence $ev


  # New actual dyadic shell row module, downstream of the nine native-passed modules.
  $rowOleanHash = HashFile (Join-Path $work 'S_DIR_L2_DYADIC_ROW.olean')
  Save (Join-Path $ev 'actual-key.txt') @(
    "s-dir-l2-433-actual-shells-v0_6_0`n" + $version + "`n" +
    $actualHash + "`n" + $rowOleanHash + "`n" +
    $mathHash + "`n" + $rootIdentity
  )
  $actualBucket = Join-Path $cache (HashFile (Join-Path $ev 'actual-key.txt'))
  [void][IO.Directory]::CreateDirectory($actualBucket)
  BuildCached -Name 'S_DIR_L2_ACTUAL_SHELLS' -Source $actualSrc `
    -CacheKey $actualBucket -Work $work -Evidence $ev


  # New infinite Schur module, downstream of all ten externally audited modules.
  $actualOleanHash = HashFile (Join-Path $work 'S_DIR_L2_ACTUAL_SHELLS.olean')
  Save (Join-Path $ev 'infinite-schur-key.txt') @(
    "s-dir-l2-433-infinite-schur-v0_7_1-fix1`n" + $version + "`n" +
    $infiniteSchurHash + "`n" + $actualOleanHash + "`n" +
    $mathHash + "`n" + $rootIdentity
  )
  $infiniteSchurBucket = Join-Path $cache (HashFile (Join-Path $ev 'infinite-schur-key.txt'))
  [void][IO.Directory]::CreateDirectory($infiniteSchurBucket)
  BuildCached -Name 'S_DIR_L2_INFINITE_SCHUR' -Source $infiniteSchurSrc `
    -CacheKey $infiniteSchurBucket -Work $work -Evidence $ev


  # Independent new physical-time finite-mode Serrin module: cache keys of all
  # previous 11 PASS modules are preserved exactly.
  $infiniteSchurOleanHash = HashFile (Join-Path $work 'S_DIR_L2_INFINITE_SCHUR.olean')
  Save (Join-Path $ev 'serrin-finite-key.txt') @(
    "s-dir-l2-433-serrin-finite-v0_8_1-fix1`n" + $version + "`n" +
    $serrinFiniteHash + "`n" + $infiniteSchurOleanHash + "`n" +
    $mathHash + "`n" + $rootIdentity
  )
  $serrinFiniteBucket = Join-Path $cache (HashFile (Join-Path $ev 'serrin-finite-key.txt'))
  [void][IO.Directory]::CreateDirectory($serrinFiniteBucket)
  BuildCached -Name 'S_DIR_L2_SERRIN_FINITE' -Source $serrinFiniteSrc `
    -CacheKey $serrinFiniteBucket -Work $work -Evidence $ev

  # v0.9.0 standalone monotone-convergence module. Every earlier
  # source and cache key is retained exactly from the external PASS run.
  $serrinFiniteOleanHash = HashFile (Join-Path $work 'S_DIR_L2_SERRIN_FINITE.olean')
  Save (Join-Path $ev 'serrin-infinite-key.txt') @(
    "s-dir-l2-433-serrin-infinite-v0_9_1-fix1`n" + $version + "`n" +
    $serrinInfiniteHash + "`n" + $serrinFiniteOleanHash + "`n" +
    $mathHash + "`n" + $rootIdentity
  )
  $serrinInfiniteBucket = Join-Path $cache (HashFile (Join-Path $ev 'serrin-infinite-key.txt'))
  [void][IO.Directory]::CreateDirectory($serrinInfiniteBucket)
  BuildCached -Name 'S_DIR_L2_SERRIN_INFINITE' -Source $serrinInfiniteSrc `
    -CacheKey $serrinInfiniteBucket -Work $work -Evidence $ev

  $audit = @'
import S_DIR_L2_SERRIN_INFINITE
import S_DIR_L2_SERRIN_FINITE
import S_DIR_L2_INFINITE_SCHUR
import S_DIR_L2_ACTUAL_SHELLS
import S_DIR_L2_DYADIC_ROW
import S_DIR_L2_DYADIC_SCHUR
import S_DIR_L2_PROOF_ASSEMBLY
import NSE_ROUGH_SHEAR_STRICT_NONEMPTY
set_option format.width 100000

#check SDirL2.S_DIR_L2_SPECTRAL_REGULARITY
#check SDirL2.S_DIR_L2_M7_FOURIER_FLUX_ZERO
#check SDirL2.S_DIR_L2_M7_FOURIER_DENSITY_ZERO
#check SDirL2.S_DIR_L2_GLOBAL_REGULARITY
#check SDirL2.AnalyticEndpointCertificates
#check SDirL2.S_DIR_L2_GLOBAL_REGULARITY_of_certificates
#check SDirL2.S_DIR_L2_GLOBAL_REGULARITY_FOURIER_M7_UNCONDITIONAL
#check SDirL2.S_DIR_L2_PLANE_PROJECTION_INJECTIVE
#check SDirL2.S_DIR_L2_PLANE_FINITE_CUBE_CARD
#check SDirL2.S_DIR_L2_WEIGHTED_FINITE_SCHUR
#check SDirL2.S_DIR_L2_FINITE_HEAT_KERNEL_SCHUR
#check SDirL2.S_DIR_L2_SERRIN_CONSTANT_NORMALIZATION
#check SDirL2.S_DIR_L2_GLOBAL_REGULARITY_PROOF_SPINE
#check SDirL2.S_DIR_L2_P1_PHYSICAL_SYNTHESIS
#check SDirL2.S_DIR_L2_P2_SERRIN
#check SDirL2.S_DIR_L2_P3_LERAY_HOPF_UNIQUENESS
#check NSERoughShearL2Family.StrictNonemptyWitness.NSE_ROUGH_SHEAR_STRICT_SUBFAMILY_NONEMPTY
#check NSERoughShearL2Family.StrictNonemptyWitness.EXISTS_NSE_ROUGH_SHEAR_STRICT_POSITIVE_TIME_FLOW
#check SDirL2.S_DIR_L2_RADIUS_TO_STRICT_CUBE
#check SDirL2.S_DIR_L2_PLANE_STRICT_CUBE_CARD
#check SDirL2.S_DIR_L2_DYADIC_PLANE_BALL_CARD
#check SDirL2.S_DIR_L2_DYADIC_KERNEL_TELESCOPIC_STEP
#check SDirL2.S_DIR_L2_DYADIC_KERNEL_STEP
#check SDirL2.S_DIR_L2_DYADIC_KERNEL_PREFIX_BOUND
#check SDirL2.S_DIR_L2_DYADIC_SERRIN_CONSTANT_LE_FROZEN
#check SDirL2.S_DIR_L2_DYADIC_KERNEL_TERM_NONNEG
#check SDirL2.S_DIR_L2_DYADIC_KERNEL_SUMMABLE
#check SDirL2.S_DIR_L2_DYADIC_KERNEL_TSUM_BOUND
#check SDirL2.S_DIR_L2_INFINITE_ROW_FROM_ALL_FINITE_BOUNDS
#check SDirL2.S_DIR_L2_DYADIC_ROW_POINTWISE
#check SDirL2.S_DIR_L2_DYADIC_FINITE_SHELL_BUDGET
#check SDirL2.S_DIR_L2_DYADIC_PLANE_FINITE_SHELL_BUDGET
#check SDirL2.S_DIR_L2_FINITE_ROW_OF_DYADIC_SHELL_PARTITION

#check SDirL2.S_DIR_L2_SUPNORM_COORD_LE
#check SDirL2.S_DIR_L2_SUPNORM_POS
#check SDirL2.S_DIR_L2_SUPNORM_DYADIC_BRACKET
#check SDirL2.S_DIR_L2_SUPNORM_LE_EUCLIDEAN
#check SDirL2.S_DIR_L2_SUPNORM_SHELL_RADIUS_LOWER
#check SDirL2.S_DIR_L2_SUPNORM_SHELL_COORD_UPPER
#check SDirL2.S_DIR_L2_ACTUAL_SHELL_PARTITION
#check SDirL2.S_DIR_L2_ACTUAL_SHELL_DISJOINT
#check SDirL2.S_DIR_L2_ACTUAL_SHELL_CARD
#check SDirL2.S_DIR_L2_ACTUAL_SHELL_RADIUS_LOWER
#check SDirL2.S_DIR_L2_ACTUAL_SHELL_ROW_BUDGET
#check SDirL2.S_DIR_L2_ACTUAL_FINITE_PLANE_ROW
#check SDirL2.S_DIR_L2_NONZERO_RADIUS_POS
#check SDirL2.S_DIR_L2_PLANE_RADIAL_ROW_NONNEG
#check SDirL2.S_DIR_L2_FINITE_AMBIENT_PLANE_ROW
#check SDirL2.S_DIR_L2_ACTUAL_INFINITE_LATTICE_ROW

#check SDirL2.S_DIR_L2_ACTIVE_RADIUS_POS
#check SDirL2.S_DIR_L2_ACTIVE_HEAT_KERNEL_ROW_EQ
#check SDirL2.S_DIR_L2_ACTIVE_FINITE_HEAT_ROW
#check SDirL2.S_DIR_L2_ACTIVE_FINITE_HEAT_SCHUR
#check SDirL2.S_DIR_L2_GENERIC_INFINITE_SCHUR_FROM_FINITE_SQUARES
#check SDirL2.S_DIR_L2_INFINITE_NONNEG_WEIGHTED_SCHUR
#check SDirL2.S_DIR_L2_INFINITE_WEIGHTED_SCHUR

#check SDirL2.S_DIR_L2_EXPONENTIAL_INTEGRABLE_ON_Ioi
#check SDirL2.S_DIR_L2_EXPONENTIAL_INTEGRAL_ON_Ioi
#check SDirL2.S_DIR_L2_TWO_HEAT_MULTIPLIERS
#check SDirL2.S_DIR_L2_HEAT_PAIR_TIME_INTEGRAL
#check SDirL2.S_DIR_L2_FINITE_HEAT_AMPLITUDE_SQUARE
#check SDirL2.S_DIR_L2_FINITE_HEAT_PAIR_INTEGRABLE
#check SDirL2.S_DIR_L2_FINITE_HEAT_PAIR_WEIGHTED_INTEGRAL
#check SDirL2.S_DIR_L2_FINITE_HEAT_ENERGY_INTEGRAL
#check SDirL2.S_DIR_L2_FINITE_SERRIN_HEAT_ESTIMATE


#check SDirL2.S_DIR_L2_FINITE_HEAT_AMPLITUDE_NONNEG
#check SDirL2.S_DIR_L2_FINITE_HEAT_AMPLITUDE_MONO
#check SDirL2.S_DIR_L2_FINITE_HEAT_SQUARE_INTEGRABLE
#check SDirL2.S_DIR_L2_GENERIC_MONOTONE_L2_LINTEGRAL
#check SDirL2.S_DIR_L2_INFINITE_SERRIN_HEAT
#check SDirL2.S_DIR_L2_INFINITE_SERRIN_FROZEN_MAJORANT

#print axioms SDirL2.S_DIR_L2_SPECTRAL_REGULARITY
#print axioms SDirL2.S_DIR_L2_M7_FOURIER_FLUX_ZERO
#print axioms SDirL2.S_DIR_L2_M7_FOURIER_DENSITY_ZERO
#print axioms SDirL2.S_DIR_L2_GLOBAL_REGULARITY_of_certificates
#print axioms SDirL2.S_DIR_L2_GLOBAL_REGULARITY_FOURIER_M7_UNCONDITIONAL
#print axioms SDirL2.S_DIR_L2_PLANE_PROJECTION_INJECTIVE
#print axioms SDirL2.S_DIR_L2_PLANE_FINITE_CUBE_CARD
#print axioms SDirL2.S_DIR_L2_WEIGHTED_FINITE_SCHUR
#print axioms SDirL2.S_DIR_L2_ABSTRACT_KERNEL_NONNEG
#print axioms SDirL2.S_DIR_L2_ABSTRACT_KERNEL_SYMMETRIC
#print axioms SDirL2.S_DIR_L2_FINITE_HEAT_KERNEL_SCHUR
#print axioms SDirL2.S_DIR_L2_SERRIN_CONSTANT_NORMALIZATION
#print axioms SDirL2.S_DIR_L2_GLOBAL_REGULARITY_PROOF_SPINE
#print axioms NSERoughShearL2Family.StrictNonemptyWitness.harmonicDatum_not_hhalf
#print axioms NSERoughShearL2Family.StrictNonemptyWitness.NSE_ROUGH_SHEAR_STRICT_SUBFAMILY_NONEMPTY
#print axioms NSERoughShearL2Family.StrictNonemptyWitness.EXISTS_NSE_ROUGH_SHEAR_STRICT_POSITIVE_TIME_FLOW
#print axioms SDirL2.S_DIR_L2_RADIUS_TO_STRICT_CUBE
#print axioms SDirL2.S_DIR_L2_PLANE_STRICT_CUBE_CARD
#print axioms SDirL2.S_DIR_L2_DYADIC_PLANE_BALL_CARD
#print axioms SDirL2.S_DIR_L2_DYADIC_KERNEL_TELESCOPIC_STEP
#print axioms SDirL2.S_DIR_L2_DYADIC_KERNEL_STEP
#print axioms SDirL2.S_DIR_L2_DYADIC_KERNEL_PREFIX_BOUND
#print axioms SDirL2.S_DIR_L2_DYADIC_SERRIN_CONSTANT_LE_FROZEN
#print axioms SDirL2.S_DIR_L2_DYADIC_KERNEL_TERM_NONNEG
#print axioms SDirL2.S_DIR_L2_DYADIC_KERNEL_SUMMABLE
#print axioms SDirL2.S_DIR_L2_DYADIC_KERNEL_TSUM_BOUND
#print axioms SDirL2.S_DIR_L2_INFINITE_ROW_FROM_ALL_FINITE_BOUNDS
#print axioms SDirL2.S_DIR_L2_DYADIC_ROW_POINTWISE
#print axioms SDirL2.S_DIR_L2_DYADIC_FINITE_SHELL_BUDGET
#print axioms SDirL2.S_DIR_L2_DYADIC_PLANE_FINITE_SHELL_BUDGET
#print axioms SDirL2.S_DIR_L2_FINITE_ROW_OF_DYADIC_SHELL_PARTITION
#print axioms SDirL2.S_DIR_L2_SUPNORM_COORD_LE
#print axioms SDirL2.S_DIR_L2_SUPNORM_POS
#print axioms SDirL2.S_DIR_L2_SUPNORM_DYADIC_BRACKET
#print axioms SDirL2.S_DIR_L2_SUPNORM_LE_EUCLIDEAN
#print axioms SDirL2.S_DIR_L2_SUPNORM_SHELL_RADIUS_LOWER
#print axioms SDirL2.S_DIR_L2_SUPNORM_SHELL_COORD_UPPER
#print axioms SDirL2.S_DIR_L2_ACTUAL_SHELL_PARTITION
#print axioms SDirL2.S_DIR_L2_ACTUAL_SHELL_DISJOINT
#print axioms SDirL2.S_DIR_L2_ACTUAL_SHELL_CARD
#print axioms SDirL2.S_DIR_L2_ACTUAL_SHELL_RADIUS_LOWER
#print axioms SDirL2.S_DIR_L2_ACTUAL_SHELL_ROW_BUDGET
#print axioms SDirL2.S_DIR_L2_ACTUAL_FINITE_PLANE_ROW
#print axioms SDirL2.S_DIR_L2_NONZERO_RADIUS_POS
#print axioms SDirL2.S_DIR_L2_PLANE_RADIAL_ROW_NONNEG
#print axioms SDirL2.S_DIR_L2_FINITE_AMBIENT_PLANE_ROW
#print axioms SDirL2.S_DIR_L2_ACTUAL_INFINITE_LATTICE_ROW
#print axioms SDirL2.S_DIR_L2_ACTIVE_RADIUS_POS
#print axioms SDirL2.S_DIR_L2_ACTIVE_HEAT_KERNEL_ROW_EQ
#print axioms SDirL2.S_DIR_L2_ACTIVE_FINITE_HEAT_ROW
#print axioms SDirL2.S_DIR_L2_ACTIVE_FINITE_HEAT_SCHUR
#print axioms SDirL2.S_DIR_L2_GENERIC_INFINITE_SCHUR_FROM_FINITE_SQUARES
#print axioms SDirL2.S_DIR_L2_INFINITE_NONNEG_WEIGHTED_SCHUR
#print axioms SDirL2.S_DIR_L2_INFINITE_WEIGHTED_SCHUR
#print axioms SDirL2.S_DIR_L2_EXPONENTIAL_INTEGRABLE_ON_Ioi
#print axioms SDirL2.S_DIR_L2_EXPONENTIAL_INTEGRAL_ON_Ioi
#print axioms SDirL2.S_DIR_L2_TWO_HEAT_MULTIPLIERS
#print axioms SDirL2.S_DIR_L2_HEAT_PAIR_TIME_INTEGRAL
#print axioms SDirL2.S_DIR_L2_FINITE_HEAT_AMPLITUDE_SQUARE
#print axioms SDirL2.S_DIR_L2_FINITE_HEAT_PAIR_INTEGRABLE
#print axioms SDirL2.S_DIR_L2_FINITE_HEAT_PAIR_WEIGHTED_INTEGRAL
#print axioms SDirL2.S_DIR_L2_FINITE_HEAT_ENERGY_INTEGRAL
#print axioms SDirL2.S_DIR_L2_FINITE_SERRIN_HEAT_ESTIMATE
#print axioms SDirL2.S_DIR_L2_FINITE_HEAT_AMPLITUDE_NONNEG
#print axioms SDirL2.S_DIR_L2_FINITE_HEAT_AMPLITUDE_MONO
#print axioms SDirL2.S_DIR_L2_FINITE_HEAT_SQUARE_INTEGRABLE
#print axioms SDirL2.S_DIR_L2_GENERIC_MONOTONE_L2_LINTEGRAL
#print axioms SDirL2.S_DIR_L2_INFINITE_SERRIN_HEAT
#print axioms SDirL2.S_DIR_L2_INFINITE_SERRIN_FROZEN_MAJORANT
'@
  [IO.File]::WriteAllText((Join-Path $work 'Audit.lean'), $audit, $utf8)
  RunNative -LeanArgs @('-j4','Audit.lean') -Dir $work -Log (Join-Path $ev 'audit.log')

  $auditText = [IO.File]::ReadAllText((Join-Path $ev 'audit.log'), $utf8)
  $allowed = @('propext','Classical.choice','Quot.sound')
  $reports = [regex]::Matches(
    $auditText,
    "(?ms)'(?<name>[A-Za-z0-9_.]+)' (?:depends on axioms:\s*\[(?<items>[^\]]*)\]|does not depend on any axioms)"
  )
  if ($reports.Count -ne 69) {
    throw "Expected 69 theorem-level axiom reports; found $($reports.Count)."
  }
  foreach ($report in $reports) {
    $items = $report.Groups['items'].Value
    if ($items) {
      foreach ($ax in ($items -split ',')) {
        $name = $ax.Trim()
        if ($name -and $allowed -cnotcontains $name) {
          throw "Unapproved axiom $name in $($report.Groups['name'].Value)"
        }
      }
    }
  }

  $result = @(
    'PACKAGE=S_DIR_L2_GLOBAL_REGULARITY_433_v0_9_1_INFINITE_SERRIN_FIX1'
    ('EVIDENCE=' + $ev)
    ('COMPILER=' + $version)
    ('CACHED_MATHLIB=' + $mathPrimary)
    ('DEPENDENCY_ROOT_COUNT=' + $leanRoots.Count)
    ('BASE_SOURCE_SHA256=' + $baseHash)
    ('SPECTRAL_SOURCE_SHA256=' + $spectralHash)
    ('ROOT_SOURCE_SHA256=' + $rootHash)
    ('SCHUR_SOURCE_SHA256=' + $schurHash)
    ('WITNESS_SOURCE_SHA256=' + $witnessHash)
    ('KERNEL_SOURCE_SHA256=' + $kernelHash)
    ('ASSEMBLY_SOURCE_SHA256=' + $assemblyHash)
    ('DYADIC_SOURCE_SHA256=' + $dyadicHash)
    ('ROW_SOURCE_SHA256=' + $rowHash)
    ('ACTUAL_SOURCE_SHA256=' + $actualHash)
    ('INFINITE_SCHUR_SOURCE_SHA256=' + $infiniteSchurHash)
    ('SERRIN_FINITE_SOURCE_SHA256=' + $serrinFiniteHash)
    ('SERRIN_INFINITE_SOURCE_SHA256=' + $serrinInfiniteHash)
    'PROJECT_BUILD=PASS'
    'THEOREM_AXIOM_AUDITS=69'
    'AXIOMS=STANDARD_ONLY'
    'DIRECTIONAL_SPECTRAL_REGULARITY=PASS'
    'FINITE_FOURIER_M7_ZERO=PASS'
    'CONDITIONAL_ENDPOINT_COMPOSITION=PASS'
    'PLANE_PROJECTION_INJECTIVITY=PASS'
    'FINITE_PLANE_CUBE_COUNTING=PASS'
    'FINITE_WEIGHTED_SCHUR_REDUCTION=PASS'
    'EXPLICIT_FIXED_AXIS_ROUGH_NONEMPTY=PASS'
    'FINITE_HEAT_KERNEL_SCHUR=PASS'
    'SERRIN_CONSTANT_NORMALIZATION=PASS'
    'DETERMINISTIC_CONDITIONAL_ROOT_ASSEMBLY=PASS'
    'DYADIC_PLANE_BALL_COUNT=PASS'
    'DYADIC_TELESCOPIC_PREFIX=PASS'
    'DYADIC_SERRIN_CONSTANT_LE_FROZEN=PASS'
    'INFINITE_DYADIC_MAJORANT_TSUM=PASS'
    'NONNEGATIVE_FINITE_TO_INFINITE_ROW_ADAPTER=PASS'
    'CONDITIONAL_FINITE_SHELL_GEOMETRIC_ROW=PASS'
    'NEW_UNCONDITIONAL_ROOT_THEOREM=NOT_INCLUDED'
    'ROOT_TARGET_IS_DEFINITION=TRUE'
    'ROOT_UNCONDITIONAL_PHYSICAL_THEOREM=NOT_PROVED'
    'PHYSICAL_TORUS_SYNTHESIS_ADAPTER=OPEN'
    'UNIFORM_RANK_TWO_SCHUR_SERRIN=PARTIAL_ACTUAL_LATTICE_ROW_ONLY'
    'DYADIC_INFINITE_ROW_COMPOSITION=PASS'
    'ACTUAL_PLANE_SHELL_PARTITION=PASS'
    'ACTUAL_INFINITE_LATTICE_ROW=PASS'
    'INFINITE_WEIGHTED_SCHUR=PASS'
    'P2_GEOMETRIC_AND_INFINITE_SCHUR=PASS'
    'P2_PHYSICAL_SERRIN_REALIZATION=OPEN'
    'UNRESTRICTED_LERAY_HOPF_UNIQUENESS_ADAPTER=OPEN'
    'FINITE_TIME_HEAT_PAIR_INTEGRAL=PASS'
    'FINITE_TRUNCATION_SERRIN_BOUND=PASS'
    'P2_FINITE_TIME_REALIZATION=PASS'
    'P2_INFINITE_PHYSICAL_SERRIN_REALIZATION=OPEN'
    'P2_MONOTONE_FINITE_SUPREMUM_MAJORANT=PASS'
    'P2_EXHAUSTIVE_SEQUENCE_IDENTITY=OPEN'
    'P2_INFINITE_SERRIN_LINTEGRAL=PASS'
    'NEW_UNCONDITIONAL_ROOT_THEOREM=NOT_INCLUDED'
    'RUN=PASS'
  )
  Save (Join-Path $ev 'result.txt') $result
  $result | ForEach-Object { Write-Host $_ }
  exit 0
} catch {
  $result = @(
    'RUN=FAIL'
    ('REASON=' + $_.Exception.Message)
    ('EVIDENCE=' + $ev)
  )
  Save (Join-Path $ev 'result.txt') $result
  $result | ForEach-Object { Write-Host $_ }
  exit 1
}
