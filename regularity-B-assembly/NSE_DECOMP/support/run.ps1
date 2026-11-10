[CmdletBinding()]
param(
  [string]$MathlibProject = '',
  [switch]$Full
)

# NSE_DECOMP v0_1_9_FIX2 FASTCACHE. Native Windows/installed Lean, no network or dependency builds.
# The compile checks only a theorem conditional on explicit AnalyticEndpoints.
$ErrorActionPreference = 'Stop'
$ProgressPreference = 'SilentlyContinue'
$pkg = Split-Path -Parent $PSScriptRoot
$src = Join-Path $pkg 'NSE_DECOMP.lean'
$buildLog = Join-Path $pkg 'run-build.log'
$auditLog = Join-Path $pkg 'run-audit.log'
$sealPath = Join-Path $pkg 'run-cache.seal'
$expected = '4.34.0-rc1'
if ($env:NSE_DECOMP_EXPECTED_LEAN) { $expected = $env:NSE_DECOMP_EXPECTED_LEAN }
$threadCount = 16
if ($env:NSE_DECOMP_THREADS) {
  $threadsCandidate = 0
  if ([int]::TryParse($env:NSE_DECOMP_THREADS, [ref]$threadsCandidate) -and
      $threadsCandidate -ge 1 -and $threadsCandidate -le 64) { $threadCount = $threadsCandidate }
}
$enc = New-Object System.Text.UTF8Encoding($false)

function SaveText([string]$path, [string[]]$lines) {
  [System.IO.File]::WriteAllLines($path, $lines, $enc)
}
function HashFile([string]$path) {
  return (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant()
}
function HashText([string]$value) {
  $sha = [System.Security.Cryptography.SHA256]::Create()
  try {
    $bytes = $enc.GetBytes($value)
    return ([BitConverter]::ToString($sha.ComputeHash($bytes))).Replace('-', '').ToLowerInvariant()
  } finally { $sha.Dispose() }
}
function ExistsFile([string]$path) {
  return ((Test-Path -LiteralPath $path -PathType Leaf) -and
          ((Get-Item -LiteralPath $path).Length -gt 0))
}

try {
  if (-not (ExistsFile $src)) { throw "SOURCE_MISSING=$src" }
  $elanHome = if ($env:ELAN_HOME) { $env:ELAN_HOME } else { Join-Path $env:USERPROFILE '.elan' }
  $toolchainDir = Join-Path $elanHome ("toolchains\leanprover--lean4---v" + $expected + "\bin")
  $lean = Join-Path $toolchainDir 'lean.exe'
  $lake = Join-Path $toolchainDir 'lake.exe'
  if (-not (ExistsFile $lean) -or -not (ExistsFile $lake)) {
    throw "INSTALLED_TOOLCHAIN_MISSING=$toolchainDir (no automatic toolchain installation)"
  }

  $candidates = New-Object 'System.Collections.Generic.List[string]'
  $seen = @{}
  function AddCandidate([string]$value) {
    if ([string]::IsNullOrWhiteSpace($value)) { return }
    try { $key = [System.IO.Path]::GetFullPath($value) } catch { return }
    $id = $key.ToLowerInvariant()
    if (-not $seen.ContainsKey($id)) { $seen[$id] = $true; $candidates.Add($key) }
  }
  $strict = $false
  if ($MathlibProject) {
    AddCandidate $MathlibProject
    $strict = $true
  } elseif ($env:NSE_DECOMP_LAKE_ROOT) {
    AddCandidate $env:NSE_DECOMP_LAKE_ROOT
    $strict = $true
  } else {
    AddCandidate $pkg
    AddCandidate (Join-Path $env:USERPROFILE 'Lean\mathlib4')
    AddCandidate (Join-Path $env:USERPROFILE 'lean-native\awpi_phi_rh_lean_sieved_v0_1_9_FIX2')
    foreach ($parent in @('LeanRuns', 'lean-native', 'LeanProjects', 'Lean', 'Documents\Lean', 'Downloads')) {
      $dir = Join-Path $env:USERPROFILE $parent
      if (Test-Path -LiteralPath $dir -PathType Container) {
        AddCandidate $dir
        Get-ChildItem -LiteralPath $dir -Directory -ErrorAction SilentlyContinue |
          Sort-Object Name | ForEach-Object { AddCandidate $_.FullName }
      }
    }
  }

  $workspace = $null
  $olean = $null
  $candidateCount = 0
  foreach ($candidate in $candidates) {
    if (-not (Test-Path -LiteralPath $candidate -PathType Container)) { continue }
    $candidateCount++
    $hasLakefile = (Test-Path -LiteralPath (Join-Path $candidate 'lakefile.toml') -PathType Leaf) -or
                   (Test-Path -LiteralPath (Join-Path $candidate 'lakefile.lean') -PathType Leaf)
    if (-not $hasLakefile) { continue }
    $pin = Join-Path $candidate 'lean-toolchain'
    if (-not (Test-Path -LiteralPath $pin -PathType Leaf)) { continue }
    $declaredToolchain = ((Get-Content -LiteralPath $pin -Raw).Trim())
    if ($declaredToolchain -ne ('leanprover/lean4:v' + $expected)) { continue }
    foreach ($test in @(
       (Join-Path $candidate '.lake\packages\mathlib\.lake\build\lib\lean\Mathlib.olean'),
       (Join-Path $candidate '.lake\build\lib\lean\Mathlib.olean')
    )) {
      if (ExistsFile $test) { $workspace = $candidate; $olean = $test; break }
    }
    if ($workspace) { break }
  }
  if (-not $workspace) {
    throw ('CACHE_MISS: no pinned existing Mathlib.olean for Lean ' + $expected +
      '. Inspected ' + $candidateCount + ' directories. ' +
      'Set NSE_DECOMP_LAKE_ROOT to an existing fully cached Mathlib Lake project; no downloads/rebuilds were attempted.')
  }

  # Fingerprint all inputs that the fast-cache decision relies upon.
  $manifest = Join-Path $workspace 'lake-manifest.json'
  $manifestHash = if (ExistsFile $manifest) { HashFile $manifest } else { 'NO_MANIFEST' }
  $lakefileToml = Join-Path $workspace 'lakefile.toml'
  $lakefileLean = Join-Path $workspace 'lakefile.lean'
  $lakefileHash = if (ExistsFile $lakefileToml) { HashFile $lakefileToml } elseif (ExistsFile $lakefileLean) { HashFile $lakefileLean } else { 'NO_LAKEFILE' }
  $details = @(
    'CACHE_FORMAT=NSE_DECOMP_FASTCACHE_v0_1_9_FIX2',
    "EXPECTED=$expected", "WORKSPACE=$workspace", "MATHLIB_OLEAN=$olean",
    ('SRC_SHA256=' + (HashFile $src)),
    ('MATHLIB_OLEAN_SHA256=' + (HashFile $olean)),
    ('LEAN_EXE_SHA256=' + (HashFile $lean)),
    ('LAKE_EXE_SHA256=' + (HashFile $lake)),
    "MANIFEST_SHA256=$manifestHash", "LAKEFILE_SHA256=$lakefileHash",
    "THREADS=$threadCount"
  )
  $seal = HashText ($details -join "`n")

  Write-Host "NSE_DECOMP_FASTCACHE=v0_1_9_FIX2"
  Write-Host "PROJECT_ROOT=$workspace"
  Write-Host "MATHLIB_CACHE=EXISTING_OLEAN"
  Write-Host "DEPENDENCY_UPDATE=NOT_INVOKED"
  Write-Host "CACHE_DOWNLOAD=NOT_INVOKED"
  Write-Host "THREADS=$threadCount"
  Write-Host "CONDITIONAL_ANALYTIC_ENDPOINTS=OPEN"

  if (-not $Full -and (ExistsFile $sealPath) -and
      (Get-Content -LiteralPath $sealPath -Raw).Trim() -eq $seal -and
      (ExistsFile $buildLog) -and (ExistsFile $auditLog)) {
    $auditString = Get-Content -LiteralPath $auditLog -Raw
    if ($auditString.Contains('BUILD=PASS') -and
        $auditString.Contains('AXIOM_AUDIT=STANDARD_ONLY') -and
        $auditString.Contains('ROOT_STATUS=CONDITIONAL')) {
      Write-Host 'CACHE_HIT=SEALED_ROOT_AND_AUDIT'
      Write-Host 'BUILD=REUSED_PREVIOUS_VERIFIED_RUN'
      Write-Host "RUN_BUILD_LOG=$buildLog"
      Write-Host "RUN_AUDIT_LOG=$auditLog"
      exit 0
    }
  }

  # Installed exact binary, not elan dispatch: no toolchain auto-install.
  # Lake only computes LEAN_PATH from the *existing* workspace; it never runs
  # update/build/cache-get. Theorem file is compiled directly with Lean -jN.
  $oldThreads = $env:LEAN_NUM_THREADS
  $env:LEAN_NUM_THREADS = "$threadCount"
  $outputLines = @()
  $code = 1
  Push-Location -LiteralPath $workspace
  try {
    $ErrorActionPreference = 'Continue' # native stderr is diagnostics
    $outputLines = @(& $lake env $lean ('-j' + $threadCount) $src 2>&1 |
                      ForEach-Object { $_.ToString() })
    $code = $LASTEXITCODE
    $ErrorActionPreference = 'Stop'
  } finally {
    Pop-Location
    $env:LEAN_NUM_THREADS = $oldThreads
    $ErrorActionPreference = 'Stop'
  }
  SaveText $buildLog ([string[]]$outputLines)
  if ($code -ne 0) {
    SaveText $auditLog @(
      'PACKAGE=NSE_DECOMP_A_TIER_CANDIDATE_v0_1_9_FIX2_FASTCACHE',
      "LEAN_VERSION=$expected", "PROJECT_ROOT=$workspace",
      'BUILD=FAIL', "BUILD_EXIT_CODE=$code",
      'AXIOM_AUDIT=NOT_RUN', 'ROOT_STATUS=CONDITIONAL',
      'A_TIER=NOT_ESTABLISHED'
    )
    Remove-Item -LiteralPath $sealPath -ErrorAction SilentlyContinue
    # Surface actual compiler errors rather than burying them below #print axioms.
    $errorIndices = New-Object 'System.Collections.Generic.List[int]'
    for ($i = 0; $i -lt $outputLines.Count; $i++) {
      if ($outputLines[$i] -match '(:[0-9]+:[0-9]+:\s*error(?:\(|:|\b)|^error:|^unsolved goals|^No goals to be solved)') {
        $errorIndices.Add($i)
      }
    }
    $errorSummary = New-Object 'System.Collections.Generic.List[string]'
    $errorSummary.Add("LEAN_BUILD_EXIT=$code")
    $errorSummary.Add("COMPILER_ERROR_COUNT=$($errorIndices.Count)")
    $errorSummary.Add('COMPILER_ERRORS_BEGIN')
    if ($errorIndices.Count -gt 0) {
      $shown = New-Object 'System.Collections.Generic.HashSet[int]'
      foreach ($index in $errorIndices) {
        $end = [Math]::Min($outputLines.Count - 1, $index + 6)
        for ($n = $index; $n -le $end; $n++) {
          if ($shown.Add($n)) { $errorSummary.Add($outputLines[$n]) }
        }
      }
    } else {
      $errorSummary.Add('No standard Lean error line detected; showing first 35 output lines:')
      @($outputLines | Select-Object -First 35) | ForEach-Object { $errorSummary.Add($_) }
    }
    $errorSummary.Add('COMPILER_ERRORS_END')
    $errorLog = Join-Path $pkg 'run-error-summary.log'
    SaveText $errorLog ([string[]]$errorSummary.ToArray())
    $errorSummary | ForEach-Object { Write-Host $_ }
    Write-Host "RUN_ERROR_SUMMARY_LOG=$errorLog"
    throw "BUILD_FAILED_EXIT_$code; see $buildLog"
  }

  $rootNames = @(
    'NSEDecomp.fieldCoeff_lipschitz_of_L2Bound',
    'NSEDecomp.fieldCoeff_trace_of_L2Bound',
    'NSEDecomp.finiteHhalfWindowTrace_of_L2Bound',
    'NSEDecomp.FourierTraceEndpoint_of_L2Bound',
    'NSEDecomp.boundaryTraceEndpoint_of_L2Bound',
    'NSEDecomp.NSE_DECOMP_STRICT_HHALF_of_L2Bound',
    'NSEDecomp.NSE_DECOMP_all_LH_strict_HHALF_of_L2Bound',
    'NSEDecomp.finiteHhalfWindow_unbounded_of_notMemHhalf',
    'NSEDecomp.hhalfTerm_tendsto_of_coeffTrace',
    'NSEDecomp.finiteHhalfWindowTrace_of_coeffTrace',
    'NSEDecomp.roughTraceBlowup_of_finiteWindowTrace',
    'NSEDecomp.boundaryTraceEndpoint_of_FourierTrace',
    'NSEDecomp.NSE_DECOMP_STRICT_HHALF_of_FourierTrace',
    'NSEDecomp.NSE_DECOMP_all_LH_strict_HHALF_of_FourierTrace',
    'NSEDecomp.projectedODE_unprojected_corrector',
    'NSEDecomp.projectedODE_zero_mode_hasDerivAt',
    'NSEDecomp.finiteHhalfMass_le_total',
    'NSEDecomp.hhalfNorm_sq_eq_total',
    'NSEDecomp.finiteHhalfMass_le_norm_sq',
    'NSEDecomp.hhalfMode_le_norm_sq',
    'NSEDecomp.pressureCorrector_zero_of_modeSq_zero',
    'NSEDecomp.pressureCorrector_zero_mode',
    'NSEDecomp.projectedTransportCoeff_eq_raw_sub_corrector',
    'NSEDecomp.rawTransportCoeff_eq_projected_plus_corrector',
    'NSEDecomp.pressureCorrector_gradient_divergence',
    'NSEDecomp.pressureCorrector_divergence_identity',
    'NSEDecomp.viscousMode_solenoidal',
    'NSEDecomp.projectedNSForce_solenoidal',
    'NSEDecomp.projectedNSForce_zero_mode',
    'NSEDecomp.modeSq_nonneg',
    'NSEDecomp.freqSq_nonneg',
    'NSEDecomp.modeSq_eq_zero_iff',
    'NSEDecomp.projectedTransportCoeff_zero_of_modeSq_zero',
    'NSEDecomp.modeSq_complex_sum',
    'NSEDecomp.projectedTransport_solenoidal',
    'NSEDecomp.hhalfTerm_nonneg',
    'NSEDecomp.hmTerm_nonneg',
    'NSEDecomp.hhalfTerm_le_hmTerm_one',
    'NSEDecomp.memHhalf_of_hmOne_summable',
    'NSEDecomp.positiveHInf_memHhalf',
    'NSEDecomp.positiveTimeCInfFourier_memHhalf',
    'NSEDecomp.rawTransportCoeff_zero_mode',
    'NSEDecomp.freqSq_zero_mode',
    'NSEDecomp.projectedTransportCoeff_zero_mode',
    'NSEDecomp.passiveTransportCoeff_zero_mode',
    'NSEDecomp.weakNSIntegrand_zero_mode',
    'NSEDecomp.passiveWeakIntegrand_zero_mode',
    'NSEDecomp.nse_zero_mode_weak_identity',
    'NSEDecomp.passive_zero_mode_weak_identity',
    'NSEDecomp.globalLerayHopf_trace_unique',
    'NSEDecomp.energyBound_of_energyEquality',
    'NSEDecomp.energyEquality_congr',
    'NSEDecomp.twoD3CInvariant_congr',
    'NSEDecomp.positiveHInf_congr',
    'NSEDecomp.timeDeriv_eqOn_positive',
    'NSEDecomp.positiveTimeCInfFourier_congr',
    'NSEDecomp.isReconstruction_unique',
    'NSEDecomp.NSE_DECOMP_every_LH_agrees_with_reconstruction',
    'NSEDecomp.NSE_DECOMP_all_LH_unique_pair',
    'NSEDecomp.NSE_DECOMP_all_LH_energyEquality',
    'NSEDecomp.NSE_DECOMP_all_LH_pressureFourier',
    'NSEDecomp.NSE_DECOMP_all_LH_strict_HHALF',
    'NSEDecomp.NSE_DECOMP',
    'NSEDecomp.NSE_DECOMP_every_LH_regular',
    'NSEDecomp.NSE_DECOMP_STRICT_HHALF'
  )
  $auditLines = New-Object 'System.Collections.Generic.List[string]'
  foreach ($name in $rootNames) {
    $pattern = "^['`"]?" + [regex]::Escape($name) + "['`"]?\s+(depends on axioms:|does not depend on any axioms)"
    $matchLine = @($outputLines | Where-Object { $_ -match $pattern })
    if ($matchLine.Count -eq 0) {
      throw "AUDIT_MISSING_DECLARATION=$name ; see $buildLog"
    }
    foreach ($record in $matchLine) {
      $auditLines.Add($record)
      if ($record -match 'depends on axioms:\s*\[([^\]]*)\]') {
        foreach ($axiom in @($Matches[1].Split(',') | ForEach-Object { $_.Trim() })) {
          if ($axiom -notin @('propext', 'Classical.choice', 'Quot.sound')) {
            throw "AUDIT_UNAPPROVED_AXIOM=$axiom (theorem $name)"
          }
        }
      } elseif ($record -notmatch 'does not depend on any axioms') {
        throw "AUDIT_UNPARSEABLE=$name : $record"
      }
    }
  }
  if (($outputLines -join "`n") -match '(?i)sorryAx|warning:.*declaration uses .sorry.') {
    throw 'AUDIT_SORRY_FOUND: see run-build.log'
  }
  SaveText $auditLog ([string[]](@(
    'PACKAGE=NSE_DECOMP_A_TIER_CANDIDATE_v0_1_9_FIX2_FASTCACHE',
    "LEAN_VERSION=$expected", "PROJECT_ROOT=$workspace",
    "THREADS=$threadCount", 'BUILD=PASS', 'AXIOM_AUDIT=STANDARD_ONLY',
    'ANALYTIC_ENDPOINTS=NOT_DISCHARGED',
    'STRUCTURAL_DISCHARGE=regularityCongr,energyEqualityCongr,zeroModeTransport,weakZeroMode,traceUniqueness,projectedTransportSolenoidal,H1toHhalf,pressureSymbolCoherence,projectedODEPressureInterface,finiteHhalfWindowBound,boundaryTraceReduction,L2CoeffBoundReduction',
    'EXACT_PDE_SEMANTICS=OPEN',
    'ROOT_STATUS=CONDITIONAL', 'A_TIER=NOT_ESTABLISHED',
    "CACHE_SEAL_SHA256=$seal", 'THEOREM_AXIOM_REPORT_BEGIN'
  ) + @($auditLines.ToArray()) + @('THEOREM_AXIOM_REPORT_END')))
  SaveText $sealPath @($seal)
  Write-Host 'CACHE_HIT=NO'
  Write-Host 'BUILD=PASS'
  Write-Host 'AXIOM_AUDIT=STANDARD_ONLY'
  Write-Host 'STRUCTURAL_DISCHARGE=regularityCongr,energyEqualityCongr,zeroModeTransport,weakZeroMode,traceUniqueness,projectedTransportSolenoidal,H1toHhalf,pressureSymbolCoherence,projectedODEPressureInterface,finiteHhalfWindowBound,boundaryTraceReduction,L2CoeffBoundReduction'
  Write-Host 'EXACT_PDE_SEMANTICS=OPEN'
  Write-Host 'ROOT_STATUS=CONDITIONAL'
  Write-Host 'A_TIER=NOT_ESTABLISHED'
  Write-Host "RUN_BUILD_LOG=$buildLog"
  Write-Host "RUN_AUDIT_LOG=$auditLog"
  exit 0
} catch {
  Remove-Item -LiteralPath $sealPath -ErrorAction SilentlyContinue
  Write-Host "RUN=FAIL: $($_.Exception.Message)"
  Write-Host "BUILD_LOG=$buildLog"
  Write-Host "AUDIT_LOG=$auditLog"
  exit 1
}
