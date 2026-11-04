param(
  [string]$MathlibCacheRoot = $env:MATHLIB_CACHE_ROOT,
  [string]$LeanExe = $env:LEAN_EXE,
  [switch]$TraceDependencies
)
$ErrorActionPreference = 'Stop'
$pkg = $PSScriptRoot
$tag = (Get-Date -Format 'yyyyMMdd-HHmmss-fff') + '-' + [Guid]::NewGuid().ToString('N').Substring(0,8)
$ev = Join-Path $pkg ('evidence\' + $tag)
$ol = Join-Path $ev 'olean'
New-Item -ItemType Directory -Force -Path $ol | Out-Null
Write-Host "EVIDENCE=$ev"
function Fail([string]$why) {
  "RESULT=FAIL`r`nREASON=$why" | Set-Content -LiteralPath (Join-Path $ev 'result.txt') -Encoding UTF8
  Write-Host 'RESULT=FAIL'
  Write-Host "REASON=$why"
  exit 1
}
try {
  # Never call an elan PATH shim, which may install a missing toolchain.
  # Prefer a user-specified executable, then real binaries in installed
  # elan toolchain directories. No administrator launch is attempted.
  $leanCandidates = [System.Collections.Generic.List[string]]::new()
  if (-not [string]::IsNullOrWhiteSpace($LeanExe)) {
    $leanCandidates.Add($LeanExe)
  }
  $toolchainRoots = [System.Collections.Generic.List[string]]::new()
  if (-not [string]::IsNullOrWhiteSpace($env:ELAN_HOME)) {
    $toolchainRoots.Add((Join-Path $env:ELAN_HOME 'toolchains'))
  }
  if (-not [string]::IsNullOrWhiteSpace($env:USERPROFILE)) {
    $defaultToolchains = Join-Path $env:USERPROFILE '.elan\toolchains'
    if (-not $toolchainRoots.Contains($defaultToolchains)) { $toolchainRoots.Add($defaultToolchains) }
  }
  foreach ($toolchains in $toolchainRoots) {
    if (Test-Path -LiteralPath $toolchains -PathType Container) {
      foreach ($dir in @(Get-ChildItem -LiteralPath $toolchains -Directory | Sort-Object Name)) {
        $candidate = Join-Path $dir.FullName 'bin\lean.exe'
        if (Test-Path -LiteralPath $candidate -PathType Leaf) {
          if (-not $leanCandidates.Contains($candidate)) { $leanCandidates.Add($candidate) }
        }
      }
    }
  }
  $leanSelectionLog = Join-Path $ev 'lean-selection.txt'
  @('LEAN_SELECTION=INSTALLED_TOOLCHAINS_ONLY', "TOOLCHAIN_ROOTS=$($toolchainRoots -join ';')") |
    Set-Content -LiteralPath $leanSelectionLog -Encoding UTF8
  $selectedLean = $null
  foreach ($candidate in $leanCandidates) {
    if (-not (Test-Path -LiteralPath $candidate -PathType Leaf)) {
      Add-Content -LiteralPath $leanSelectionLog -Value "MISSING=$candidate"
      continue
    }
    $candidatePath = (Resolve-Path -LiteralPath $candidate).Path
    $isElanShim = $candidatePath -match '(?i)[\\/]\.elan[\\/]bin[\\/]lean\.exe$'
    if (-not [string]::IsNullOrWhiteSpace($env:ELAN_HOME)) {
      $customShim = Join-Path $env:ELAN_HOME 'bin\lean.exe'
      if (Test-Path -LiteralPath $customShim -PathType Leaf) {
        $customShimPath = (Resolve-Path -LiteralPath $customShim).Path
        if ($candidatePath -ieq $customShimPath) { $isElanShim = $true }
      }
    }
    if ($isElanShim) {
      Add-Content -LiteralPath $leanSelectionLog -Value "SKIPPED_ELAN_SHIM=$candidatePath"
      continue
    }
    try {
      $candidateVersion = (& $candidatePath --version 2>&1 | Out-String).Trim()
      $candidateExit = $LASTEXITCODE
      if ($candidateExit -eq 0 -and $candidateVersion -match '^Lean \(version 4\.34\.0-rc1,') {
        $selectedLean = $candidatePath
        $ver = $candidateVersion
        Add-Content -LiteralPath $leanSelectionLog -Value "SELECTED=$candidatePath"
        break
      }
      Add-Content -LiteralPath $leanSelectionLog -Value "VERSION_MISMATCH_OR_FAILURE=$candidatePath EXIT=$candidateExit VERSION=$candidateVersion"
    } catch {
      Add-Content -LiteralPath $leanSelectionLog -Value "CANNOT_RUN=$candidatePath ERROR=$($_.Exception.Message)"
    }
  }
  if (-not $selectedLean) {
    Write-Host 'No existing non-elevated Lean 4.34.0-rc1 compiler was found in the checked locations.'
    Write-Host 'Set LEAN_EXE to the full path of an existing native Lean 4.34.0-rc1 compiler and run again.'
    Write-Host "See $leanSelectionLog for candidates and errors."
    Fail 'Lean_4_34_0_rc1_not_runnable_set_LEAN_EXE'
  }
  $LeanExe = $selectedLean
  $ver | Set-Content -LiteralPath (Join-Path $ev 'lean-version.txt') -Encoding UTF8
  Write-Host "LEAN_EXE=$LeanExe"
  Write-Host $ver
  if ([string]::IsNullOrWhiteSpace($MathlibCacheRoot)) { Fail 'Set_MATHLIB_CACHE_ROOT_to_cached_Mathlib_project_or_lib_lean' }
  if (-not (Test-Path -LiteralPath $MathlibCacheRoot -PathType Container)) { Fail 'MATHLIB_CACHE_ROOT_not_found' }
  $root = (Resolve-Path -LiteralPath $MathlibCacheRoot).Path
  $candidates = @($root, (Join-Path $root '.lake\build\lib\lean'), (Join-Path $root '.lake\packages\mathlib\.lake\build\lib\lean'))
  $mathlib = $null
  foreach ($c in $candidates) {
    if (Test-Path -LiteralPath (Join-Path $c 'Mathlib\Analysis\SpecialFunctions\Trigonometric\Basic.olean') -PathType Leaf) { $mathlib = (Resolve-Path $c).Path; break }
  }
  if (-not $mathlib) { Fail 'Cached_Mathlib_olean_not_found' }
  # Discover dependency caches under both the supplied project and the mathlib project.
  $pathList = [System.Collections.Generic.List[string]]::new()
  $pathList.Add($ol); $pathList.Add($mathlib)
  $parents = [System.Collections.Generic.List[string]]::new()
  foreach ($initial in @($root,$mathlib)) {
    $d = Get-Item -LiteralPath $initial
    while ($null -ne $d) {
      if (-not $parents.Contains($d.FullName)) { $parents.Add($d.FullName) }
      $d = $d.Parent
    }
  }
  foreach ($p in $parents) {
    $packages = Join-Path $p '.lake\packages'
    if (Test-Path -LiteralPath $packages -PathType Container) {
      foreach ($dep in Get-ChildItem -LiteralPath $packages -Directory) {
        $lib = Join-Path $dep.FullName '.lake\build\lib\lean'
        if ((Test-Path -LiteralPath $lib -PathType Container) -and -not $pathList.Contains($lib)) { $pathList.Add($lib) }
      }
    }
  }
  $env:LEAN_PATH = $pathList -join ';'
  $pathList | Set-Content -LiteralPath (Join-Path $ev 'lean-path.txt') -Encoding UTF8
  @(
    "COMPILER_SHA256=$((Get-FileHash -LiteralPath $LeanExe -Algorithm SHA256).Hash.ToLowerInvariant())"
    "SOURCE_SHA256=$((Get-FileHash -LiteralPath (Join-Path $pkg 'HVR_Prime_Gram.lean') -Algorithm SHA256).Hash.ToLowerInvariant())"
    "MATHLIB_ROOT=$mathlib"
    "MATHLIB_WITNESS_SHA256=$((Get-FileHash -LiteralPath (Join-Path $mathlib 'Mathlib\Analysis\SpecialFunctions\Trigonometric\Basic.olean') -Algorithm SHA256).Hash.ToLowerInvariant())"
    'MATHLIB_CACHE_PROVENANCE=USER_SUPPLIED_NOT_INDEPENDENTLY_VERIFIED'
  ) | Set-Content -LiteralPath (Join-Path $ev 'provenance.txt') -Encoding UTF8
  function Invoke-Lean([string[]]$arguments, [string]$name) {
    $stdout = Join-Path $ev ($name + '.stdout.log')
    $stderr = Join-Path $ev ($name + '.stderr.log')
    Push-Location $pkg
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
  $plan = @(
    @{ module = 'HVR_Prime_Gram'; deps = @(); names = @('HVRPrimeGram.kernel_identity', 'HVRPrimeGram.primeWeight_nonneg', 'HVRPrimeGram.finite_prime_gram_identity', 'HVRPrimeGram.finite_prime_gram_nonnegative', 'HVRPrimeGram.normalized_limit_excludes_zero_order', 'HVRPrimeGram.finite_prime_limit_excludes_zero_order') },
    @{ module = 'HVR_Positive_SmoothingSqueeze'; deps = @(); names = @('HVRPositiveSmoothingSqueeze.eventually_lt_four_of_upper_smoothing', 'HVRPositiveSmoothingSqueeze.tendsto_one_of_one_sided_smoothing') },
    @{ module = 'HVR_Smoothing_MonotoneNormalization'; deps = @(); names = @('HVRMonotoneNormalization.cutoffMass_monotone', 'HVRMonotoneNormalization.normalizedMass_le', 'HVRMonotoneNormalization.normalized_cutoffMass_le', 'HVRMonotoneNormalization.weighted_normalized_cutoffMass_le') },
    @{ module = 'HVR_PrimeMellin_Abel'; deps = @(); names = @('HVRPrimeMellinAbel.lseries_eq_mellin_of_zero') },
    @{ module = 'HVR_Complex_PoleLaplace'; deps = @(); names = @('HVRComplexPoleLaplace.exponential_integrable', 'HVRComplexPoleLaplace.exponential_integral_eq_inv') },
    @{ module = 'HVR_Smoothing_FrequencySeed'; deps = @(); names = @('HVRSmoothingFrequencySeed.seed_nonneg', 'HVRSmoothingFrequencySeed.seed_even', 'HVRSmoothingFrequencySeed.seed_smooth_Cinfty', 'HVRSmoothingFrequencySeed.seed_compact', 'HVRSmoothingFrequencySeed.seed_integrable', 'HVRSmoothingFrequencySeed.seed_integral', 'HVRSmoothingFrequencySeed.seed_support', 'HVRSmoothingFrequencySeed.seed_zero_of_band') },
    @{ module = 'HVR_HalfLine_IndicatorConvolution'; deps = @(); names = @('HVRHalfLineIndicatorConvolution.halfLineConvolution_eq_integral_Iic', 'HVRHalfLineIndicatorConvolution.integral_Iic_tendsto_integral', 'HVRHalfLineIndicatorConvolution.halfLineConvolution_tendsto_one') },
    @{ module = 'HVRSimpleMoebiusBound'; deps = @(); names = @('HVRSimpleMoebiusBound.abs_moebius_le_one') },
    @{ module = 'NativeZetaNonzero'; deps = @(); names = @('HVRNativeZetaNonzero.zeta_ne_zero_of_moebius_inverse', 'HVRNativeZetaNonzero.zeta_ne_zero_of_one_lt_re_of_moebius_inverse') },
    @{ module = 'NativeOneZetaSummability'; deps = @(); names = @('HVRNativeOneZetaSummability.one_summable', 'HVRNativeOneZetaSummability.arithmetic_zeta_summable', 'HVRNativeOneZetaSummability.one_abscissa_lt') },
    @{ module = 'NativeChebyshevBound'; deps = @(); names = @('HVRNativeChebyshevBound.primorial_lt_four_pow_native', 'HVRNativeChebyshevBound.primorial_le_four_pow_native', 'HVRNativeChebyshevBound.theta_le_log4_mul_x_native') },
    @{ module = 'HVRNativePrimePowerDivisorSum'; deps = @(); names = @('HVRNativePrimePowerDivisorSum.sum_divisors_prime_pow') },
    @{ module = 'HVRNativeCoprimePrimePowerDivisors'; deps = @(); names = @('HVRNativeCoprimePrimePowerDivisors.filtered_divisors_mul') },
    @{ module = 'HVRNativeArithmeticZeta'; deps = @(); names = @('HVRNativeArithmeticZeta.mangoldt_mul_zeta_apply') },
    @{ module = 'HVRSimpleMangoldtOne'; deps = @(); names = @('HVRSimpleMangoldtOne.vonMangoldt_one') },
    @{ module = 'HVRSimplePrimePowDisjoint'; deps = @(); names = @('HVRSimplePrimePowDisjoint.disjoint_divisors') },
    @{ module = 'NativeMangoldtPrime'; deps = @(); names = @('HVRNativeMangoldtPrime.vonMangoldt_apply_prime_native') },
    @{ module = 'NativeMangoldtPow'; deps = @(); names = @('HVRNativeMangoldtPow.vonMangoldt_apply_pow_native') },
    @{ module = 'HVRNativeLogRpow'; deps = @(); names = @('HVRNativeLogRpow.log_le_rpow_div_nonneg', 'HVRNativeLogRpow.log_natCast_le_rpow_div') },
    @{ module = 'HVRNativeLSeriesNorm'; deps = @(); names = @('HVRNativeLSeriesNorm.norm_term') },
    @{ module = 'NativeMangoldtNonneg'; deps = @(); names = @('HVRNativeMangoldtNonneg.vonMangoldt_nonneg_native') },
    @{ module = 'NativeMangoldtBound'; deps = @(); names = @('HVRNativeMangoldtBound.vonMangoldt_le_log_native') },
    @{ module = 'NativeSeriesInfrastructure'; deps = @(); names = @('HVRNativeSeriesInfrastructure.hasSum_scale', 'HVRNativeSeriesInfrastructure.hasSum_identifies_tsum', 'HVRNativeSeriesInfrastructure.complex_summable_of_majorant') },
    @{ module = 'HVR_Prime_Summability'; deps = @('HVR_Prime_Gram'); names = @('HVRPrimeSummability.primeWeightSeries_nonneg', 'HVRPrimeSummability.primeWeightSeries_summable') },
    @{ module = 'HVR_PhysicalKernel_Candidate'; deps = @('HVR_Smoothing_FrequencySeed'); names = @('HVRPhysicalKernelCandidate.complexSeed_compact', 'HVRPhysicalKernelCandidate.complexSeed_smooth', 'HVRPhysicalKernelCandidate.seedSchwartz_apply', 'HVRPhysicalKernelCandidate.seedSchwartz_zero_of_band', 'HVRPhysicalKernelCandidate.rawKernel_nonneg', 'HVRPhysicalKernelCandidate.rawKernel_continuous', 'HVRPhysicalKernelCandidate.rawKernel_integrable', 'HVRPhysicalKernelCandidate.normalizedKernel_nonneg', 'HVRPhysicalKernelCandidate.normalizedKernel_integral') },
    @{ module = 'IntegratedZetaNonzero'; deps = @('HVRSimpleMoebiusBound', 'NativeZetaNonzero', 'NativeOneZetaSummability'); names = @('HVRIntegratedZetaNonzero.moebiusLSeries_summable', 'HVRIntegratedZetaNonzero.zetaLSeries_mul_moebiusLSeries', 'HVRIntegratedZetaNonzero.rightHalfPlaneMoebiusInverse', 'HVRIntegratedZetaNonzero.zeta_ne_zero_of_one_lt_re') },
    @{ module = 'NextMangoldtDivisorSum'; deps = @('HVRNativePrimePowerDivisorSum', 'HVRNativeCoprimePrimePowerDivisors', 'HVRNativeArithmeticZeta', 'HVRSimpleMangoldtOne', 'HVRSimplePrimePowDisjoint', 'NativeMangoldtPrime', 'NativeMangoldtPow'); names = @('HVRNextMangoldtDivisorSum.vonMangoldt_sum_native', 'HVRNextMangoldtDivisorSum.vonMangoldt_mul_zeta_native') },
    @{ module = 'NextSummability'; deps = @('HVRNativeLogRpow', 'HVRNativeLSeriesNorm', 'NativeMangoldtNonneg', 'NativeMangoldtBound', 'NativeSeriesInfrastructure'); names = @('HVRNextSummability.vonMangoldt_lseries_summable') },
    @{ module = 'HVR_Prime_InfiniteGram'; deps = @('HVR_Prime_Summability'); names = @('HVRPrimeInfinite.cosMoment_summable', 'HVRPrimeInfinite.gramTerm_nonneg', 'HVRPrimeInfinite.infinite_prime_gram_nonnegative') },
    @{ module = 'HVR_Prime_PowerCorrection'; deps = @('HVR_Prime_Summability'); names = @('HVRPrimePowerCorrection.denominator_uniform_pos', 'HVRPrimePowerCorrection.ratio_le_two', 'HVRPrimePowerCorrection.correctionTerm_nonneg', 'HVRPrimePowerCorrection.correctionTerm_le', 'HVRPrimePowerCorrection.correction_summable', 'HVRPrimePowerCorrection.correction_abs_summable', 'HVRPrimePowerCorrection.correction_geometric_hasSum') },
    @{ module = 'HVR_PhysicalKernel_PositiveMass'; deps = @('HVR_PhysicalKernel_Candidate'); names = @('HVRPhysicalKernelCandidate.wave_at_zero', 'HVRPhysicalKernelCandidate.rawKernel_at_zero', 'HVRPhysicalKernelCandidate.mass_pos', 'HVRPhysicalKernelCandidate.normalizedKernel_nonneg_unconditional', 'HVRPhysicalKernelCandidate.normalizedKernel_integral_unconditional') },
    @{ module = 'HVR_SpectralSeedCorrelation'; deps = @('HVR_PhysicalKernel_Candidate'); names = @('HVRSpectralSeedCorrelation.correlation_nonneg', 'HVRSpectralSeedCorrelation.correlation_zero_of_band') },
    @{ module = 'HVR_PhysicalKernel_WaveReal'; deps = @('HVR_PhysicalKernel_Candidate'); names = @('HVRPhysicalKernelWaveReal.wave_im_zero') },
    @{ module = 'HVRMajorZetaLogDerivative'; deps = @('NextMangoldtDivisorSum', 'NextSummability', 'IntegratedZetaNonzero'); names = @('HVRMajorZetaLogDerivative.convolution_vonMangoldt_zeta_native', 'HVRMajorZetaLogDerivative.convolution_vonMangoldt_const_one_native', 'HVRMajorZetaLogDerivative.vonMangoldt_LSeries_eq_neg_logDeriv_one', 'HVRMajorZetaLogDerivative.vonMangoldt_LSeries_eq_neg_logDeriv_zeta') },
    @{ module = 'HVR_Prime_BoundaryBridge'; deps = @('HVR_Prime_InfiniteGram'); names = @('HVRPrimeBoundaryBridge.residue_limits_contradict_prime_gram') },
    @{ module = 'HVR_Zeta_LogDerivative'; deps = @('HVR_Prime_InfiniteGram', 'HVRMajorZetaLogDerivative'); names = @('HVRZetaLogDerivative.vonMangoldt_coefficient_split', 'HVRZetaLogDerivative.higherCoefficient_eq_zero_of_prime', 'HVRZetaLogDerivative.higherCoefficient_eq_zero_of_not_prime_pow', 'HVRZetaLogDerivative.higherCoefficient_support', 'HVRZetaLogDerivative.vonMangoldt_at_prime_pow', 'HVRZetaLogDerivative.vonMangoldt_series_eq_zeta_log_deriv') },
    @{ module = 'HVR_Prime_Complex'; deps = @('HVR_Prime_InfiniteGram'); names = @('HVRPrimeComplex.primeTerm_summable', 'HVRPrimeComplex.primeTerm_re', 'HVRPrimeComplex.primeSeries_re', 'HVRPrimeComplex.primeTerm_eq_dirichlet', 'HVRPrimeComplex.primeTerm_eq_dirichlet_indicator', 'HVRPrimeComplex.primeSeries_eq_dirichlet', 'HVRPrimeComplex.infinite_complex_gram_nonnegative') },
    @{ module = 'HVR_PowerCorrection_Holomorphic'; deps = @('HVR_Prime_PowerCorrection'); names = @('HVRPowerCorrectionHolomorphic.halfPlane_isOpen', 'HVRPowerCorrectionHolomorphic.complexCorrection_summable_of_bound', 'HVRPowerCorrectionHolomorphic.complexCorrection_differentiableOn_of_bounds') },
    @{ module = 'HVR_Generic_LogDerivativeResidue'; deps = @('HVR_Prime_InfiniteGram'); names = @('HVRGenericLogDerivativeResidue.factored_log_derivative_algebra', 'HVRGenericLogDerivativeResidue.factored_log_derivative_limit', 'HVRGenericLogDerivativeResidue.factored_quotient_limit') },
    @{ module = 'HVR_SpectralCorrelation_Compact'; deps = @('HVR_SpectralSeedCorrelation'); names = @('HVRSpectralCorrelationCompact.correlation_hasCompactSupport', 'HVRSpectralCorrelationCompact.complexCorrelation_hasCompactSupport') },
    @{ module = 'HVR_Prime_ZetaSplit'; deps = @('HVR_Prime_Complex', 'HVR_Zeta_LogDerivative'); names = @('HVRPrimeZetaSplit.higherCoefficientC_eq_sub', 'HVRPrimeZetaSplit.primeCoefficientC_zero', 'HVRPrimeZetaSplit.prime_lseries_term_eq', 'HVRPrimeZetaSplit.prime_lseries_eq_primeSeries', 'HVRPrimeZetaSplit.prime_lseries_summable', 'HVRPrimeZetaSplit.higher_lseries_summable', 'HVRPrimeZetaSplit.zeta_log_deriv_eq_primeSeries_add_higher') },
    @{ module = 'HVR_Correction_TermHolomorphic'; deps = @('HVR_PowerCorrection_Holomorphic'); names = @('HVRCorrectionTermHolomorphic.complexRatio_norm', 'HVRCorrectionTermHolomorphic.complex_denominator_ne_zero', 'HVRCorrectionTermHolomorphic.complexCorrectionTerm_differentiableOn', 'HVRCorrectionTermHolomorphic.complexCorrection_differentiableOn_of_uniform_bound') },
    @{ module = 'HVR_SpectralCorrelation_Regularity'; deps = @('HVR_SpectralCorrelation_Compact'); names = @('HVRSpectralCorrelationRegularity.correlation_eq_convolution', 'HVRSpectralCorrelationRegularity.correlation_continuous', 'HVRSpectralCorrelationRegularity.correlation_integrable') },
    @{ module = 'HVR_Correction_UniformBound'; deps = @('HVR_Correction_TermHolomorphic'); names = @('HVRCorrectionUniformBound.ratio_antitone_re', 'HVRCorrectionUniformBound.ratio_sq_eq_weight_exp', 'HVRCorrectionUniformBound.complexCorrectionTerm_uniform_bound', 'HVRCorrectionUniformBound.complexCorrection_differentiableOn', 'HVRCorrectionUniformBound.complexCorrection_summable') },
    @{ module = 'HVR_HigherCoefficient_Reindex'; deps = @('HVR_Prime_ZetaSplit'); names = @('HVRHigherCoefficientReindex.higher_lseries_support_prime_powers', 'HVRHigherCoefficientReindex.higher_lseries_term_at_prime', 'HVRHigherCoefficientReindex.higher_lseries_eq_prime_power_tsum') },
    @{ module = 'HVR_SpectralCorrelation_FourierSquare'; deps = @('HVR_SpectralCorrelation_Regularity', 'HVR_PhysicalKernel_Candidate'); names = @('HVRSpectralCorrelationFourierSquare.complexSeed_integrable', 'HVRSpectralCorrelationFourierSquare.complexCorrelation_eq_convolution', 'HVRSpectralCorrelationFourierSquare.wave_eq_fourierInv_complexSeed', 'HVRSpectralCorrelationFourierSquare.fourierInv_correlation_eq_wave_sq', 'HVRSpectralCorrelationFourierSquare.fourierInv_correlation_eq_rawKernel_of_im_zero') },
    @{ module = 'HVR_PhysicalKernel_ScaledSpectrum'; deps = @('HVR_SpectralCorrelation_Regularity', 'HVR_PhysicalKernel_PositiveMass'); names = @('HVRPhysicalKernelScaledSpectrum.scaledSpectrum_continuous', 'HVRPhysicalKernelScaledSpectrum.scaledSpectrum_zero_of_band', 'HVRPhysicalKernelScaledSpectrum.scaledSpectrum_compact', 'HVRPhysicalKernelScaledSpectrum.scaledSpectrum_integrable') },
    @{ module = 'HVR_Correction_PrimeSubtype'; deps = @('HVR_Correction_UniformBound'); names = @('HVRCorrectionPrimeSubtype.complexCorrectionTerm_support', 'HVRCorrectionPrimeSubtype.complexCorrection_eq_prime_tsum', 'HVRCorrectionPrimeSubtype.complexCorrectionTerm_at_prime') },
    @{ module = 'HVR_HigherCoefficient_Geometric'; deps = @('HVR_HigherCoefficient_Reindex', 'HVR_Correction_UniformBound'); names = @('HVRHigherCoefficientGeometric.higherCoefficient_prime_power', 'HVRHigherCoefficientGeometric.complexRatio_eq_cpow_neg', 'HVRHigherCoefficientGeometric.cpow_prime_power_eq_ratio', 'HVRHigherCoefficientGeometric.higher_lseries_term_prime_power', 'HVRHigherCoefficientGeometric.correction_prime_power_hasSum', 'HVRHigherCoefficientGeometric.correction_prime_power_tsum') },
    @{ module = 'HVR_Correction_BoundaryLimit'; deps = @('HVR_Correction_UniformBound', 'HVR_Prime_ZetaSplit'); names = @('HVRCorrectionBoundaryLimit.boundaryEps_pos', 'HVRCorrectionBoundaryLimit.boundarySigma_gt_one', 'HVRCorrectionBoundaryLimit.boundaryEps_tendsto', 'HVRCorrectionBoundaryLimit.boundaryEps_complex_tendsto', 'HVRCorrectionBoundaryLimit.boundaryApproach_eq', 'HVRCorrectionBoundaryLimit.boundaryApproach_tendsto', 'HVRCorrectionBoundaryLimit.complexCorrection_continuousAt', 'HVRCorrectionBoundaryLimit.complexCorrection_tendsto_boundary', 'HVRCorrectionBoundaryLimit.normalized_correction_tendsto_zero', 'HVRCorrectionBoundaryLimit.normalized_correction_re_tendsto_zero') },
    @{ module = 'HVR_PhysicalKernel_SpectralIdentity'; deps = @('HVR_SpectralCorrelation_FourierSquare', 'HVR_PhysicalKernel_WaveReal'); names = @('HVRPhysicalKernelSpectralIdentity.fourierInv_correlation_eq_rawKernel') },
    @{ module = 'HVR_Snditeration_PrimePowerTail'; deps = @('HVR_HigherCoefficient_Geometric'); names = @('HVRSnditerationPrimePowerTail.prime_ratio_norm_lt_one', 'HVRSnditerationPrimePowerTail.higher_prime_power_hasSum', 'HVRSnditerationPrimePowerTail.mangoldt_term_prime_power', 'HVRSnditerationPrimePowerTail.mangoldt_prime_power_hasSum', 'HVRSnditerationPrimePowerTail.mangoldt_prime_power_tsum') },
    @{ module = 'HVR_Zeta_CorrectionIdentity'; deps = @('HVR_Snditeration_PrimePowerTail', 'HVR_Correction_PrimeSubtype'); names = @('HVRZetaCorrectionIdentity.higher_lseries_eq_complexCorrection', 'HVRZetaCorrectionIdentity.zeta_log_deriv_eq_primeSeries_add_complexCorrection') },
    @{ module = 'HVR_Zeta_PoleResidue'; deps = @('HVR_Zeta_CorrectionIdentity'); names = @('HVRZetaPoleResidue.logDerivative_regular_part_tendsto', 'HVRZetaPoleResidue.normalized_zeta_logDerivative_tendsto_one') },
    @{ module = 'HVR_Prime_ResidueTransfer'; deps = @('HVR_Zeta_CorrectionIdentity', 'HVR_Prime_BoundaryBridge'); names = @('HVRPrimeResidueTransfer.cosMoment_frequency_one', 'HVRPrimeResidueTransfer.cosMoment_zero_eq_primeMass', 'HVRPrimeResidueTransfer.primeSeries_limit_of_log_derivative', 'HVRPrimeResidueTransfer.cosMoment_limit_of_log_derivative', 'HVRPrimeResidueTransfer.primeMass_limit_of_log_derivative') },
    @{ module = 'HVR_Zeta_BoundaryFactor'; deps = @('HVR_Zeta_CorrectionIdentity', 'IntegratedZetaNonzero'); names = @('HVRZetaBoundaryFactor.zeta_boundary_finite_order', 'HVRZetaBoundaryFactor.zeta_boundary_local_factor', 'HVRZetaBoundaryFactor.zeta_boundary_zero_order_pos') },
    @{ module = 'HVR_PrimeCount_MellinDefs'; deps = @('HVR_Zeta_CorrectionIdentity'); names = @('HVRPrimeCountMellin.primeTheta_eq_log_prime_sum') },
    @{ module = 'HVR_PrimeMellin_Modes'; deps = @('HVR_Zeta_CorrectionIdentity'); names = @('HVRPrimeMellinModes.weighted_exponential_mode', 'HVRPrimeMellinModes.primeMode_integral', 'HVRPrimeMellinModes.primeMode_integrable', 'HVRPrimeMellinModes.primeMode_integral_norm', 'HVRPrimeMellinModes.primeMode_integral_norm_summable', 'HVRPrimeMellinModes.primeMode_integral_eq_primeTerm', 'HVRPrimeMellinModes.theta_exp_laplace_of_modes', 'HVRPrimeMellinModes.theta_exp_laplace_of_prime_expansion') },
    @{ module = 'HVR_Prime_PoleMass'; deps = @('HVR_Zeta_PoleResidue', 'HVR_Correction_BoundaryLimit', 'HVR_Prime_ResidueTransfer'); names = @('HVRPrimePoleMass.boundaryApproach_zero_ne_one', 'HVRPrimePoleMass.boundaryApproach_zero_sub_one', 'HVRPrimePoleMass.boundaryApproach_zero_punctured', 'HVRPrimePoleMass.normalized_zeta_pole_along_boundary', 'HVRPrimePoleMass.normalized_primeMass_pole_limit') },
    @{ module = 'HVR_Analytic_Residue'; deps = @('HVR_Zeta_BoundaryFactor'); names = @('HVRAnalyticResidue.logDeriv_continuousAt_of_analytic', 'HVRAnalyticResidue.normalized_neg_logDeriv_tendsto') },
    @{ module = 'HVR_PrimeCount_MellinConversion'; deps = @('HVR_PrimeCount_MellinDefs'); names = @('HVRPrimeCountGrowth.primeTheta_eq_chebyshev', 'HVRPrimeCountLogSubstitution.exp_image_pos_halfline', 'HVRPrimeCountLogSubstitution.exp_mul_mellin_power', 'HVRPrimeCountLogSubstitution.primeThetaMellin_eq_exp_integral') },
    @{ module = 'HVR_Zeta_GramResidueConditional'; deps = @('HVR_Prime_PoleMass', 'HVR_Zeta_BoundaryFactor'); names = @('HVRZetaGramResidueConditional.boundaryPoint_ne_one', 'HVRZetaGramResidueConditional.nonvanishing_of_two_zeta_residues', 'HVRZetaGramResidueConditional.nonvanishing_of_all_zeta_residues') },
    @{ module = 'HVR_Zeta_BoundarySequence'; deps = @('HVR_Analytic_Residue', 'HVR_Zeta_BoundaryFactor', 'HVR_Correction_BoundaryLimit', 'HVR_Prime_ResidueTransfer'); names = @('HVRZetaBoundarySequence.boundaryPoint_re', 'HVRZetaBoundarySequence.boundaryPoint_ne_one', 'HVRZetaBoundarySequence.boundaryApproach_ne_center', 'HVRZetaBoundarySequence.boundaryApproach_sub_center', 'HVRZetaBoundarySequence.boundaryApproach_punctured', 'HVRZetaBoundarySequence.zeta_boundary_neg_logderiv_residue', 'HVRZetaBoundarySequence.zeta_boundary_neg_logderiv_sequence', 'HVRZetaBoundarySequence.cosMoment_boundary_order_limit') },
    @{ module = 'HVR_PrimeMellin_ModeAssembly'; deps = @('HVR_PrimeMellin_Modes', 'HVR_PrimeCount_MellinConversion'); names = @('HVRPrimeMellinModeAssembly.mem_primeCutoff_iff', 'HVRPrimeMellinModeAssembly.theta_exp_modes_pointwise', 'HVRPrimeMellinModeAssembly.theta_exp_modes_ae', 'HVRPrimeMellinModeAssembly.theta_exp_laplace_unconditional', 'HVRPrimeMellinModeAssembly.primeSeries_eq_mul_mellin_via_modes') },
    @{ module = 'HVR_Zeta_ZeroFreeBoundary'; deps = @('HVR_Zeta_GramResidueConditional', 'HVR_Zeta_BoundarySequence'); names = @('HVRZetaZeroFreeBoundary.zeta_nonzero_on_one_line') },
    @{ module = 'HVR_PrimeCount_MellinCandidate'; deps = @('HVR_Zeta_CorrectionIdentity', 'HVR_PrimeMellin_ModeAssembly'); names = @('HVRPrimeCountMellin.primeSeries_eq_mul_primeThetaMellin', 'HVRPrimeCountMellin.zeta_log_deriv_eq_primeThetaMellin_add_correction') },
    @{ module = 'HVR_Smoothing_AnalyticGerms'; deps = @('HVR_Zeta_ZeroFreeBoundary'); names = @('HVRSmoothingAnalyticGerms.complexCorrection_differentiableAt_halfPlane', 'HVRSmoothingAnalyticGerms.poleRegularPart_differentiableAt_zero', 'HVRSmoothingAnalyticGerms.regularPartAt_differentiableAt', 'HVRSmoothingAnalyticGerms.regularPartAt_differentiableAt_boundary') },
    @{ module = 'HVR_PrimeCount_GrowthCandidate'; deps = @('HVR_PrimeCount_MellinCandidate', 'HVR_PrimeCount_MellinConversion', 'NativeChebyshevBound'); names = @('HVRPrimeCountGrowth.primeCoefficient_partial_sum_isBigO', 'HVRPrimeCountGrowth.primeSeries_eq_mul_primeThetaMellin_unconditional', 'HVRPrimeCountGrowth.zeta_log_deriv_eq_primeThetaMellin_add_correction_unconditional') },
    @{ module = 'HVR_Smoothing_PoleGlue'; deps = @('HVR_Smoothing_AnalyticGerms'); names = @('HVRSmoothingAnalyticGerms.poleRegularPart_eventuallyEq_raw') },
    @{ module = 'HVR_PrimeCount_MellinGerm'; deps = @('HVR_PrimeCount_GrowthCandidate', 'HVR_Smoothing_AnalyticGerms'); names = @('HVRPrimeCountMellinGerm.primeThetaMellin_sub_pole_eq_regularPartAt', 'HVRPrimeCountMellinGerm.primeThetaMellin_sub_pole_eq_regularPartAt_of_growth') },
    @{ module = 'HVR_PrimeLogDensity'; deps = @('HVR_PrimeCount_GrowthCandidate', 'HVR_Smoothing_MonotoneNormalization', 'NativeChebyshevBound'); names = @('HVRPrimeLogDensity.logPrimeMass_eq_primeTheta', 'HVRPrimeLogDensity.logPrimeMass_monotone', 'HVRPrimeLogDensity.logPrimeDensity_nonneg', 'HVRPrimeLogDensity.logPrimeDensity_le_log_four', 'HVRPrimeLogDensity.logPrimeDensity_le', 'HVRPrimeLogDensity.weighted_logPrimeDensity_le', 'HVRPrimeLogDensity.logPrimeDensity_past_le', 'HVRPrimeLogDensity.logPrimeDensity_le_future') },
    @{ module = 'HVR_PrimeCount_ExpGrowth'; deps = @('HVR_PrimeLogDensity', 'NativeChebyshevBound'); names = @('HVRPrimeCountExpGrowth.logPrimeMass_isBigO_exp', 'HVRPrimeCountExpGrowth.logPrimeMass_integrableOn_exp_neg_mul') },
    @{ module = 'HVR_PrimeCount_LogSubstitution'; deps = @('HVR_PrimeCount_MellinGerm', 'HVR_PrimeCount_MellinConversion'); names = @('HVRPrimeCountLogSubstitution.exp_integral_sub_pole_eq_regularPartAt') },
    @{ module = 'HVR_PrimeDensity_WindowBounds'; deps = @('HVR_PrimeLogDensity'); names = @('HVRPrimeDensityWindowBounds.future_window_lower', 'HVRPrimeDensityWindowBounds.past_window_upper', 'HVRPrimeDensityWindowBounds.weighted_density_upper') },
    @{ module = 'HVR_PrimeDensity_WeightedIntegrability'; deps = @('HVR_PrimeLogDensity'); names = @('HVRPrimeDensityWeightedIntegrability.logPrimeDensity_measurable', 'HVRPrimeDensityWeightedIntegrability.weighted_density_integrableOn') },
    @{ module = 'HVR_PrimeDensity_Laplace'; deps = @('HVR_PrimeCount_LogSubstitution', 'HVR_PrimeCount_ExpGrowth', 'HVR_Complex_PoleLaplace'); names = @('HVRPrimeDensityLaplace.primeMass_complex_integrable', 'HVRPrimeDensityLaplace.density_integrand_eq', 'HVRPrimeDensityLaplace.primeDensity_integrable', 'HVRPrimeDensityLaplace.primeDensityLaplace_eq_regularPartAt') },
    @{ module = 'HVR_Smoothing_BoundaryExtension'; deps = @('HVR_Smoothing_PoleGlue', 'HVR_PrimeCount_LogSubstitution'); names = @('HVRSmoothingBoundaryExtension.patchedShift_eventuallyEq_pole', 'HVRSmoothingBoundaryExtension.patchedShift_continuousAt_zero', 'HVRSmoothingBoundaryExtension.patchedShift_continuousAt_imaginary', 'HVRSmoothingBoundaryExtension.patchedShift_continuous_boundary', 'HVRSmoothingBoundaryExtension.exp_integral_sub_pole_eq_patchedShift') },
    @{ module = 'HVR_PrimeDensity_WindowBridge'; deps = @('HVR_PrimeDensity_WindowBounds', 'HVR_PrimeDensity_WeightedIntegrability'); names = @('HVRPrimeDensityWindowBridge.future_window_lower_of_integrable', 'HVRPrimeDensityWindowBridge.past_window_upper_of_integrable', 'HVRPrimeDensityWindowBridge.weighted_density_upper_of_integrable') },
    @{ module = 'HVR_PrimeDensity_BoundaryLink'; deps = @('HVR_PrimeDensity_Laplace', 'HVR_Smoothing_BoundaryExtension'); names = @('HVRPrimeDensityBoundaryLink.primeDensityLaplace_eq_patchedShift') },
    @{ module = 'HVR_PrimeBoundary_FourierDecay'; deps = @('HVR_Smoothing_BoundaryExtension'); names = @('HVRPrimeBoundaryFourierDecay.weightedBoundary_continuous', 'HVRPrimeBoundaryFourierDecay.weightedBoundary_hasCompactSupport', 'HVRPrimeBoundaryFourierDecay.weightedBoundary_integrable', 'HVRPrimeBoundaryFourierDecay.weightedBoundary_fourier_tendsto_zero') },
    @{ module = 'HVR_PrimeDensity_FubiniBridge'; deps = @('HVR_PrimeDensity_Laplace'); names = @('HVRPrimeDensityFubiniBridge.mixed_factorization', 'HVRPrimeDensityFubiniBridge.abel_smoothing_eq_frequency_integral') },
    @{ module = 'HVR_PrimeDensity_ConcentratedSqueeze'; deps = @('HVR_PrimeDensity_WindowBridge', 'HVR_Positive_SmoothingSqueeze'); names = @('HVRPrimeDensityConcentratedSqueeze.integral_split_window', 'HVRPrimeDensityConcentratedSqueeze.two_bounds_of_concentrated_kernel', 'HVRPrimeDensityConcentratedSqueeze.primeDensity_tendsto_of_concentrated_smoothing') },
    @{ module = 'HVR_PrimeDensity_BoundaryLimit'; deps = @('HVR_PrimeDensity_BoundaryLink'); names = @('HVRPrimeDensityBoundaryLimit.primeDensityLaplace_tendsto_right_boundary', 'HVRPrimeDensityBoundaryLimit.primeDensityLaplace_boundaryEps_tendsto', 'HVRPrimeDensityBoundaryLimit.primeDensityLaplace_uniform_on_compact') },
    @{ module = 'HVR_PrimeDensity_FubiniIntegrable'; deps = @('HVR_PrimeDensity_FubiniBridge'); names = @('HVRPrimeDensityFubiniIntegrable.dampedError_integrable', 'HVRPrimeDensityFubiniIntegrable.mixed_integrable', 'HVRPrimeDensityFubiniIntegrable.abel_smoothing_eq_frequency_integral_of_integrable') },
    @{ module = 'HVR_PrimeDensity_PNTConditional'; deps = @('HVR_PrimeDensity_ConcentratedSqueeze'); names = @('HVRPrimeDensityPNTConditional.theta_ratio_tendsto_one_of_density', 'HVRPrimeDensityPNTConditional.theta_ratio_tendsto_one_of_concentrated_smoothing') },
    @{ module = 'HVR_PhysicalKernel_WindowAlgebra'; deps = @('HVR_PhysicalKernel_PositiveMass', 'HVR_PrimeDensity_ConcentratedSqueeze'); names = @('HVRPhysicalKernelWindowAlgebra.normalizedKernel_integrable', 'HVRPhysicalKernelWindowAlgebra.window_bounds_of_unit_mass_tail') },
    @{ module = 'HVR_PrimeBoundary_OrdinaryFrequencyDecay'; deps = @('HVR_PrimeBoundary_FourierDecay'); names = @('HVRPrimeBoundaryOrdinaryFrequencyDecay.ordinaryBoundary_eq_scaled_fourier', 'HVRPrimeBoundaryOrdinaryFrequencyDecay.ordinaryBoundary_tendsto_zero') },
    @{ module = 'HVR_PrimeDensity_SpatialAbel'; deps = @('HVR_PrimeDensity_FubiniIntegrable', 'HVR_PrimeDensity_WeightedIntegrability', 'HVR_Correction_BoundaryLimit'); names = @('HVRPrimeDensitySpatialAbel.spatial_abel_tendsto') },
    @{ module = 'HVR_PrimeBoundary_AbelLimitConditional'; deps = @('HVR_PrimeDensity_BoundaryLimit', 'HVR_PrimeBoundary_OrdinaryFrequencyDecay'); names = @('HVRPrimeBoundaryAbelLimitConditional.frequency_integral_tendsto_boundary_of_dominated') },
    @{ module = 'HVR_PhysicalKernel_CanonicalWindow'; deps = @('HVR_PhysicalKernel_WindowAlgebra'); names = @('HVRPhysicalKernelCanonicalWindow.canonicalWindow_pos', 'HVRPhysicalKernelCanonicalWindow.canonicalWindow_exp', 'HVRPhysicalKernelCanonicalWindow.canonicalWindow_bounds_of_tail') },
    @{ module = 'HVR_PhysicalKernel_ScaledTranslate'; deps = @('HVR_PhysicalKernel_WindowAlgebra'); names = @('HVRPhysicalKernelScaledTranslate.scaledTranslate_nonneg', 'HVRPhysicalKernelScaledTranslate.scaledTranslate_integrable', 'HVRPhysicalKernelScaledTranslate.scaledTranslate_integral') },
    @{ module = 'HVR_PhysicalKernel_Tail'; deps = @('HVR_PhysicalKernel_WindowAlgebra'); names = @('HVRPhysicalKernelTail.symmetricTail_antitone', 'HVRPhysicalKernelTail.symmetricTail_iInter', 'HVRPhysicalKernelTail.normalizedKernel_symmetricTail_tendsto', 'HVRPhysicalKernelTail.normalizedKernel_exists_small_tail', 'HVRPhysicalKernelTail.outside_window_scaled') },
    @{ module = 'HVR_PrimeDensity_AbelGlueConditional'; deps = @('HVR_PrimeDensity_SpatialAbel', 'HVR_PrimeBoundary_AbelLimitConditional'); names = @('HVRPrimeDensityAbelGlueConditional.undamped_eq_ordinaryBoundary_of_dominated', 'HVRPrimeDensityAbelGlueConditional.undamped_tendsto_zero_of_dominated') },
    @{ module = 'HVR_PrimeBoundary_EventualDomination'; deps = @('HVR_PrimeBoundary_AbelLimitConditional'); names = @('HVRPrimeBoundaryEventualDomination.laplace_eventually_bounded_on_compact', 'HVRPrimeBoundaryEventualDomination.frequency_eventually_dominated_on_compact') },
    @{ module = 'HVR_PrimeBoundary_FrequencyMeasurable'; deps = @('HVR_PrimeBoundary_AbelLimitConditional', 'HVR_PrimeDensity_FubiniIntegrable'); names = @('HVRPrimeBoundaryFrequencyMeasurable.frequencyIntegrand_aestronglyMeasurable') },
    @{ module = 'HVR_PhysicalKernel_TailScaling'; deps = @('HVR_PhysicalKernel_Tail', 'HVR_PhysicalKernel_ScaledTranslate', 'HVR_PhysicalKernel_CanonicalWindow'); names = @('HVRPhysicalKernelTailScaling.scaled_window_tail_le', 'HVRPhysicalKernelTailScaling.exists_scaled_window_small_tail', 'HVRPhysicalKernelTailScaling.exists_concentrated_scaled_kernel') },
    @{ module = 'HVR_PhysicalKernel_ScaledRepresentation'; deps = @('HVR_PhysicalKernel_SpectralIdentity', 'HVR_PhysicalKernel_ScaledSpectrum', 'HVR_PhysicalKernel_ScaledTranslate', 'HVR_PrimeDensity_FubiniBridge'); names = @('HVRPhysicalKernelScaledRepresentation.kernel_scaledSpectrum_eq_scaledTranslate') },
    @{ module = 'HVR_PrimeDensity_IndicatorIntegral'; deps = @('HVR_HalfLine_IndicatorConvolution', 'HVR_PrimeDensity_SpatialAbel'); names = @('HVRPrimeDensityIndicatorIntegral.halfLineConvolution_eq_Ioi') },
    @{ module = 'HVR_PrimeBoundary_EventualAbelGlue'; deps = @('HVR_PrimeBoundary_EventualDomination', 'HVR_PrimeDensity_SpatialAbel', 'HVR_PrimeDensity_FubiniIntegrable'); names = @('HVRPrimeBoundaryEventualAbelGlue.frequency_integral_tendsto_boundary_of_compact_support', 'HVRPrimeBoundaryEventualAbelGlue.undamped_eq_ordinaryBoundary_of_compact_support') },
    @{ module = 'HVR_PrimeDensity_HalfLineSmoothing'; deps = @('HVR_HalfLine_IndicatorConvolution', 'HVR_PrimeDensity_AbelGlueConditional', 'HVR_PrimeDensity_ConcentratedSqueeze'); names = @('HVRPrimeDensityHalfLineSmoothing.smoothing_tendsto_one_of_halfLine_error', 'HVRPrimeDensityHalfLineSmoothing.both_smoothing_limits_of_halfLine_errors', 'HVRPrimeDensityHalfLineSmoothing.smoothing_tendsto_one_of_frequency_test') },
    @{ module = 'HVR_PrimeBoundary_CompactGlue'; deps = @('HVR_PrimeBoundary_EventualAbelGlue', 'HVR_PrimeBoundary_FrequencyMeasurable'); names = @('HVRPrimeBoundaryCompactGlue.undamped_eq_ordinaryBoundary_of_compact', 'HVRPrimeBoundaryCompactGlue.undamped_tendsto_zero_of_compact') },
    @{ module = 'HVR_PrimeDensity_SmoothingDecomposition'; deps = @('HVR_PrimeDensity_HalfLineSmoothing'); names = @('HVRPrimeDensitySmoothingDecomposition.logPrimeDensity_zero_of_nonpos', 'HVRPrimeDensitySmoothingDecomposition.logPrimeDensity_strict_indicator_decomposition', 'HVRPrimeDensitySmoothingDecomposition.reflectedKernel_integrable', 'HVRPrimeDensitySmoothingDecomposition.reflectedKernel_integral') },
    @{ module = 'HVR_PrimeDensity_ScaledSpectrumDecay'; deps = @('HVR_PhysicalKernel_ScaledSpectrum', 'HVR_PrimeBoundary_CompactGlue'); names = @('HVRPrimeDensityScaledSpectrumDecay.scaledSpectrum_undamped_tendsto_zero') },
    @{ module = 'HVR_PrimeDensity_IntegralDecomposition'; deps = @('HVR_PrimeDensity_SmoothingDecomposition'); names = @('HVRPrimeDensityIntegralDecomposition.forward_eq_backward_reflection', 'HVRPrimeDensityIntegralDecomposition.undamped_ofReal_re') },
    @{ module = 'HVR_PrimeDensity_ScaledPhysicalDecay'; deps = @('HVR_PhysicalKernel_ScaledRepresentation', 'HVR_PrimeDensity_ScaledSpectrumDecay'); names = @('HVRPrimeDensityScaledPhysicalDecay.scaledSpectrum_inverseKernel_integrable', 'HVRPrimeDensityScaledPhysicalDecay.scaledPhysical_undamped_tendsto_zero') },
    @{ module = 'HVR_PrimeDensity_ReflectedSpectrum'; deps = @('HVR_PrimeDensity_ScaledSpectrumDecay'); names = @('HVRPrimeDensityReflectedSpectrum.kernel_reflectFrequency', 'HVRPrimeDensityReflectedSpectrum.reflectedScaledSpectrum_zero_of_band', 'HVRPrimeDensityReflectedSpectrum.reflectedScaledSpectrum_compact', 'HVRPrimeDensityReflectedSpectrum.reflected_scaledSpectrum_undamped_tendsto_zero') },
    @{ module = 'HVR_PrimeDensity_ScaledConditionalEndpoint'; deps = @('HVR_PhysicalKernel_TailScaling', 'HVR_PrimeDensity_ScaledSpectrumDecay', 'HVR_PrimeDensity_SmoothingDecomposition', 'HVR_PrimeDensity_PNTConditional'); names = @('HVRPrimeDensityScaledConditionalEndpoint.scaled_smoothing_limits_of_data', 'HVRPrimeDensityScaledConditionalEndpoint.theta_ratio_tendsto_one_of_scaled_smoothing_data') },
    @{ module = 'HVR_PrimeDensity_BackwardDecomposition'; deps = @('HVR_PrimeDensity_IndicatorIntegral', 'HVR_PrimeDensity_IntegralDecomposition', 'HVR_PrimeDensity_WeightedIntegrability'); names = @('HVRPrimeDensityBackwardDecomposition.backward_eq_halfLine_add_error', 'HVRPrimeDensityBackwardDecomposition.forward_eq_halfLine_add_reflected_error') },
    @{ module = 'HVR_PrimeDensity_ReflectedPhysicalDecay'; deps = @('HVR_PrimeDensity_ReflectedSpectrum', 'HVR_PrimeDensity_ScaledPhysicalDecay'); names = @('HVRPrimeDensityReflectedPhysicalDecay.reflectedSpectrum_kernel_eq_reflectedPhysical', 'HVRPrimeDensityReflectedPhysicalDecay.reflectedPhysical_undamped_tendsto_zero') },
    @{ module = 'HVR_PrimeDensity_DecompositionEndpoint'; deps = @('HVR_PrimeDensity_ReflectedPhysicalDecay', 'HVR_PhysicalKernel_TailScaling', 'HVR_PrimeDensity_IntegralDecomposition', 'HVR_PrimeDensity_PNTConditional'); names = @('HVRPrimeDensityDecompositionEndpoint.scaled_smoothing_limits_of_backward_decomposition', 'HVRPrimeDensityDecompositionEndpoint.theta_ratio_tendsto_one_of_backward_decomposition') },
    @{ module = 'HVR_PrimeDensity_FinalRoot'; deps = @('HVR_PrimeDensity_DecompositionEndpoint', 'HVR_PrimeDensity_BackwardDecomposition'); names = @('HVRPrimeDensityFinalRoot.backwardDecomposition', 'HVRPrimeDensityFinalRoot.actual_prime_concentrated_smoothing', 'HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one') },
  )
  # Reuse only objects associated with the immediately preceding user-supplied
  # successful module builds. Every copied object is freshly theorem-audited.
  # A single Mathlib witness is recorded; cache provenance is therefore partial.
  $cacheEv = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_BOUNDARY_RESIDUES_FIX2\evidence\20261103-034324-737-32daf4ff'
  $recentRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_ZERO_FREE_BOUNDARY_FIX1\evidence'
  if (Test-Path -LiteralPath $recentRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $recentRoot -Directory | Sort-Object Name -Descending)) {
      $candidateResult = Join-Path $candidateDir.FullName 'result.txt'
      $candidateProvenance = Join-Path $candidateDir.FullName 'provenance.txt'
      if ((Test-Path -LiteralPath $candidateResult -PathType Leaf) -and
          (Test-Path -LiteralPath $candidateProvenance -PathType Leaf)) {
        $resultText = Get-Content -LiteralPath $candidateResult -Encoding UTF8 -Raw
        if ($resultText -match '(?m)^RESULT=PASS\s*$') {
          $cacheEv = $candidateDir.FullName
          break
        }
      }
    }
  }
  # The reported run below failed overall, but the listed prior modules,
  # including the squeeze, individually built and passed their named audits.
  # Object reuse still requires all per-module hashes and a fresh audit.
  $smoothingEv = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_SMOOTHING_GERMS\evidence\20261103-040310-839-0c3cf145'
  if (Test-Path -LiteralPath (Join-Path $smoothingEv 'provenance.txt') -PathType Leaf) {
    $cacheEv = $smoothingEv
  }
  # The user's next run passed all 28 scoped modules and named audits.
  $latestEv = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_SMOOTHING_GERMS_FIX1\evidence\20261103-041103-962-33bb363c'
  if ((Test-Path -LiteralPath (Join-Path $latestEv 'provenance.txt') -PathType Leaf) -and
      (Test-Path -LiteralPath (Join-Path $latestEv 'result.txt') -PathType Leaf) -and
      ((Get-Content -LiteralPath (Join-Path $latestEv 'result.txt') -Raw -Encoding UTF8) -match '(?m)^RESULT=PASS\s*$')) {
    $cacheEv = $latestEv
  }
  # Search the reported passing Mellin run; each object still requires
  # matching context and hashes and receives a fresh named axiom audit.
  $mellinRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_PRIME_MELLIN_FIX1\evidence'
  if (Test-Path -LiteralPath $mellinRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $mellinRoot -Directory | Sort-Object Name -Descending)) {
      $candidateResult = Join-Path $candidateDir.FullName 'result.txt'
      $candidateProvenance = Join-Path $candidateDir.FullName 'provenance.txt'
      if ((Test-Path -LiteralPath $candidateResult -PathType Leaf) -and
          (Test-Path -LiteralPath $candidateProvenance -PathType Leaf) -and
          ((Get-Content -LiteralPath $candidateResult -Encoding UTF8 -Raw) -match '(?m)^RESULT=PASS\s*$')) {
        $cacheEv = $candidateDir.FullName
        break
      }
    }
  }
  # Reuse the user's passing growth run when its recorded provenance matches.
  $growthRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_PRIME_GROWTH_FIX1\evidence'
  if (Test-Path -LiteralPath $growthRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $growthRoot -Directory | Sort-Object Name -Descending)) {
      $candidateResult = Join-Path $candidateDir.FullName 'result.txt'
      $candidateProvenance = Join-Path $candidateDir.FullName 'provenance.txt'
      if ((Test-Path -LiteralPath $candidateResult -PathType Leaf) -and
          (Test-Path -LiteralPath $candidateProvenance -PathType Leaf) -and
          ((Get-Content -LiteralPath $candidateResult -Encoding UTF8 -Raw) -match '(?m)^RESULT=PASS\s*$')) {
        $cacheEv = $candidateDir.FullName
        break
      }
    }
  }
  # This run failed overall, but log-density and log-substitution individually
  # built and passed their named audits. Hash checks and fresh audits apply.
  $logEv = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_PRIME_LOG_COORDINATES\evidence\20261103-050126-557-6b90928a'
  if (Test-Path -LiteralPath (Join-Path $logEv 'provenance.txt') -PathType Leaf) {
    $cacheEv = $logEv
  }
  # Search the user's most recent fully passing log-coordinate run.
  $logFixRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_PRIME_LOG_COORDINATES_FIX1\evidence'
  if (Test-Path -LiteralPath $logFixRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $logFixRoot -Directory | Sort-Object Name -Descending)) {
      $candidateResult = Join-Path $candidateDir.FullName 'result.txt'
      $candidateProvenance = Join-Path $candidateDir.FullName 'provenance.txt'
      if ((Test-Path -LiteralPath $candidateResult -PathType Leaf) -and
          (Test-Path -LiteralPath $candidateProvenance -PathType Leaf) -and
          ((Get-Content -LiteralPath $candidateResult -Encoding UTF8 -Raw) -match '(?m)^RESULT=PASS\s*$')) {
        $cacheEv = $candidateDir.FullName
        break
      }
    }
  }
  # The user reported a passing FIX2 run of the prime-density Laplace chain.
  $laplaceRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_PRIME_LAPLACE_FIX2\evidence'
  if (Test-Path -LiteralPath $laplaceRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $laplaceRoot -Directory | Sort-Object Name -Descending)) {
      $candidateResult = Join-Path $candidateDir.FullName 'result.txt'
      $candidateProvenance = Join-Path $candidateDir.FullName 'provenance.txt'
      if ((Test-Path -LiteralPath $candidateResult -PathType Leaf) -and
          (Test-Path -LiteralPath $candidateProvenance -PathType Leaf) -and
          ((Get-Content -LiteralPath $candidateResult -Encoding UTF8 -Raw) -match '(?m)^RESULT=PASS\s*$')) {
        $cacheEv = $candidateDir.FullName
        break
      }
    }
  }
  # This reported run had no final result yet: only the three window modules
  # are added to the reuse allowlist based on their individual named audits.
  # Source/object/context/dependency checks and fresh audits still apply.
  $fourierEv = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_FOURIER_SMOOTHING_FIX1\evidence\20261103-122404-934-c1ff49bd'
  if (Test-Path -LiteralPath (Join-Path $fourierEv 'provenance.txt') -PathType Leaf) {
    $cacheEv = $fourierEv
  }
  # Prefer the user's successful FIX2 result; copied objects are re-audited.
  $fourierFixRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_FOURIER_SMOOTHING_FIX2\evidence'
  if (Test-Path -LiteralPath $fourierFixRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $fourierFixRoot -Directory | Sort-Object Name -Descending)) {
      $candidateResult = Join-Path $candidateDir.FullName 'result.txt'
      $candidateProvenance = Join-Path $candidateDir.FullName 'provenance.txt'
      if ((Test-Path -LiteralPath $candidateResult -PathType Leaf) -and
          (Test-Path -LiteralPath $candidateProvenance -PathType Leaf) -and
          ((Get-Content -LiteralPath $candidateResult -Encoding UTF8 -Raw) -match '(?m)^RESULT=PASS\s*$')) {
        $cacheEv = $candidateDir.FullName
        break
      }
    }
  }
  # The candidate run reported these three builds individually, even though
  # the overall run failed. Only reuse if their recorded objects are present;
  # the normal provenance checks and fresh theorem-level audits still apply.
  $convRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_CONVOLUTION_CANDIDATE\evidence'
  if (Test-Path -LiteralPath $convRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $convRoot -Directory | Sort-Object Name -Descending)) {
      $prov = Join-Path $candidateDir.FullName 'provenance.txt'
      $paths = Join-Path $candidateDir.FullName 'lean-path.txt'
      $names = @('HVR_HalfLine_IndicatorConvolution', 'HVR_PrimeDensity_FubiniBridge', 'HVR_PhysicalKernel_Candidate')
      $complete = (Test-Path -LiteralPath $prov -PathType Leaf) -and (Test-Path -LiteralPath $paths -PathType Leaf)
      if ($complete) {
        $provText = Get-Content -LiteralPath $prov -Encoding UTF8 -Raw
        foreach ($name in $names) {
          if (($provText -notmatch "(?m)^OBJECT_${name}_SHA256=[0-9a-fA-F]{64}\s*$") -or
              -not (Test-Path -LiteralPath (Join-Path (Join-Path $candidateDir.FullName 'olean') ($name + '.olean')) -PathType Leaf)) {
            $complete = $false; break
          }
        }
      }
      if ($complete) { $cacheEv = $candidateDir.FullName; break }
    }
  }
  # Prefer the externally reported passing convolution FIX1 run, after
  # checking its recorded result. The normal per-object checks still apply.
  $convFixRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_CONVOLUTION_FIX1\evidence'
  if (Test-Path -LiteralPath $convFixRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $convFixRoot -Directory | Sort-Object Name -Descending)) {
      $result = Join-Path $candidateDir.FullName 'result.txt'
      $prov = Join-Path $candidateDir.FullName 'provenance.txt'
      if ((Test-Path -LiteralPath $result -PathType Leaf) -and
          (Test-Path -LiteralPath $prov -PathType Leaf) -and
          ((Get-Content -LiteralPath $result -Encoding UTF8 -Raw) -match '(?m)^RESULT=PASS\s*$')) {
        $cacheEv = $candidateDir.FullName; break
      }
    }
  }
  # The kernel-preparation run failed overall, but the two modules below
  # were reported built and audited individually. Verify records and files;
  # the usual context/hash checks and fresh theorem audits still apply.
  $prepRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_KERNEL_PREPARATION_CANDIDATE\evidence'
  if (Test-Path -LiteralPath $prepRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $prepRoot -Directory | Sort-Object Name -Descending)) {
      $prov = Join-Path $candidateDir.FullName 'provenance.txt'
      $paths = Join-Path $candidateDir.FullName 'lean-path.txt'
      $names = @('HVR_PhysicalKernel_WindowAlgebra', 'HVR_SpectralSeedCorrelation')
      $complete = (Test-Path -LiteralPath $prov -PathType Leaf) -and (Test-Path -LiteralPath $paths -PathType Leaf)
      if ($complete) {
        $provText = Get-Content -LiteralPath $prov -Encoding UTF8 -Raw
        foreach ($name in $names) {
          if (($provText -notmatch "(?m)^OBJECT_${name}_SHA256=[0-9a-fA-F]{64}\s*$") -or
              -not (Test-Path -LiteralPath (Join-Path (Join-Path $candidateDir.FullName 'olean') ($name + '.olean')) -PathType Leaf)) {
            $complete = $false; break
          }
        }
      }
      if ($complete) { $cacheEv = $candidateDir.FullName; break }
    }
  }
  # Prefer a complete externally reported kernel-preparation FIX1 run.
  $prepFixRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_KERNEL_PREPARATION_FIX1\evidence'
  if (Test-Path -LiteralPath $prepFixRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $prepFixRoot -Directory | Sort-Object Name -Descending)) {
      $result = Join-Path $candidateDir.FullName 'result.txt'
      $prov = Join-Path $candidateDir.FullName 'provenance.txt'
      if ((Test-Path -LiteralPath $result -PathType Leaf) -and
          (Test-Path -LiteralPath $prov -PathType Leaf) -and
          ((Get-Content -LiteralPath $result -Encoding UTF8 -Raw) -match '(?m)^RESULT=PASS\s*$')) {
        $cacheEv = $candidateDir.FullName; break
      }
    }
  }
  # The prior run failed overall, but these modules were reported built.
  # Their reuse is conditional on recorded objects and the normal hash checks;
  # every reused theorem receives a fresh audit in this run.
  $abelRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_ABEL_LIMITS_CANDIDATE\evidence'
  if (Test-Path -LiteralPath $abelRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $abelRoot -Directory | Sort-Object Name -Descending)) {
      $prov = Join-Path $candidateDir.FullName 'provenance.txt'
      $paths = Join-Path $candidateDir.FullName 'lean-path.txt'
      $names = @('HVR_PrimeBoundary_AbelLimitConditional', 'HVR_PhysicalKernel_CanonicalWindow', 'HVR_SpectralCorrelation_Compact', 'HVR_SpectralCorrelation_Regularity')
      $complete = (Test-Path -LiteralPath $prov -PathType Leaf) -and (Test-Path -LiteralPath $paths -PathType Leaf)
      if ($complete) {
        $provText = Get-Content -LiteralPath $prov -Encoding UTF8 -Raw
        foreach ($name in $names) {
          if (($provText -notmatch "(?m)^OBJECT_${name}_SHA256=[0-9a-fA-F]{64}\s*$") -or
              -not (Test-Path -LiteralPath (Join-Path (Join-Path $candidateDir.FullName 'olean') ($name + '.olean')) -PathType Leaf)) {
            $complete = $false; break
          }
        }
      }
      if ($complete) { $cacheEv = $candidateDir.FullName; break }
    }
  }
  # Prefer the reported passing Abel-limits FIX1 evidence. The standard
  # per-object provenance checks and fresh audits still apply.
  $abelFixRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_ABEL_LIMITS_FIX1\evidence'
  if (Test-Path -LiteralPath $abelFixRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $abelFixRoot -Directory | Sort-Object Name -Descending)) {
      $result = Join-Path $candidateDir.FullName 'result.txt'
      $prov = Join-Path $candidateDir.FullName 'provenance.txt'
      if ((Test-Path -LiteralPath $result -PathType Leaf) -and
          (Test-Path -LiteralPath $prov -PathType Leaf) -and
          ((Get-Content -LiteralPath $result -Encoding UTF8 -Raw) -match '(?m)^RESULT=PASS\s*$')) {
        $cacheEv = $candidateDir.FullName; break
      }
    }
  }
  # These three builds were reported successful in the prior, incomplete
  # excerpt. Reuse remains subject to all hash checks and fresh named audits.
  $smoothRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_SMOOTHING_BRIDGES_CANDIDATE\evidence'
  if (Test-Path -LiteralPath $smoothRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $smoothRoot -Directory | Sort-Object Name -Descending)) {
      $prov = Join-Path $candidateDir.FullName 'provenance.txt'
      $paths = Join-Path $candidateDir.FullName 'lean-path.txt'
      $names = @('HVR_PrimeBoundary_EventualAbelGlue', 'HVR_PrimeBoundary_CompactGlue', 'HVR_PrimeDensity_HalfLineSmoothing')
      $complete = (Test-Path -LiteralPath $prov -PathType Leaf) -and (Test-Path -LiteralPath $paths -PathType Leaf)
      if ($complete) {
        $provText = Get-Content -LiteralPath $prov -Encoding UTF8 -Raw
        foreach ($name in $names) {
          if (($provText -notmatch "(?m)^OBJECT_${name}_SHA256=[0-9a-fA-F]{64}\s*$") -or
              -not (Test-Path -LiteralPath (Join-Path (Join-Path $candidateDir.FullName 'olean') ($name + '.olean')) -PathType Leaf)) {
            $complete = $false; break
          }
        }
      }
      if ($complete) { $cacheEv = $candidateDir.FullName; break }
    }
  }
  # Prefer the reported passing smoothing-bridges FIX1 evidence. Reuse remains
  # subject to the existing context/hash checks and fresh named audits.
  $smoothFixRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_SMOOTHING_BRIDGES_FIX1\evidence'
  if (Test-Path -LiteralPath $smoothFixRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $smoothFixRoot -Directory | Sort-Object Name -Descending)) {
      $result = Join-Path $candidateDir.FullName 'result.txt'
      $prov = Join-Path $candidateDir.FullName 'provenance.txt'
      if ((Test-Path -LiteralPath $result -PathType Leaf) -and
          (Test-Path -LiteralPath $prov -PathType Leaf) -and
          ((Get-Content -LiteralPath $result -Encoding UTF8 -Raw) -match '(?m)^RESULT=PASS\s*$')) {
        $cacheEv = $candidateDir.FullName; break
      }
    }
  }
  # Prefer the reported passing kernel-connections candidate evidence.
  # Per-object provenance checks and fresh named audits still apply.
  $connRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_KERNEL_CONNECTIONS_CANDIDATE\evidence'
  if (Test-Path -LiteralPath $connRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $connRoot -Directory | Sort-Object Name -Descending)) {
      $result = Join-Path $candidateDir.FullName 'result.txt'
      $prov = Join-Path $candidateDir.FullName 'provenance.txt'
      if ((Test-Path -LiteralPath $result -PathType Leaf) -and
          (Test-Path -LiteralPath $prov -PathType Leaf) -and
          ((Get-Content -LiteralPath $result -Encoding UTF8 -Raw) -match '(?m)^RESULT=PASS\s*$')) {
        $cacheEv = $candidateDir.FullName; break
      }
    }
  }
  # Prefer the user-reported failed run only for its individually successful
  # objects; normal provenance checks and fresh theorem audits still apply.
  $finalEv = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_FINAL_BRIDGES_CANDIDATE\evidence\20261103-150914-248-2e1533c3'
  $finalProv = Join-Path $finalEv 'provenance.txt'
  $finalPaths = Join-Path $finalEv 'lean-path.txt'
  $finalNames = @('HVR_PrimeDensity_IntegralDecomposition', 'HVR_PrimeDensity_ReflectedSpectrum', 'HVR_PrimeDensity_ScaledConditionalEndpoint')
  $finalReady = (Test-Path -LiteralPath $finalProv -PathType Leaf) -and (Test-Path -LiteralPath $finalPaths -PathType Leaf)
  if ($finalReady) {
    $provText = Get-Content -LiteralPath $finalProv -Encoding UTF8 -Raw
    foreach ($name in $finalNames) {
      if (($provText -notmatch "(?m)^OBJECT_${name}_SHA256=[0-9a-fA-F]{64}\s*$") -or
          -not (Test-Path -LiteralPath (Join-Path (Join-Path $finalEv 'olean') ($name + '.olean')) -PathType Leaf)) {
        $finalReady = $false; break
      }
    }
  }
  if ($finalReady) { $cacheEv = $finalEv }
  # Prefer the user-reported passing final-bridges FIX1 run. Reuse is still
  # guarded by context and object hashes, followed by fresh named audits.
  $finalFixRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_FINAL_BRIDGES_FIX1\evidence'
  if (Test-Path -LiteralPath $finalFixRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $finalFixRoot -Directory | Sort-Object Name -Descending)) {
      $result = Join-Path $candidateDir.FullName 'result.txt'
      $prov = Join-Path $candidateDir.FullName 'provenance.txt'
      if ((Test-Path -LiteralPath $result -PathType Leaf) -and
          (Test-Path -LiteralPath $prov -PathType Leaf) -and
          ((Get-Content -LiteralPath $result -Encoding UTF8 -Raw) -match '(?m)^RESULT=PASS\s*$')) {
        $cacheEv = $candidateDir.FullName; break
      }
    }
  }
  # Reuse only the two builds confirmed by the supplied excerpt, from a
  # completed FIX1 evidence run with recorded objects. Fresh audits follow.
  $thetaFixRoot = Join-Path $env:USERPROFILE 'Downloads\HVR_PNT_THETA_ASSEMBLY_FIX1\evidence'
  if (Test-Path -LiteralPath $thetaFixRoot -PathType Container) {
    foreach ($candidateDir in @(Get-ChildItem -LiteralPath $thetaFixRoot -Directory | Sort-Object Name -Descending)) {
      $prov = Join-Path $candidateDir.FullName 'provenance.txt'
      $paths = Join-Path $candidateDir.FullName 'lean-path.txt'
      $result = Join-Path $candidateDir.FullName 'result.txt'
      $names = @('HVR_PrimeDensity_IndicatorIntegral', 'HVR_PrimeDensity_ReflectedPhysicalDecay')
      $complete = (Test-Path -LiteralPath $prov -PathType Leaf) -and (Test-Path -LiteralPath $paths -PathType Leaf) -and (Test-Path -LiteralPath $result -PathType Leaf)
      if ($complete) {
        $provText = Get-Content -LiteralPath $prov -Encoding UTF8 -Raw
        foreach ($name in $names) {
          if (($provText -notmatch "(?m)^OBJECT_${name}_SHA256=[0-9a-fA-F]{64}\s*$") -or
              -not (Test-Path -LiteralPath (Join-Path (Join-Path $candidateDir.FullName 'olean') ($name + '.olean')) -PathType Leaf)) {
            $complete = $false; break
          }
        }
      }
      if ($complete) { $cacheEv = $candidateDir.FullName; break }
    }
  }
  Write-Host "CACHE_SOURCE=$cacheEv"
  $cacheMeta = @{}
  $cacheOk = $false
  $cacheProv = Join-Path $cacheEv 'provenance.txt'
  if (Test-Path -LiteralPath $cacheProv -PathType Leaf) {
    try {
      foreach ($line in @(Get-Content -LiteralPath $cacheProv -Encoding UTF8)) {
        if ($line -match '^([^=]+)=(.*)$') { $cacheMeta[$Matches[1]] = $Matches[2] }
      }
      $compilerHash = (Get-FileHash -LiteralPath $LeanExe -Algorithm SHA256).Hash
      $witnessHash = (Get-FileHash -LiteralPath (Join-Path $mathlib 'Mathlib\Analysis\SpecialFunctions\Trigonometric\Basic.olean') -Algorithm SHA256).Hash
      $oldPathFile = Join-Path $cacheEv 'lean-path.txt'
      $pathsMatch = $false
      if (Test-Path -LiteralPath $oldPathFile -PathType Leaf) {
        $oldPaths = @(Get-Content -LiteralPath $oldPathFile -Encoding UTF8 | Select-Object -Skip 1)
        $newPaths = @($pathList | Select-Object -Skip 1)
        $pathsMatch = (($oldPaths -join ';') -ieq ($newPaths -join ';'))
      }
      $cacheOk = ($cacheMeta['COMPILER_SHA256'] -ieq $compilerHash -and
                  $cacheMeta['MATHLIB_WITNESS_SHA256'] -ieq $witnessHash -and
                  $cacheMeta['MATHLIB_ROOT'] -ieq $mathlib -and $pathsMatch)
    } catch {
      $cacheOk = $false
      Write-Host 'CACHE_CONTEXT=UNAVAILABLE_FALLBACK_TO_REBUILD'
    }
  }
  if ($cacheOk) { Write-Host 'CACHE_CONTEXT=MATCHED_PARTIAL_PROVENANCE' }
  else { Write-Host 'CACHE_CONTEXT=NO_MATCH_REBUILD' }
  $priorPassed = @('HVR_Prime_Gram', 'HVR_Prime_Summability', 'HVR_Prime_InfiniteGram',
    'HVR_Prime_BoundaryBridge', 'HVR_Prime_PowerCorrection', 'HVR_Zeta_LogDerivative', 'HVR_Prime_Complex',
    'HVR_Prime_ZetaSplit', 'HVR_PowerCorrection_Holomorphic', 'HVR_Generic_LogDerivativeResidue',
    'HVR_Correction_TermHolomorphic', 'HVR_Correction_UniformBound', 'HVR_HigherCoefficient_Reindex',
    'HVR_Correction_PrimeSubtype', 'HVR_HigherCoefficient_Geometric', 'HVR_Zeta_CorrectionIdentity',
    'HVR_Correction_BoundaryLimit', 'HVR_Zeta_PoleResidue', 'HVR_Prime_ResidueTransfer', 'HVR_Zeta_BoundaryFactor', 'HVR_Prime_PoleMass',
    'HVR_Zeta_GramResidueConditional', 'HVR_Analytic_Residue', 'HVR_Zeta_BoundarySequence', 'HVR_Zeta_ZeroFreeBoundary',
    'HVR_Positive_SmoothingSqueeze', 'HVR_Smoothing_AnalyticGerms', 'HVR_Smoothing_PoleGlue',
    'HVR_Smoothing_MonotoneNormalization', 'HVR_PrimeCount_MellinCandidate',
    'HVR_PrimeCount_GrowthCandidate', 'HVR_PrimeCount_MellinGerm',
    'HVR_PrimeLogDensity', 'HVR_PrimeCount_LogSubstitution', 'HVR_PrimeCount_ExpGrowth',
    'HVR_Complex_PoleLaplace', 'HVR_PrimeDensity_Laplace', 'HVR_Smoothing_BoundaryExtension',
    'HVR_PrimeDensity_BoundaryLink',
    'HVR_PrimeDensity_WindowBounds', 'HVR_PrimeDensity_WeightedIntegrability',
    'HVR_PrimeDensity_WindowBridge', 'HVR_PrimeDensity_BoundaryLimit',
    'HVR_PrimeBoundary_FourierDecay', 'HVR_Smoothing_FrequencySeed',
    'HVR_HalfLine_IndicatorConvolution', 'HVR_PrimeDensity_FubiniBridge', 'HVR_PhysicalKernel_Candidate',
    'HVR_PrimeDensity_FubiniIntegrable', 'HVR_PrimeDensity_ConcentratedSqueeze',
    'HVR_PrimeDensity_PNTConditional', 'HVR_PhysicalKernel_PositiveMass',
    'HVR_PhysicalKernel_WindowAlgebra', 'HVR_SpectralSeedCorrelation',
    'HVR_PrimeBoundary_OrdinaryFrequencyDecay',
    'HVR_PrimeBoundary_AbelLimitConditional', 'HVR_PhysicalKernel_CanonicalWindow',
    'HVR_SpectralCorrelation_Compact', 'HVR_SpectralCorrelation_Regularity',
    'HVR_PrimeDensity_SpatialAbel', 'HVR_PrimeDensity_AbelGlueConditional',
    'HVR_PhysicalKernel_ScaledTranslate', 'HVR_PrimeBoundary_EventualAbelGlue',
    'HVR_PrimeBoundary_CompactGlue', 'HVR_PrimeDensity_HalfLineSmoothing',
    'HVR_PrimeBoundary_EventualDomination', 'HVR_PrimeBoundary_FrequencyMeasurable',
    'HVR_PhysicalKernel_Tail', 'HVR_SpectralCorrelation_FourierSquare',
    'HVR_PhysicalKernel_WaveReal', 'HVR_PhysicalKernel_SpectralIdentity',
    'HVR_PhysicalKernel_TailScaling', 'HVR_PhysicalKernel_ScaledSpectrum',
    'HVR_PrimeDensity_ScaledSpectrumDecay', 'HVR_PrimeDensity_SmoothingDecomposition',
    'HVR_PrimeDensity_IntegralDecomposition', 'HVR_PrimeDensity_ReflectedSpectrum',
    'HVR_PrimeDensity_ScaledConditionalEndpoint',
    'HVR_PhysicalKernel_ScaledRepresentation', 'HVR_PrimeDensity_ScaledPhysicalDecay',
    'HVR_PrimeDensity_IndicatorIntegral', 'HVR_PrimeDensity_ReflectedPhysicalDecay')
  $state = @{}
  $allOk = $true
  foreach ($entry in $plan) {
    $module = $entry.module
    $source = Join-Path $pkg ($module + '.lean')
    $object = Join-Path $ol ($module + '.olean')
    if (-not (Test-Path -LiteralPath $source -PathType Leaf)) {
      Write-Host "SOURCE_MISSING=$module"; $state[$module] = 'FAIL'; $allOk = $false; continue
    }
    $hash = (Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash.ToLowerInvariant()
    Add-Content -LiteralPath (Join-Path $ev 'provenance.txt') -Value "SOURCE_${module}_SHA256=$hash"
    $blocked = $false
    foreach ($dep in $entry.deps) { if ($state[$dep] -ne 'PASS') { Write-Host "BLOCKED=$module DEPENDENCY=$dep"; $blocked = $true } }
    if ($blocked) { $state[$module] = 'BLOCKED'; $allOk = $false; continue }
    $reused = $false
    if ($cacheOk -and $module -in $priorPassed) {
      try {
        $oldObject = Join-Path (Join-Path $cacheEv 'olean') ($module + '.olean')
        $expectedSource = $cacheMeta["SOURCE_${module}_SHA256"]
        $expectedObject = $cacheMeta["OBJECT_${module}_SHA256"]
        $depsMatch = $true
        foreach ($dep in $entry.deps) {
          $depPath = Join-Path $ol ($dep + '.olean')
          $expectedDep = $cacheMeta["OBJECT_${dep}_SHA256"]
          if ([string]::IsNullOrWhiteSpace($expectedDep) -or -not (Test-Path -LiteralPath $depPath -PathType Leaf)) { $depsMatch = $false; break }
          $actualDep = (Get-FileHash -LiteralPath $depPath -Algorithm SHA256).Hash
          if ($actualDep -ine $expectedDep) { $depsMatch = $false; break }
        }
        if ($depsMatch -and -not [string]::IsNullOrWhiteSpace($expectedSource) -and
            -not [string]::IsNullOrWhiteSpace($expectedObject) -and
            $hash -ieq $expectedSource -and (Test-Path -LiteralPath $oldObject -PathType Leaf)) {
          $oldHash = (Get-FileHash -LiteralPath $oldObject -Algorithm SHA256).Hash
          if ($oldHash -ieq $expectedObject) {
            Copy-Item -LiteralPath $oldObject -Destination $object
            $copyHash = (Get-FileHash -LiteralPath $object -Algorithm SHA256).Hash
            if ($copyHash -ieq $expectedObject) { $reused = $true }
          }
        }
      } catch { Write-Host "CACHE_REUSE_ERROR=$module FALLBACK=REBUILD" }
    }
    if ($reused) { Write-Host "CACHE_REUSE=$module FRESH_AUDIT_PENDING" }
    else {
      Write-Host "CACHE_MISS=$module BUILD_FROM_SOURCE"
      if (Test-Path -LiteralPath $object -PathType Leaf) { Remove-Item -LiteralPath $object -Force }
      $ok = Invoke-Lean @('-o', $object, ($module + '.lean')) ('build_' + $module)
      if (-not $ok -or -not (Test-Path -LiteralPath $object -PathType Leaf)) { $state[$module] = 'FAIL'; $allOk = $false; continue }
    }
    $state[$module] = 'PASS'
    $hash = (Get-FileHash -LiteralPath $object -Algorithm SHA256).Hash.ToLowerInvariant()
    Add-Content -LiteralPath (Join-Path $ev 'provenance.txt') -Value "OBJECT_${module}_SHA256=$hash"
  }
  foreach ($entry in $plan) {
    $module = $entry.module
    if ($state[$module] -ne 'PASS') { Write-Host "AUDIT_SKIPPED=$module BUILD=$($state[$module])"; continue }
    $audit = Join-Path $ev ('Audit_' + $module + '.lean')
    Copy-Item -LiteralPath (Join-Path $pkg ('Audit_' + $module + '.lean')) -Destination $audit
    $ok = Invoke-Lean @($audit) ('audit_' + $module)
    if (-not $ok) { $allOk = $false; Write-Host "AXIOM_AUDIT_FAIL=$module"; continue }
    $log = Get-Content -LiteralPath (Join-Path $ev ('audit_' + $module + '.stdout.log')) -Raw
    $auditOk = $true
    foreach ($full in $entry.names) {
      $pattern = "(?s)'" + [regex]::Escape($full) + "' (?:depends on axioms: \[(?<axs>[^\]]*)\]|(?<none>does not depend on any axioms))"
      $match = [regex]::Match($log, $pattern)
      if (-not $match.Success) { Write-Host "MISSING_AXIOM_REPORT=$full"; $auditOk = $false; continue }
      if (-not $match.Groups['none'].Success) {
        $axs = @($match.Groups['axs'].Value -split ',' | ForEach-Object { $_.Trim() } | Where-Object { $_ })
        foreach ($ax in $axs) { if ($ax -notin @('propext','Classical.choice','Quot.sound')) { Write-Host "UNAPPROVED_AXIOM=$full AXIOM=$ax"; $auditOk = $false } }
      }
    }
    if ($auditOk) { Write-Host "AXIOM_AUDIT_STANDARD_ONLY=$module" }
    else { $allOk = $false; Write-Host "AXIOM_AUDIT_FAIL=$module" }
  }
  if ($TraceDependencies) {
    if ($state['HVR_Zeta_ZeroFreeBoundary'] -eq 'PASS') {
      Write-Host 'DEPENDENCY_TRACE=STARTING_DIAGNOSTIC_ONLY'
      $traceOk = Invoke-Lean @('HVR_ZeroFree_DependencyTrace.lean') 'dependency_trace'
      if ($traceOk) {
        Write-Host "DEPENDENCY_TRACE_LOG=$(Join-Path $ev 'dependency_trace.stdout.log')"
        Write-Host 'DEPENDENCY_COVERAGE=UNVERIFIED'
      } else { Write-Host 'DEPENDENCY_TRACE=FAILED_NO_INDEPENDENCE_CONCLUSION' }
    } else { Write-Host 'DEPENDENCY_TRACE=BLOCKED_ROOT_NOT_BUILT' }
    if ($state['HVR_PrimeDensity_BoundaryLink'] -eq 'PASS') {
      Write-Host 'FULL_CHAIN_DEPENDENCY_TRACE=STARTING_DIAGNOSTIC_ONLY'
      $fullTraceOk = Invoke-Lean @('HVR_FullChain_DependencyTrace.lean') 'full_chain_dependency_trace'
      if ($fullTraceOk) {
        Write-Host "FULL_CHAIN_TRACE_LOG=$(Join-Path $ev 'full_chain_dependency_trace.stdout.log')"
        Write-Host 'FULL_CHAIN_TRACE_COVERAGE=UNVERIFIED'
      } else { Write-Host 'FULL_CHAIN_DEPENDENCY_TRACE=FAILED_NO_INDEPENDENCE_CONCLUSION' }
    } else { Write-Host 'FULL_CHAIN_DEPENDENCY_TRACE=BLOCKED_ROOT_NOT_BUILT' }
    if ($state['HVR_PrimeDensity_PNTConditional'] -eq 'PASS' -and $state['HVR_PrimeDensity_AbelGlueConditional'] -eq 'PASS') {
      Write-Host 'EXPANDED_DEPENDENCY_TRACE=STARTING_DIAGNOSTIC_ONLY'
      $expandedTraceOk = Invoke-Lean @('HVR_PNT_Expanded_DependencyTrace.lean') 'expanded_dependency_trace'
      if ($expandedTraceOk) {
        Write-Host "EXPANDED_TRACE_LOG=$(Join-Path $ev 'expanded_dependency_trace.stdout.log')"
        Write-Host 'EXPANDED_TRACE_COVERAGE=UNVERIFIED'
      } else { Write-Host 'EXPANDED_DEPENDENCY_TRACE=FAILED_NO_INDEPENDENCE_CONCLUSION' }
    } else { Write-Host 'EXPANDED_DEPENDENCY_TRACE=BLOCKED_ROOT_NOT_BUILT' }
    if ($state['HVR_PrimeDensity_FinalRoot'] -eq 'PASS') {
      Write-Host 'FINAL_ROOT_TRACE=STARTING_DIAGNOSTIC_ONLY'
      $rootTraceOk = Invoke-Lean @('HVR_PNT_FinalRoot_DependencyTrace.lean') 'final_root_dependency_trace'
      if ($rootTraceOk) { Write-Host "FINAL_ROOT_TRACE_LOG=$(Join-Path $ev 'final_root_dependency_trace.stdout.log')"; Write-Host 'FINAL_ROOT_TRACE_COVERAGE=UNVERIFIED' }
      else { Write-Host 'FINAL_ROOT_TRACE=FAILED_NO_INDEPENDENCE_CONCLUSION' }
    } else { Write-Host 'FINAL_ROOT_TRACE=BLOCKED_ROOT_NOT_BUILT' }
  }
  if (-not $allOk) { Fail 'One_or_more_build_or_audit_stages_failed' }
  @('RESULT=PASS', 'SCOPE=THETA_RATIO_ROOT', 'THETA_ROOT_BUILD_AND_NAMED_AXIOM_AUDIT=PASS', 'DEPENDENCY_INDEPENDENCE=NOT_YET_VERIFIED', 'PNT=THETA_ROOT_PASS_REVIEW_PENDING', 'AXIOM_AUDIT=STANDARD_ONLY', 'MATHLIB_CACHE_PROVENANCE=USER_SUPPLIED_NOT_INDEPENDENTLY_VERIFIED') |
    Set-Content -LiteralPath (Join-Path $ev 'result.txt') -Encoding UTF8
  Write-Host 'RESULT=PASS'
  Write-Host 'SCOPE=THETA_RATIO_ROOT'
  Write-Host 'THETA_ROOT_BUILD_AND_NAMED_AXIOM_AUDIT=PASS'
  Write-Host 'MELLIN_GROWTH_BOUND=DISCHARGED_FOR_EXACT_COEFFICIENTS'
  Write-Host 'DEPENDENCY_INDEPENDENCE=NOT_YET_VERIFIED'
  Write-Host 'PNT=THETA_ROOT_PASS_REVIEW_PENDING'
  exit 0
} catch {
  $detail = $_ | Out-String
  $detail | Set-Content -LiteralPath (Join-Path $ev 'runner-error.txt') -Encoding UTF8
  Write-Host $detail
  Fail 'Runner_exception_see_runner-error.txt'
}
