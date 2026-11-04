import HVR_PrimeDensity_FinalRoot
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment

open Lean Elab Command

namespace HVRCallReductionTrace

def directControl := @MeasureTheory.integral_integral_swap
def indirectControl := @directControl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target := `MeasureTheory.integral_integral_swap
  for c in #[`HVRCallReductionTrace.directControl, `HVRCallReductionTrace.indirectControl] do
    let reached ← liftCoreM c.transitivelyUsedConstants
    unless reached.contains target do throwError "CONTROL_FAILED={c}|{target}"
  let root := `HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one
  let deps ← liftCoreM root.transitivelyUsedConstants
  let anchor := `HVRPrimeDensityFinalRoot.actual_prime_concentrated_smoothing
  unless deps.contains anchor do throwError "ROOT_CONTROL_FAILED={root}|{anchor}"
  let targets : Array Name := #[
    `MeasureTheory.tendsto_integral_of_dominated_convergence,
    `MeasureTheory.tendsto_integral_filter_of_dominated_convergence,
    `MeasureTheory.integral_integral_swap,
    `MeasureTheory.integral_tendsto_of_tendsto_of_antitone,
    `ArithmeticFunction.vonMangoldt_apply_prime, `ArithmeticFunction.vonMangoldt_apply_pow,
    `ArithmeticFunction.vonMangoldt_eq_zero_iff, `ArithmeticFunction.LSeriesSummable_vonMangoldt,
    `LSeriesSummable.sub, `LSeries_sub, `tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers,
    `HasSum.tsum_eq, `HasSum.mul_left, `hasSum_geometric_of_norm_lt_one,
    `primorial_add_le, `primorial_succ, `primorial_pos, `Nat.choose_symm_half,
    `Nat.choose_middle_le_pow, `Chebyshev.theta_eq_log_primorial,
    `riemannZeta_eq_inv_sub_mul, `deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add,
    `log_deriv_riemannZeta_eq_neg_inv_sub_add, `analyticOn_riemannZeta,
    `MeasureTheory.tendsto_lintegral_norm_of_dominated_convergence,
    `MeasureTheory.tendsto_integral_of_L1, `MeasureTheory.integral_prod, `MeasureTheory.integral_prod_symm,
    `riemannZeta₁_ne_zero_of_near_one, `differentiable_riemannZeta₁,
    `riemannZeta₁_one, `deriv_riemannZeta₁_one, `differentiable_riemannZeta₀,
    `LSeries_convolution', `LSeries_deriv, `LSeries_congr, `LSeries_one_eq_riemannZeta,
    `ArithmeticFunction.LSeries_zeta_eq_riemannZeta, `LSeriesSummable_of_bounded_of_one_lt_re,
    `LSeries.convolution_one_eq_convolution_zeta, `ArithmeticFunction.const_one_eq_zeta,
    `LSeriesSummable_congr, `zeta_eq_tsum_one_div_nat_cpow, `LSeries.term_convolution',
    `HVRPrimeBoundaryEventualAbelGlue.frequency_integral_tendsto_boundary_of_compact_support,
    `HVRPrimeDensitySpatialAbel.spatial_abel_tendsto,
    `HVRNativeDominatedLimit.integral_error_le_weighted,
    `HVRNativeZetaPoleEquality.regularized_hasDerivAt,
    `HVRNativeOneZetaSummability.convolution_sum, `HVRMajorZetaLogDerivative.deriv_one_series,
    `HVRHigherCoefficientGeometric.complex_geometric_hasSum]
  for t in targets do
    if (env.find? t).isNone then
      IO.println s!"TARGET_UNKNOWN={root}|{t}"
    else if deps.contains t then
      IO.println s!"TARGET_FOUND={root}|{t}"
    else
      IO.println s!"TARGET_NOT_SEEN_COVERAGE_UNVERIFIED={root}|{t}"
  let mut hidden : Nat := 0
  let mut missing : Nat := 0
  for n in deps do
    match env.find? n with
    | none => missing := missing + 1
    | some ci => if ci.isTheorem && (ci.value? true).isNone then hidden := hidden + 1
  IO.println s!"REACHED_THEOREM_BODIES_UNAVAILABLE={hidden}"
  IO.println s!"REACHED_DECLARATIONS_MISSING={missing}"
  IO.println "DEPENDENCY_COVERAGE=UNVERIFIED"
  IO.println "CALL_REDUCTION_TRACE=COMPLETE"

end HVRCallReductionTrace
