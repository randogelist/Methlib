import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace CEATheta

structure CriticalToRegularityCertificate
    (H12sup H32int H1L4 L6L4 C6 : ℝ)
    (Serrin46 Regular : Prop) : Prop where
  hH12sup : 0 ≤ H12sup
  hH32int : 0 ≤ H32int
  hH1L4 : 0 ≤ H1L4
  hL6L4 : 0 ≤ L6L4
  hC6 : 0 ≤ C6
  interpolation : H1L4 ≤ H12sup * H32int
  sobolev_integrated : L6L4 ≤ C6 ^ 4 * H1L4
  serrin46_of_finite_bound :
    (L6L4 ≤ C6 ^ 4 * (H12sup * H32int)) → Serrin46
  regular_of_serrin46 : Serrin46 → Regular

theorem criticalPair_to_L4L6_bound
    {H12sup H32int H1L4 L6L4 C6 : ℝ}
    {Serrin46 Regular : Prop}
    (c : CriticalToRegularityCertificate
      H12sup H32int H1L4 L6L4 C6 Serrin46 Regular) :
    L6L4 ≤ C6 ^ 4 * (H12sup * H32int) := by
  have hCpow : 0 ≤ C6 ^ 4 := pow_nonneg c.hC6 4
  calc
    L6L4 ≤ C6 ^ 4 * H1L4 := c.sobolev_integrated
    _ ≤ C6 ^ 4 * (H12sup * H32int) :=
      mul_le_mul_of_nonneg_left c.interpolation hCpow

theorem criticalPair_to_Serrin46
    {H12sup H32int H1L4 L6L4 C6 : ℝ}
    {Serrin46 Regular : Prop}
    (c : CriticalToRegularityCertificate
      H12sup H32int H1L4 L6L4 C6 Serrin46 Regular) :
    Serrin46 :=
  c.serrin46_of_finite_bound (criticalPair_to_L4L6_bound c)

theorem CEA_theta_criticalPair_to_regular
    {H12sup H32int H1L4 L6L4 C6 : ℝ}
    {Serrin46 Regular : Prop}
    (c : CriticalToRegularityCertificate
      H12sup H32int H1L4 L6L4 C6 Serrin46 Regular) :
    Regular :=
  c.regular_of_serrin46 (criticalPair_to_Serrin46 c)

#print axioms CEATheta.criticalPair_to_L4L6_bound
#print axioms CEATheta.criticalPair_to_Serrin46
#print axioms CEATheta.CEA_theta_criticalPair_to_regular

end CEATheta
