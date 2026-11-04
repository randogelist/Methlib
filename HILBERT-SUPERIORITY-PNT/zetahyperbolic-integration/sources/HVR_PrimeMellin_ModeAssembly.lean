import HVR_PrimeMellin_Modes
import HVR_PrimeCount_LogSubstitution
import HVR_PrimeCount_GrowthCandidate
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic

noncomputable section

open scoped BigOperators
open MeasureTheory Filter
open HVRPrimeComplex HVRPrimeZetaSplit HVRPrimeMellinModes
open HVRPrimeCountMellin HVRPrimeCountGrowth HVRPrimeCountLogSubstitution

/-!
Prime-mode theta expansion and assembly candidate.

The strictly open mode cutoffs differ from Chebyshev.theta exactly at log-prime
endpoints; countable singleton-nullness gives the required a.e. identity. The
last theorem uses the already existing primeThetaMellin exponential change
of variables. This is a DOWNSTREAM integration candidate: its imports include
HVR_PrimeCount_MellinCandidate through the existing growth and substitution
modules. It cannot replace that file in the root without first factoring its
definitions and substitution proof into modules upstream of MellinCandidate.
Transitive dependency independence is not established. No local Lean run has
been performed; external cached build and named axiom audit are required.
-/
namespace HVRPrimeMellinModeAssembly

/-- The prime cutoff in the Chebyshev theta definition. -/
def primeCutoff (u : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊Real.exp u⌋₊).filter Nat.Prime

/-- Away from the countable mode endpoints, a prime is in the theta cutoff
exactly when its logarithmic spectral point is below the time parameter. -/
theorem mem_primeCutoff_iff (u : ℝ) (hne : ∀ n : ℕ, u ≠ Real.log (n : ℝ)) (n : ℕ) :
    n ∈ primeCutoff u ↔ Nat.Prime n ∧ Real.log (n : ℝ) < u := by
  constructor
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, hp⟩
    have hnfloor : n ≤ ⌊Real.exp u⌋₊ := (Finset.mem_Ioc.mp hnI).2
    have hnreal : (n : ℝ) ≤ Real.exp u :=
      (Nat.le_floor_iff (le_of_lt (Real.exp_pos u))).mp hnfloor
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
    have hlogle : Real.log (n : ℝ) ≤ u := by
      simpa only [Real.log_exp] using Real.log_le_log hnpos hnreal
    refine ⟨hp, ?_⟩
    rcases lt_or_eq_of_le hlogle with hlt | heq
    · exact hlt
    · exact False.elim ((hne n) heq.symm)
  · rintro ⟨hp, hlog⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨hp.pos, ?_⟩, hp⟩
    apply Nat.le_floor
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
    have hexp := Real.exp_lt_exp.mpr hlog
    have hnlt : (n : ℝ) < Real.exp u := by
      simpa only [Real.exp_log hnpos] using hexp
    exact hnlt.le

/-- Pointwise mode expansion away from logarithms of natural numbers. -/
theorem theta_exp_modes_pointwise (s : ℂ) (u : ℝ)
    (hne : ∀ n : ℕ, u ≠ Real.log (n : ℝ)) :
    (Set.Ioi (0 : ℝ)).indicator
        (fun x : ℝ => Complex.exp (-s * (x : ℂ)) *
          (Chebyshev.theta (Real.exp x) : ℂ)) u =
      ∑' n : ℕ, primeMode s n u := by
  have hterm (n : ℕ) :
      primeMode s n u =
        if n ∈ primeCutoff u then
          (Real.log (n : ℝ) : ℂ) * Complex.exp (-s * (u : ℂ))
        else 0 := by
    by_cases hn : n ∈ primeCutoff u
    · obtain ⟨hp, hlog⟩ := (mem_primeCutoff_iff u hne n).mp hn
      simp [primeMode, hn, hp, hlog]
    · by_cases hp : Nat.Prime n
      · have hlog : ¬Real.log (n : ℝ) < u := by
          intro h
          exact hn ((mem_primeCutoff_iff u hne n).mpr ⟨hp, h⟩)
        simp [primeMode, hn, hp, hlog]
      · simp [primeMode, hn, hp]
  have hsum :
      (∑' n : ℕ, primeMode s n u) =
        ∑ n ∈ primeCutoff u,
          (Real.log (n : ℝ) : ℂ) * Complex.exp (-s * (u : ℂ)) := by
    rw [tsum_eq_sum (s := primeCutoff u) (by
      intro n hn
      simp [hterm n, hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [hterm n, hn]
  have htheta :
      (Chebyshev.theta (Real.exp u) : ℂ) =
        ∑ n ∈ primeCutoff u, (Real.log (n : ℝ) : ℂ) := by
    simp [primeCutoff, Chebyshev.theta]
  by_cases hu : 0 < u
  · simp only [Set.indicator_of_mem (show u ∈ Set.Ioi (0 : ℝ) from hu)]
    rw [hsum, htheta]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  · have hempty : primeCutoff u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hp, hlog⟩ := (mem_primeCutoff_iff u hne n).mp hn
      have hone : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hp.one_lt
      have hpos : 0 < Real.log (n : ℝ) := Real.log_pos hone
      have hu' : u ≤ 0 := le_of_not_gt hu
      linarith
    have hunot : u ∉ Set.Ioi (0 : ℝ) := hu
    simp [Set.indicator_of_notMem hunot, hsum, hempty]

/-- The actual theta expansion: the excluded logarithms form a null set. -/
theorem theta_exp_modes_ae (s : ℂ) :
    ∀ᵐ u : ℝ ∂volume,
      (Set.Ioi (0 : ℝ)).indicator
          (fun x : ℝ => Complex.exp (-s * (x : ℂ)) *
            (Chebyshev.theta (Real.exp x) : ℂ)) u =
        ∑' n : ℕ, primeMode s n u := by
  have hne : ∀ᵐ u : ℝ ∂volume, ∀ n : ℕ, u ≠ Real.log (n : ℝ) := by
    rw [ae_all_iff]
    intro n
    exact volume.ae_ne (Real.log (n : ℝ))
  filter_upwards [hne] with u hu
  exact theta_exp_modes_pointwise s u hu

/-- The actual prime/theta Laplace identity without the expansion hypothesis. -/
theorem theta_exp_laplace_unconditional (sigma t : ℝ) (hsigma : 1 < sigma) :
    (∫ u : ℝ in Set.Ioi 0,
      Complex.exp (-(zetaPoint sigma t) * (u : ℂ)) *
        (Chebyshev.theta (Real.exp u) : ℂ)) =
      primeSeries sigma t 1 / zetaPoint sigma t :=
  theta_exp_laplace_of_prime_expansion sigma t hsigma
    (theta_exp_modes_ae (zetaPoint sigma t))

/-- The existing exponential substitution identifies its Mellin integral with
the prime-mode Laplace integral. This is downstream, not an upstream root swap. -/
theorem primeSeries_eq_mul_mellin_via_modes (sigma t : ℝ) (hsigma : 1 < sigma) :
    primeSeries sigma t 1 =
      zetaPoint sigma t * primeThetaMellin (zetaPoint sigma t) := by
  have hz : zetaPoint sigma t ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [zetaPoint] at hr
    linarith
  have hint : primeThetaMellin (zetaPoint sigma t) =
      primeSeries sigma t 1 / zetaPoint sigma t := by
    rw [primeThetaMellin_eq_exp_integral]
    calc
      (∫ u : ℝ in Set.Ioi 0,
          primeTheta (Real.exp u) * Complex.exp (-(zetaPoint sigma t) * (u : ℂ))) =
          ∫ u : ℝ in Set.Ioi 0,
            Complex.exp (-(zetaPoint sigma t) * (u : ℂ)) *
              (Chebyshev.theta (Real.exp u) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [] with u
        rw [primeTheta_eq_chebyshev]
        ring
      _ = _ := theta_exp_laplace_unconditional sigma t hsigma
  calc
    primeSeries sigma t 1 =
        zetaPoint sigma t * (primeSeries sigma t 1 / zetaPoint sigma t) := by
      field_simp <;> ring
    _ = zetaPoint sigma t * primeThetaMellin (zetaPoint sigma t) := by
      rw [hint]

end HVRPrimeMellinModeAssembly

