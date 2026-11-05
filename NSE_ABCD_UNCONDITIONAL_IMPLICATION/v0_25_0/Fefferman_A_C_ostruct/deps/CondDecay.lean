import CondDatum
import CondGaussian

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal

noncomputable section

/-- A one-variable extension across the origin of the explicit radial factor. -/
def RadialSchwartzExtension : Prop :=
  ∃ G : SchwartzMap ℝ ℝ, ∀ s : ℝ, 0 ≤ s → G s = Real.exp (-s) / (1 + s)

private def represented (f : RSpace → ℝ) : Prop :=
  ∃ g : SchwartzMap RSpace ℝ, (g : RSpace → ℝ) = f

private theorem sq3_nonneg (x : RSpace) : 0 ≤ normSq3 x := by
  unfold normSq3
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

private theorem abs_le_one_add_self_mul (t : ℝ) : |t| ≤ 1 + t * t := by
  apply abs_le.mpr
  constructor
  · nlinarith only [sq_nonneg (t + 1), sq_nonneg t]
  · nlinarith only [sq_nonneg (t - 1), sq_nonneg t]

private theorem coordinate_sq_le_normSq3 (x : RSpace) (i : Fin 3) :
    x i * x i ≤ normSq3 x := by
  fin_cases i
  · change x 0 * x 0 ≤ x 0 * x 0 + x 1 * x 1 + x 2 * x 2
    nlinarith only [sq_nonneg (x 1), sq_nonneg (x 2)]
  · change x 1 * x 1 ≤ x 0 * x 0 + x 1 * x 1 + x 2 * x 2
    nlinarith only [sq_nonneg (x 0), sq_nonneg (x 2)]
  · change x 2 * x 2 ≤ x 0 * x 0 + x 1 * x 1 + x 2 * x 2
    nlinarith only [sq_nonneg (x 0), sq_nonneg (x 1)]

private theorem psi_represented (h : RadialSchwartzExtension) : represented psi := by
  obtain ⟨G, hG⟩ := h
  have hcoord (i : Fin 3) :
      Function.HasTemperateGrowth (fun x : RSpace => x i) := by
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasTemperateGrowth
  have htemp : Function.HasTemperateGrowth normSq3 := by
    exact (((hcoord 0).mul (hcoord 0)).add ((hcoord 1).mul (hcoord 1))).add
      ((hcoord 2).mul (hcoord 2))
  have hproper : ∃ (k : ℕ) (C : ℝ), ∀ x : RSpace, ‖x‖ ≤ C * (1 + ‖normSq3 x‖) ^ k := by
    refine ⟨1, 1, fun x => ?_⟩
    simp only [pow_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (sq3_nonneg x)]
    apply (pi_norm_le_iff_of_nonneg (by linarith [sq3_nonneg x])).2
    intro i
    rw [Real.norm_eq_abs]
    exact (abs_le_one_add_self_mul (x i)).trans
      (add_le_add (le_refl (1 : ℝ)) (coordinate_sq_le_normSq3 x i))
  refine ⟨SchwartzMap.compCLM ℝ htemp hproper G, ?_⟩
  funext x
  exact hG (normSq3 x) (sq3_nonneg x)

private theorem rep_partial {f : RSpace → ℝ} (h : represented f) (i : Fin 3) :
    represented (spatialDerivative i f) := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨SchwartzMap.evalCLM ℝ RSpace ℝ (basisDirection i)
    (SchwartzMap.fderivCLM ℝ RSpace ℝ g), rfl⟩

private theorem rep_add {f g : RSpace → ℝ} (hf : represented f) (hg : represented g) :
    represented (fun x => f x + g x) := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  exact ⟨a + b, rfl⟩

private theorem rep_sub {f g : RSpace → ℝ} (hf : represented f) (hg : represented g) :
    represented (fun x => f x - g x) := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  exact ⟨a - b, rfl⟩

private theorem rep_scale {f : RSpace → ℝ} (h : represented f) (c : ℝ) :
    represented (fun x => c * f x) := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨c • g, rfl⟩

private theorem datum_represented (hpsi : represented psi) (c : ℝ) (i : Fin 3) :
    represented (fun x => datum c x i) := by
  change represented (fun x => c * profile x i)
  apply rep_scale
  unfold profile
  apply rep_sub
  · by_cases hi : i = 0
    · simp only [if_pos hi]
      exact rep_add (rep_add (rep_partial (rep_partial hpsi 0) 0)
        (rep_partial (rep_partial hpsi 1) 1)) (rep_partial (rep_partial hpsi 2) 2)
    · simp only [if_neg hi]
      exact ⟨0, rfl⟩
  · exact rep_partial (rep_partial hpsi 0) i

private def coordsRepresented (v : RInitial) : Prop :=
  ∀ i : Fin 3, represented (fun x => v x i)

private theorem rep_repDx (v : RInitial) (hv : coordsRepresented v) (j : Fin 3) (n : ℕ) :
    coordsRepresented (repeatOp (vectorDx realAnalysis j) n v) := by
  induction n with
  | zero => exact hv
  | succ n ih => exact fun i => rep_partial (ih i) j

private theorem jet_represented (v : RInitial) (hv : coordsRepresented v) (α : MultiIndex) :
    coordsRepresented (spatialJet realAnalysis α v) :=
  rep_repDx _ (rep_repDx _ (rep_repDx v hv 2 (α 2)) 1 (α 1)) 0 (α 0)

private theorem euclidean_le_sum (x : RSpace) :
    euclideanNorm3 x ≤ |x 0| + |x 1| + |x 2| := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · unfold normSq3
    nlinarith [sq_abs (x 0), sq_abs (x 1), sq_abs (x 2),
      mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1)),
      mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 2)),
      mul_nonneg (abs_nonneg (x 1)) (abs_nonneg (x 2))]

private theorem euclidean_le_pi (x : RSpace) : euclideanNorm3 x ≤ 3 * ‖x‖ := by
  have h (i : Fin 3) : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  linarith [euclidean_le_sum x, h 0, h 1, h 2]

private theorem scalar_weighted {f : RSpace → ℝ} (h : represented f) (K : ℕ) :
    ∃ C : ℝ, ∀ x : RSpace, |f x| * (1 + ‖x‖) ^ K ≤ C := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨2 ^ K * (Finset.Iic (K, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g,
    fun x => ?_⟩
  calc
    _ = (1 + ‖x‖) ^ K * ‖g x‖ := by rw [Real.norm_eq_abs, mul_comm]
    _ ≤ _ := by
      simpa only [norm_iteratedFDeriv_zero] using
        (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (K, 0)) (n := 0)
          (k := K) le_rfl le_rfl g x)

private theorem scalarPow_real (a : ℝ) (n : ℕ) : scalarPow realAnalysis a n = a ^ n := by
  induction n with
  | zero => simp [scalarPow, realAnalysis]
  | succ n ih =>
    change a * scalarPow realAnalysis a n = a ^ (n + 1)
    rw [ih, pow_succ]; ring

/-- Coordinatewise Schwartz representations imply the exact project clause (04),
including the Euclidean weight and the fixed order of spatial derivatives. -/
private theorem decay_of_represented (v : RInitial) (hv : coordsRepresented v) :
    clause04 realAnalysis v := by
  intro α K
  let j := spatialJet realAnalysis α v
  have h (i : Fin 3) := scalar_weighted (jet_represented v hv α i) K
  obtain ⟨C₀, h₀⟩ := h 0
  obtain ⟨C₁, h₁⟩ := h 1
  obtain ⟨C₂, h₂⟩ := h 2
  let C := (3 : ℝ)^K * (C₀ + C₁ + C₂)
  refine ⟨max C 1, ?_, fun x => ?_⟩
  · change 0 < max C 1
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · change euclideanNorm3 (j x) * scalarPow realAnalysis (1 + euclideanNorm3 x) K ≤ max C 1
    rw [scalarPow_real]
    refine le_trans ?_ (le_max_left C 1)
    have hw : (1 + euclideanNorm3 x)^K ≤ (3 * (1 + ‖x‖))^K := by
      exact pow_le_pow_left₀ (by unfold euclideanNorm3; positivity)
        (by linarith [euclidean_le_pi x]) K
    calc
      _ ≤ (|j x 0| + |j x 1| + |j x 2|) * (3 * (1 + ‖x‖)) ^ K :=
        mul_le_mul (euclidean_le_sum _) hw (by unfold euclideanNorm3; positivity) (by positivity)
      _ = 3 ^ K * (|j x 0| * (1 + ‖x‖)^K + |j x 1| * (1 + ‖x‖)^K +
          |j x 2| * (1 + ‖x‖)^K) := by rw [mul_pow]; ring
      _ ≤ C := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (add_le_add (h₀ x) (h₁ x)) (h₂ x)

theorem datum_decay_of_radial_extension (h : RadialSchwartzExtension) (c : ℝ) :
    clause04 realAnalysis (datum c) :=
  decay_of_represented (datum c) (datum_represented (psi_represented h) c)

theorem datum_decay (c : ℝ) : clause04 realAnalysis (datum c) :=
  datum_decay_of_radial_extension CondGaussian.exists_scalar_extension c

theorem datum_admissible (c : ℝ) : admissibleInitial realAnalysis .wholeSpace (datum c) :=
  datum_admissible_of_decay c (datum_decay c)

end

end CondFeffA

#print axioms CondFeffA.datum_decay
#print axioms CondFeffA.datum_admissible
