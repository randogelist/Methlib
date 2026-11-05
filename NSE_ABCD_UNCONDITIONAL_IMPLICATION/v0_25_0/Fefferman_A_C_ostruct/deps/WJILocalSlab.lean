import CondRaw
import COND_FEFF_A_OBSTRUCT
import Mathlib.Analysis.Distribution.Sobolev

namespace CondFeffA.WJISlab
open Fefferman Fefferman.ConcreteReal MeasureTheory Set
open scoped ContDiff ENNReal
noncomputable section

/-- Existence of a bundled Schwartz function with precisely the stated pointwise values. -/
def SchwartzRepresentative (f : RSpace → ℝ) : Prop :=
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

private theorem psi_represented (h : RadialSchwartzExtension) : SchwartzRepresentative psi := by
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

private theorem rep_partial {f : RSpace → ℝ} (h : SchwartzRepresentative f) (i : Fin 3) :
    SchwartzRepresentative (spatialDerivative i f) := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨SchwartzMap.evalCLM ℝ RSpace ℝ (basisDirection i)
    (SchwartzMap.fderivCLM ℝ RSpace ℝ g), rfl⟩

private theorem rep_add {f g : RSpace → ℝ} (hf : SchwartzRepresentative f) (hg : SchwartzRepresentative g) :
    SchwartzRepresentative (fun x => f x + g x) := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  exact ⟨a + b, rfl⟩

private theorem rep_sub {f g : RSpace → ℝ} (hf : SchwartzRepresentative f) (hg : SchwartzRepresentative g) :
    SchwartzRepresentative (fun x => f x - g x) := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  exact ⟨a - b, rfl⟩

private theorem rep_scale {f : RSpace → ℝ} (h : SchwartzRepresentative f) (c : ℝ) :
    SchwartzRepresentative (fun x => c * f x) := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨c • g, rfl⟩

private theorem datum_represented (hpsi : SchwartzRepresentative psi) (c : ℝ) (i : Fin 3) :
    SchwartzRepresentative (fun x => datum c x i) := by
  change SchwartzRepresentative (fun x => c * profile x i)
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
  ∀ i : Fin 3, SchwartzRepresentative (fun x => v x i)

private theorem rep_repDx (v : RInitial) (hv : coordsRepresented v) (j : Fin 3) (n : ℕ) :
    coordsRepresented (repeatOp (vectorDx realAnalysis j) n v) := by
  induction n with
  | zero => exact hv
  | succ n ih => exact fun i => rep_partial (ih i) j

private theorem jet_represented (v : RInitial) (hv : coordsRepresented v) (α : MultiIndex) :
    coordsRepresented (spatialJet realAnalysis α v) :=
  rep_repDx _ (rep_repDx _ (rep_repDx v hv 2 (α 2)) 1 (α 1)) 0 (α 0)

/-- Exposes the Schwartz representation of the explicit initial field, component by component. -/
theorem datum_schwartz (c : ℝ) (i : Fin 3) :
    SchwartzRepresentative (fun x => datum c x i) :=
  datum_represented (psi_represented CondGaussian.exists_scalar_extension) c i

/-- All mixed spatial derivatives of the initial velocity have Schwartz representatives. -/
theorem datumJet_schwartz (c : ℝ) (α : MultiIndex) (i : Fin 3) :
    SchwartzRepresentative (fun x => spatialJet realAnalysis α (datum c) x i) :=
  jet_represented (datum c) (datum_schwartz c) α i

theorem datumJet_memLp (c : ℝ) (α : MultiIndex) (i : Fin 3) (p : ℝ≥0∞) :
    MemLp (fun x => spatialJet realAnalysis α (datum c) x i) p volume := by
  obtain ⟨g, hg⟩ := datumJet_schwartz c α i
  rw [← hg]
  exact g.memLp p volume

/-- The Euclidean realization is used for Mathlib's Fourier Sobolev spaces.
The pointwise identity fixes the representative through the coordinate change. -/
theorem datum_memSobolev (c : ℝ) (i : Fin 3) :
    ∃ g : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ,
      (∀ x, g x = (datum c (EuclideanSpace.equiv (Fin 3) ℝ x) i : ℂ)) ∧
      ∀ r : ℝ, TemperedDistribution.MemSobolev r 2
        (g : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) := by
  obtain ⟨f, hf⟩ := datum_schwartz c i
  let G := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (EuclideanSpace.equiv (Fin 3) ℝ) f
  refine ⟨G.postcompCLM Complex.ofRealCLM, ?_, fun r => ?_⟩
  · intro x
    exact congrArg Complex.ofReal (congrFun hf (EuclideanSpace.equiv (Fin 3) ℝ x))
  · exact (G.postcompCLM Complex.ofRealCLM).memSobolev

/-- The right derivative, including the initial face, has the physical diffusion,
transport and pressure terms of the unforced momentum equation. -/
theorem witness_right_momentum {c : ℝ} {s : Solution realAnalysis} (hs : WitnessAt c s)
    (x : RSpace) (i : Fin 3) (t : ℝ) (ht : 0 ≤ t) :
    derivWithin (fun r => s.velocity x r i) (Ici 0) t = rawRHS s x i t := by
  rcases eq_or_lt_of_le ht with he | hp
  · subst t
    simpa only [timeJetField, rightJet, Nat.zero_add, iteratedDerivWithin_one,
      iteratedDerivWithin_zero] using raw_time_jet hs 0 x i
  · rw [derivWithin_of_mem_nhds (Ici_mem_nhds hp)]
    have hm := hs.1 x t ht i
    change deriv (fun r => s.velocity x r i) t +
      transport (fun y => s.velocity y t) (fun y => s.velocity y t) x i =
      1 * heatStep (fun y => s.velocity y t) x i +
        (-spatialDerivative i (fun y => s.pressure y t) x) + 0 at hm
    unfold rawRHS
    linarith only [hm]

/-- Concrete restricted-witness hypotheses for the smooth finite-energy
whole-space PDE. The pressure appearing here is the original witness pressure. -/
structure SmoothFiniteEnergySlab (c T : ℝ) (s : Solution realAnalysis) : Prop where
  velocity_smooth : ∀ i : Fin 3, ContDiffOn ℝ ∞
    (fun z : RSpace × ℝ => s.velocity z.1 z.2 i) {z | z.2 ∈ Icc 0 T}
  pressure_smooth : ContDiffOn ℝ ∞
    (fun z : RSpace × ℝ => s.pressure z.1 z.2) {z | z.2 ∈ Icc 0 T}
  initial : ∀ x, s.velocity x 0 = datum c x
  divergence : ∀ x t, t ∈ Icc 0 T → fieldDiv (fun y => s.velocity y t) x = 0
  momentum : ∀ x i t, t ∈ Icc 0 T →
    derivWithin (fun r => s.velocity x r i) (Ici 0) t = rawRHS s x i t
  energy : ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T,
    squareIntegrableReal (fun y => s.velocity y t) ∧
      integralNormSqReal (fun y => s.velocity y t) < C

theorem witness_finite_slab {c : ℝ} {s : Solution realAnalysis} (hs : WitnessAt c s)
    (T : ℝ) : SmoothFiniteEnergySlab c T s := by
  have smooth : clause06 realAnalysis s := hs.2.2.2.1
  have incl : {z : RSpace × ℝ | z.2 ∈ Icc 0 T} ⊆ {z : RSpace × ℝ | 0 ≤ z.2} :=
    fun _ hz => hz.1
  obtain ⟨C, hC, henergy⟩ := hs.2.2.2.2
  refine ⟨?_, ?_, hs.2.2.1, ?_, ?_, ⟨C, hC, fun t ht => henergy t ht.1⟩⟩
  · intro i
    have h : ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => s.velocity z.1 z.2 i)
        {z : RSpace × ℝ | 0 ≤ z.2} := smooth.1 i
    exact (h.of_le le_top).mono incl
  · have h : ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => s.pressure z.1 z.2)
        {z : RSpace × ℝ | 0 ≤ z.2} := smooth.2
    exact (h.of_le le_top).mono incl
  · intro x t ht
    exact hs.2.1 x t ht.1
  · intro x i t ht
    exact witness_right_momentum hs x i t ht.1

end
end CondFeffA.WJISlab
