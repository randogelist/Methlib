import SingularClosure.SobolevArzelaAscoli

/-!
# Fourier constraints of actual H0 limits

Coefficient evaluation is a continuous linear map on the actual H0 space.
Reality, solenoidality and the zero mode therefore pass to H0 limits. Applied
to the canonical Galerkin subsequence, all three constraints are obtained
without additional invariant or convergence certificates.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology BigOperators

namespace SingularClosure

noncomputable section

def torusSobolevH0Coeff (k : Frequency) (i : Fin 3) : TorusSobolev 0 →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : FourierIndex => ℂ) 2 (k, i)).comp
    (torusSobolevRepr 0).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem torusSobolevH0Coeff_apply (k : Frequency) (i : Fin 3) (c : TorusSobolev 0) :
    torusSobolevH0Coeff k i c = c.val k i := by
  simp [torusSobolevH0Coeff, lp.evalCLM, lp.evalₗ]

theorem torusSobolevH0Coeff_continuous (k : Frequency) (i : Fin 3) :
    Continuous (fun c : TorusSobolev 0 => c.val k i) := by
  simpa only [torusSobolevH0Coeff_apply] using (torusSobolevH0Coeff k i).continuous

theorem torusSobolevH0_reality_of_tendsto
    {α : Type*} {l : Filter α} [l.NeBot] {v : α → TorusSobolev 0} {u : TorusSobolev 0}
    (h : Tendsto v l (𝓝 u)) (hv : ∀ᶠ n in l, SpectralReality (v n).val) :
    SpectralReality u.val := by
  intro k i
  have hc : IsClosed {c : TorusSobolev 0 | c.val (-k) i = star (c.val k i)} :=
    isClosed_eq (torusSobolevH0Coeff_continuous (-k) i)
      (torusSobolevH0Coeff_continuous k i).star
  exact hc.mem_of_tendsto h (hv.mono (fun n hn => hn k i))

theorem torusSobolevH0_solenoidal_of_tendsto
    {α : Type*} {l : Filter α} [l.NeBot] {v : α → TorusSobolev 0} {u : TorusSobolev 0}
    (h : Tendsto v l (𝓝 u)) (hv : ∀ᶠ n in l, SpectralSolenoidal (v n).val) :
    SpectralSolenoidal u.val := by
  intro k
  have hc : Continuous (fun c : TorusSobolev 0 =>
      ∑ i : Fin 3, (k i : ℂ) * c.val k i) := by
    apply continuous_finset_sum
    intro i hi
    exact continuous_const.mul (torusSobolevH0Coeff_continuous k i)
  exact (isClosed_eq hc continuous_const).mem_of_tendsto h
    (hv.mono (fun n hn => hn k))

theorem torusSobolevH0_zero_mode_of_tendsto
    {α : Type*} {l : Filter α} [l.NeBot] {v : α → TorusSobolev 0} {u : TorusSobolev 0}
    (h : Tendsto v l (𝓝 u)) (hv : ∀ᶠ n in l, ∀ i : Fin 3, (v n).val 0 i = 0) :
    ∀ i : Fin 3, u.val 0 i = 0 := by
  intro i
  exact (isClosed_eq (torusSobolevH0Coeff_continuous 0 i) continuous_const).mem_of_tendsto h
    (hv.mono (fun n hn => hn i))

theorem GalerkinSolution.sobolevState_reality
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (s : ℕ) (t : ℝ) (ht : 0 ≤ t) : SpectralReality (g.sobolevState s t).val := by
  rw [g.sobolevState_coeff s ht]
  exact g.real_symmetry t ht

theorem GalerkinSolution.sobolevState_solenoidal
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (s : ℕ) (t : ℝ) (ht : 0 ≤ t) : SpectralSolenoidal (g.sobolevState s t).val := by
  rw [g.sobolevState_coeff s ht]
  exact g.solenoidal t ht

theorem GalerkinSolution.sobolevState_zero_mode
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (s : ℕ) (t : ℝ) (ht : 0 ≤ t) (i : Fin 3) : (g.sobolevState s t).val 0 i = 0 := by
  rw [g.sobolevState_coeff s ht]
  exact g.mode_support t ht 0 (cutoffModes_zero_not_mem N) i

/-- The actual uniformly convergent subsequence retains every Fourier state constraint. -/
theorem AX6_CANONICAL_GALERKIN_H0_CONSTRAINED_SUBSEQUENCE (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ u : C(Icc (0 : ℝ) T, TorusSobolev 0), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformly
        (fun n (t : Icc (0 : ℝ) T) =>
          (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t.val)
        u atTop ∧
      ∀ t : Icc (0 : ℝ) T,
        SpectralReality (u t).val ∧ SpectralSolenoidal (u t).val ∧
          ∀ i : Fin 3, (u t).val 0 i = 0 := by
  obtain ⟨u, φ, hφ, hconv⟩ :=
    AX6_CANONICAL_GALERKIN_H0_UNIFORM_SUBSEQUENCE hAX6 ν hν a ha T hT
  refine ⟨u, φ, hφ, hconv, ?_⟩
  intro t
  have ht := hconv.tendsto_at t
  refine ⟨torusSobolevH0_reality_of_tendsto ht ?_,
    torusSobolevH0_solenoidal_of_tendsto ht ?_,
    torusSobolevH0_zero_mode_of_tendsto ht ?_⟩
  · exact Filter.Eventually.of_forall fun n =>
      (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState_reality 0 t.val t.property.1
  · exact Filter.Eventually.of_forall fun n =>
      (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState_solenoidal 0 t.val t.property.1
  · exact Filter.Eventually.of_forall fun n =>
      (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState_zero_mode 0 t.val t.property.1

end

end SingularClosure
