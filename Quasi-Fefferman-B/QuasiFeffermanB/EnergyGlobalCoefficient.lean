import QuasiFeffermanB.EnergyGalerkinCompactness
import SingularClosure.CountableCompactExtraction

/-! A single Galerkin subsequence on all integer horizons, using only initial
energy. The limit coefficient curves are compatible on overlaps. -/
set_option autoImplicit false
set_option Elab.async true
open Set Filter MeasureTheory
open scoped Topology Interval BoundedContinuousFunction
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

abbrev EnergyTimeHorizon (m : ℕ) := Icc (0 : ℝ) ((m : ℝ) + 1)
local instance energyTimeHorizonCompact (m : ℕ) : CompactSpace (EnergyTimeHorizon m) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

def energyCoefficientCurve {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (m : ℕ) (ki : FourierIndex) :
    C(EnergyTimeHorizon m, ℂ) :=
  ⟨fun t => g.coeff t.val ki.1 ki.2,
    (g.coefficient_continuous ki.1 ki.2).comp_continuous
      continuous_subtype_val (fun t => t.property.1)⟩

theorem energy_coefficient_curve_precompact
    (ν : ℝ) (hν : 0 ≤ ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (R : ℝ) (hR : 0 ≤ R)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2)
    (m : ℕ) (ki : FourierIndex) :
    IsCompact (closure (range (fun n =>
      BoundedContinuousFunction.mkOfCompact (energyCoefficientCurve (g n) m ki)))) := by
  apply critical_complex_curve_precompact ((m : ℝ) + 1)
    (fun n => BoundedContinuousFunction.mkOfCompact (energyCoefficientCurve (g n) m ki))
    (‖torusSobolevH0Coeff ki.1 ki.2‖ * R)
    (((m : ℝ) + 1) * energyModeRhsBound ν R ki.1 ki.2 ^ 2)
  · positivity
  · intro n t
    have hs := galerkin_H0_energy_bound hν (g n) R hR (hinit n) t.val t.property.1
    have hc := (torusSobolevH0Coeff ki.1 ki.2).le_opNorm ((g n).sobolevState 0 t.val)
    rw [torusSobolevH0Coeff_apply, (g n).sobolevState_coeff 0 t.property.1] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left hs
      (ContinuousLinearMap.opNorm_nonneg (torusSobolevH0Coeff ki.1 ki.2)))
  · intro n s t
    change ‖(g n).coeff t.val ki.1 ki.2 - (g n).coeff s.val ki.1 ki.2‖ ^ 2 ≤ _
    rcases le_total s.val t.val with hst | hts
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using
        galerkin_energy_coefficient_modulus hν (g n) R ((m : ℝ) + 1) hR
          (by positivity) (hinit n) ki.1 ki.2 s.property.1 hst t.property.2
    · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr hts), neg_sub]
      exact galerkin_energy_coefficient_modulus hν (g n) R ((m : ℝ) + 1) hR
        (by positivity) (hinit n) ki.1 ki.2 t.property.1 hts s.property.2

theorem ENERGY_GALERKIN_GLOBAL_COEFFICIENT_SUBSEQUENCE
    (ν : ℝ) (hν : 0 ≤ ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (R : ℝ) (hR : 0 ≤ R)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2) :
    ∃ u : ∀ m : ℕ, FourierIndex → C(EnergyTimeHorizon m, ℂ),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ m ki, TendstoUniformly
        (fun n (t : EnergyTimeHorizon m) => (g (φ n)).coeff t.val ki.1 ki.2)
        (u m ki) atTop) ∧
      (∀ (m l : ℕ) (ki : FourierIndex) (t : ℝ)
        (hm : t ∈ EnergyTimeHorizon m) (hl : t ∈ EnergyTimeHorizon l),
        u m ki ⟨t, hm⟩ = u l ki ⟨t, hl⟩) := by
  let E : ℕ × FourierIndex → Type := fun q => EnergyTimeHorizon q.1 →ᵇ ℂ
  let F : ∀ q, ℕ → E q := fun q n =>
    BoundedContinuousFunction.mkOfCompact (energyCoefficientCurve (g n) q.1 q.2)
  have hcompact (q : ℕ × FourierIndex) : IsCompact (closure (range (F q))) :=
    energy_coefficient_curve_precompact ν hν a N g R hR hinit q.1 q.2
  obtain ⟨v, φ, hφ, hv⟩ := countable_precompact_family_subsequence F hcompact
  let u : ∀ m : ℕ, FourierIndex → C(EnergyTimeHorizon m, ℂ) :=
    fun m ki => (v (m, ki)).toContinuousMap
  have hu (m : ℕ) (ki : FourierIndex) : TendstoUniformly
      (fun n (t : EnergyTimeHorizon m) => (g (φ n)).coeff t.val ki.1 ki.2)
      (u m ki) atTop := by
    change TendstoUniformly (fun n t => F (m, ki) (φ n) t) (fun t => v (m, ki) t) atTop
    exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hv (m, ki))
  refine ⟨u, φ, hφ, hu, ?_⟩
  intro m l ki t hm hl
  exact tendsto_nhds_unique ((hu m ki).tendsto_at ⟨t, hm⟩)
    ((hu l ki).tendsto_at ⟨t, hl⟩)

def globalEnergyCoefficient
    (u : ∀ m : ℕ, FourierIndex → C(EnergyTimeHorizon m, ℂ))
    (t : ℝ) : FourierCoeff :=
  if ht : 0 ≤ t then
    fun k i => u (Nat.ceil t) (k, i) ⟨t, ht, (Nat.le_ceil t).trans (by linarith)⟩
  else 0

theorem globalEnergyCoefficient_eq_horizon
    (u : ∀ m : ℕ, FourierIndex → C(EnergyTimeHorizon m, ℂ))
    (hoverlap : ∀ (m l : ℕ) (ki : FourierIndex) (t : ℝ)
      (hm : t ∈ EnergyTimeHorizon m) (hl : t ∈ EnergyTimeHorizon l),
      u m ki ⟨t, hm⟩ = u l ki ⟨t, hl⟩)
    (m : ℕ) (t : ℝ) (ht : t ∈ EnergyTimeHorizon m) (k : Frequency) (i : Fin 3) :
    globalEnergyCoefficient u t k i = u m (k, i) ⟨t, ht⟩ := by
  simp only [globalEnergyCoefficient, dif_pos ht.1]
  exact hoverlap (Nat.ceil t) m (k, i) t _ ht

theorem globalEnergyCoefficient_continuousOn
    (u : ∀ m : ℕ, FourierIndex → C(EnergyTimeHorizon m, ℂ))
    (hoverlap : ∀ (m l : ℕ) (ki : FourierIndex) (t : ℝ)
      (hm : t ∈ EnergyTimeHorizon m) (hl : t ∈ EnergyTimeHorizon l),
      u m ki ⟨t, hm⟩ = u l ki ⟨t, hl⟩)
    (k : Frequency) (i : Fin 3) :
    ContinuousOn (fun t => globalEnergyCoefficient u t k i) (Ici 0) := by
  have hinterval (m : ℕ) : ContinuousOn (fun t => globalEnergyCoefficient u t k i)
      (EnergyTimeHorizon m) := by
    apply continuousOn_iff_continuous_restrict.mpr
    change Continuous (fun t : EnergyTimeHorizon m => globalEnergyCoefficient u t.val k i)
    have heq : (fun t : EnergyTimeHorizon m => globalEnergyCoefficient u t.val k i) =
        (u m (k, i) : EnergyTimeHorizon m → ℂ) := by
      funext t
      exact globalEnergyCoefficient_eq_horizon u hoverlap m t.val t.property k i
    rw [heq]
    exact (u m (k, i)).continuous
  intro t ht
  have htlt : t < (Nat.ceil t : ℝ) + 1 := by
    have hceil := Nat.le_ceil t
    linarith
  have hc := hinterval (Nat.ceil t) t ⟨ht, htlt.le⟩
  apply hc.mono_of_mem_nhdsWithin
  apply mem_of_superset
    (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htlt)))
  intro s hs
  exact ⟨hs.1, hs.2.le⟩

theorem globalEnergyCoefficient_uniform_limit
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (u : ∀ m : ℕ, FourierIndex → C(EnergyTimeHorizon m, ℂ))
    (φ : ℕ → ℕ)
    (hconv : ∀ m ki, TendstoUniformly
      (fun n (t : EnergyTimeHorizon m) => (g (φ n)).coeff t.val ki.1 ki.2)
      (u m ki) atTop)
    (hoverlap : ∀ (m l : ℕ) (ki : FourierIndex) (t : ℝ)
      (hm : t ∈ EnergyTimeHorizon m) (hl : t ∈ EnergyTimeHorizon l),
      u m ki ⟨t, hm⟩ = u l ki ⟨t, hl⟩)
    (T : ℝ) (k : Frequency) (i : Fin 3) :
    TendstoUniformlyOn (fun n t => (g (φ n)).coeff t k i)
      (fun t => globalEnergyCoefficient u t k i) atTop (Icc (0 : ℝ) T) := by
  have hT : T ≤ (Nat.ceil T : ℝ) + 1 := (Nat.le_ceil T).trans (by linarith)
  let e : Icc (0 : ℝ) T → EnergyTimeHorizon (Nat.ceil T) :=
    fun t => ⟨t.val, t.property.1, t.property.2.trans hT⟩
  have h := (hconv (Nat.ceil T) (k, i)).comp e
  have heq : (fun t : Icc (0 : ℝ) T => u (Nat.ceil T) (k, i) (e t)) =
      (fun t => globalEnergyCoefficient u t.val k i) := by
    funext t
    exact (globalEnergyCoefficient_eq_horizon u hoverlap (Nat.ceil T) t.val
      ⟨t.property.1, t.property.2.trans hT⟩ k i).symm
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  have h' : TendstoUniformly
      (fun n (t : Icc (0 : ℝ) T) => (g (φ n)).coeff t.val k i)
      (fun t => u (Nat.ceil T) (k, i) (e t)) atTop := by
    simpa only [Function.comp_def, e] using h
  rw [heq] at h'
  exact h'

end
end QuasiFeffermanB

