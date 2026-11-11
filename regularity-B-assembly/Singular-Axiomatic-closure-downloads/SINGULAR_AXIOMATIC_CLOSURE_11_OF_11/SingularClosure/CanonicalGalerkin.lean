import SingularClosure.GalerkinGlobal
import SingularClosure.Admission

/-! Canonical actual Galerkin trajectories and nonvacuous AX6 equivalence. -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace SingularClosure

noncomputable section

def canonicalGalerkinSolution (ν : ℝ) (hν : 0 < ν) (a : Field)
    (ha : SmoothSigmaZero a) (N : ℕ) : GalerkinSolution ν a N :=
  (GALERKIN_GLOBAL_EXISTS_UNIQUE ν hν a ha N).choose

theorem canonicalGalerkinSolution_unique (ν : ℝ) (hν : 0 < ν) (a : Field)
    (ha : SmoothSigmaZero a) (N : ℕ) (g : GalerkinSolution ν a N) :
    EqOn (canonicalGalerkinSolution ν hν a ha N).coeff g.coeff (Ici 0) :=
  (GALERKIN_GLOBAL_EXISTS_UNIQUE ν hν a ha N).choose_spec g

theorem budget6_eq_of_coeff_eqOn {N : ℕ} {c d : ℝ → FourierCoeff}
    (h : EqOn c d (Ici 0)) (T : ℝ) : budget6 N c T = budget6 N d T := by
  unfold budget6
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [h ht.1]

def CanonicalAX6Statement : Prop :=
  ∀ (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a),
    ∀ T : ℝ, 0 < T → ∃ M : ℝ≥0, ∀ N : ℕ, 1 ≤ N →
      budget6 N (canonicalGalerkinSolution ν hν a ha N).coeff T ≤ (M : ℝ≥0∞)

theorem AX6_IFF_CANONICAL_GALERKIN_BUDGET :
    AX6Statement ↔ CanonicalAX6Statement := by
  constructor
  · intro h ν hν a ha T hT
    obtain ⟨M, hM⟩ := h ν hν a ha T hT
    exact ⟨M, fun N hN => hM N hN (canonicalGalerkinSolution ν hν a ha N)⟩
  · intro h ν hν a ha T hT
    obtain ⟨M, hM⟩ := h ν hν a ha T hT
    refine ⟨M, ?_⟩
    intro N hN g
    rw [← budget6_eq_of_coeff_eqOn
      (canonicalGalerkinSolution_unique ν hν a ha N g) T]
    exact hM N hN

end

end SingularClosure
