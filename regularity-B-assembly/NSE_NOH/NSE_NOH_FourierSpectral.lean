import NSE_NOH_L2Closure
import NSE_NOH_Modes
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# NSE_NOH FIX20 — Actual torus Fourier modes and spectral L² factorization

The complex Fourier monomials on the actual normalized T³ are constant
in the first coordinate exactly when their first frequency vanishes.
The mode (0,k₂,k₃) is the pullback of the two-dimensional monomial.

The corresponding complex L² pullback is a linear isometry with closed
range. Mathlib's genuine L² Fourier-series convergence implies that
vanishing of all first-nonzero Fourier coefficients suffices for an
exact planar L² preimage. This is a substantive spectral factorization;
it does not silently identify the condition with an assumed preimage.

Still OPEN: derive the spectral vanishing condition from the original
WeakX1Invariant distributional test, transfer it to the three real-valued
vector components, establish the planar divergence-free property, and
construct the global planar and passive-scalar evolutions.

No local Lean execution. Native Windows Lean 4.33.0 cached Mathlib and
external theorem-level dependency inspection required.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open MeasureTheory Filter
open scoped ENNReal Topology

namespace NSE_NOH
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-! Actual Fourier product formula under the geometric 2D3C embedding. -/
theorem mFourier_modeEmbedding2 (k : Fin 2 → ℤ) (x : Torus 3) :
    UnitAddTorus.mFourier (modeEmbedding2 k) x =
      UnitAddTorus.mFourier k (torusProjection2 x) := by
  change
      (∏ i : Fin 3, fourier (modeEmbedding2 k i) (x i)) =
        (∏ j : Fin 2, fourier (k j) (torusProjection2 x j))
  simp only [Fin.prod_univ_three, Fin.prod_univ_two]
  change
      fourier 0 (x 0) * fourier (k 0) (x 1) * fourier (k 1) (x 2) =
      fourier (k 0) (x 1) * fourier (k 1) (x 2)
  simp

/-! Factorization for arbitrary supported three-dimensional monomials. -/
theorem mFourier_zeroFirst (k : Fin 3 → ℤ) (hk : k 0 = 0)
    (x : Torus 3) :
    UnitAddTorus.mFourier k x =
      UnitAddTorus.mFourier (modeProjection2 k) (torusProjection2 x) := by
  calc
    UnitAddTorus.mFourier k x =
        UnitAddTorus.mFourier (modeEmbedding2 (modeProjection2 k)) x := by
          rw [modeEmbedding2_modeProjection2 k hk]
    _ = UnitAddTorus.mFourier (modeProjection2 k) (torusProjection2 x) :=
      mFourier_modeEmbedding2 (modeProjection2 k) x

/-! Finite complex trigonometric polynomials with planar frequency support
factor exactly through the physical torus projection. -/
def finiteFourier3 (s : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → ℂ) (x : Torus 3) : ℂ :=
  ∑ k ∈ s, c k * UnitAddTorus.mFourier k x

theorem finiteFourier3_zeroFirst_factorization
    (s : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ)
    (hs : ∀ k ∈ s, k 0 = 0) (x : Torus 3) :
    finiteFourier3 s c x =
      ∑ k ∈ s, c k *
        UnitAddTorus.mFourier (modeProjection2 k) (torusProjection2 x) := by
  unfold finiteFourier3
  apply Finset.sum_congr rfl
  intro k hk
  rw [mFourier_zeroFirst k (hs k hk) x]

/-! Every such polynomial is constant along first-coordinate fibers. -/
theorem torusProjection2_update_first
    (x : Torus 3) (z : UnitAddCircle) :
    torusProjection2 (Function.update x (0 : Fin 3) z) = torusProjection2 x := by
  funext i
  fin_cases i <;> simp [torusProjection2, Function.update]

theorem finiteFourier3_zeroFirst_invariant
    (s : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ)
    (hs : ∀ k ∈ s, k 0 = 0) (x : Torus 3) (z : UnitAddCircle) :
    finiteFourier3 s c (Function.update x (0 : Fin 3) z) =
      finiteFourier3 s c x := by
  rw [finiteFourier3_zeroFirst_factorization s c hs]
  rw [finiteFourier3_zeroFirst_factorization s c hs]
  rw [torusProjection2_update_first]

/-! Complex L² is the correct Hilbert space for Mathlib's Fourier basis.
The real component projection is an additional independent endpoint. -/
abbrev ComplexL2Two := Lp ℂ (2 : ℝ≥0∞) (volume : Measure (Torus 2))
abbrev ComplexL2Three := Lp ℂ (2 : ℝ≥0∞) (volume : Measure (Torus 3))

def complexL2Pullback : ComplexL2Two →ₗᵢ[ℂ] ComplexL2Three :=
  Lp.compMeasurePreservingₗᵢ ℂ torusProjection2
    torusProjection2_measurePreserving

theorem complexL2Pullback_closedRange :
    IsClosed (Set.range complexL2Pullback) := by
  exact complexL2Pullback.isometry.isClosedEmbedding.isClosed_range

/-! The actual Fourier L² monomial (0,k) equals the pullback of the
planar L² monomial, as an almost-everywhere equivalence class. -/
theorem complexL2Pullback_fourierMode (k : Fin 2 → ℤ) :
    complexL2Pullback (UnitAddTorus.mFourierLp (d := Fin 2) 2 k) =
      UnitAddTorus.mFourierLp (d := Fin 3) 2 (modeEmbedding2 k) := by
  apply Lp.ext_iff.mpr
  have ha :
      ((complexL2Pullback (UnitAddTorus.mFourierLp (d := Fin 2) 2 k) :
          ComplexL2Three) : Torus 3 → ℂ) =ᵐ[volume]
        (fun x : Torus 3 =>
          (UnitAddTorus.mFourierLp (d := Fin 2) 2 k) (torusProjection2 x)) := by
    exact Lp.coeFn_compMeasurePreserving
      (UnitAddTorus.mFourierLp (d := Fin 2) 2 k)
      torusProjection2_measurePreserving
  have hb :
      (fun x : Torus 3 =>
        (UnitAddTorus.mFourierLp (d := Fin 2) 2 k) (torusProjection2 x)) =ᵐ[volume]
      (fun x : Torus 3 => UnitAddTorus.mFourier k (torusProjection2 x)) := by
    exact torusProjection2_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (UnitAddTorus.coeFn_mFourierLp (d := Fin 2) 2 k)
  have hc :
      ((UnitAddTorus.mFourierLp (d := Fin 3) 2 (modeEmbedding2 k) :
          ComplexL2Three) : Torus 3 → ℂ) =ᵐ[volume]
        UnitAddTorus.mFourier (modeEmbedding2 k) := by
    exact UnitAddTorus.coeFn_mFourierLp (d := Fin 3) 2 (modeEmbedding2 k)
  filter_upwards [ha, hb, hc] with x hax hbx hcx
  calc
    complexL2Pullback (UnitAddTorus.mFourierLp (d := Fin 2) 2 k) x =
        (UnitAddTorus.mFourierLp (d := Fin 2) 2 k) (torusProjection2 x) := hax
    _ = UnitAddTorus.mFourier k (torusProjection2 x) := hbx
    _ = UnitAddTorus.mFourier (modeEmbedding2 k) x :=
      (mFourier_modeEmbedding2 k x).symm
    _ = UnitAddTorus.mFourierLp (d := Fin 3) 2 (modeEmbedding2 k) x := hcx.symm

/-! The actual spectral closure theorem: zero nonplanar Fourier modes
suffice for an exact planar L² factorization. -/
theorem complexL2_zeroFirstSpectral_factorization
    (a : ComplexL2Three)
    (hzero : ∀ k : Fin 3 → ℤ, k 0 ≠ 0 →
      UnitAddTorus.mFourierCoeff a k = 0) :
    ∃ w : ComplexL2Two, complexL2Pullback w = a := by
  have hterm (k : Fin 3 → ℤ) :
      (UnitAddTorus.mFourierCoeff a k) •
        (UnitAddTorus.mFourierLp (d := Fin 3) 2 k) ∈
          Set.range complexL2Pullback := by
    by_cases hk : k 0 = 0
    · refine ⟨(UnitAddTorus.mFourierCoeff a k) •
          (UnitAddTorus.mFourierLp (d := Fin 2) 2 (modeProjection2 k)), ?_⟩
      simp only [map_smul, complexL2Pullback_fourierMode,
        modeEmbedding2_modeProjection2 k hk]
    · refine ⟨0, ?_⟩
      simp [hzero k hk]
  have hpartial (s : Finset (Fin 3 → ℤ)) :
      (∑ k ∈ s, (UnitAddTorus.mFourierCoeff a k) •
        (UnitAddTorus.mFourierLp (d := Fin 3) 2 k)) ∈
        Set.range complexL2Pullback := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert k s hk ih =>
      rcases hterm k with ⟨u, hu⟩
      rcases ih with ⟨v, hv⟩
      refine ⟨u + v, ?_⟩
      simp only [Finset.sum_insert hk, map_add, hu, hv]
  have hsum :
      Tendsto (fun s : Finset (Fin 3 → ℤ) =>
        ∑ k ∈ s, (UnitAddTorus.mFourierCoeff a k) •
          (UnitAddTorus.mFourierLp (d := Fin 3) 2 k))
        atTop (𝓝 a) := by
    exact UnitAddTorus.hasSum_mFourier_series_L2 a
  have ha : a ∈ Set.range complexL2Pullback :=
    complexL2Pullback_closedRange.mem_of_tendsto hsum
      (Filter.Eventually.of_forall hpartial)
  exact ha

end
end NSE_NOH

#check NSE_NOH.complexL2Pullback
#print axioms NSE_NOH.mFourier_modeEmbedding2
#print axioms NSE_NOH.mFourier_zeroFirst
#print axioms NSE_NOH.finiteFourier3_zeroFirst_factorization
#print axioms NSE_NOH.torusProjection2_update_first
#print axioms NSE_NOH.finiteFourier3_zeroFirst_invariant
#print axioms NSE_NOH.complexL2Pullback_closedRange
#print axioms NSE_NOH.complexL2Pullback_fourierMode
#print axioms NSE_NOH.complexL2_zeroFirstSpectral_factorization
