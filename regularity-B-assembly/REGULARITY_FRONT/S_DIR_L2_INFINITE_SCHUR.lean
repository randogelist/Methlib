import S_DIR_L2_ACTUAL_SHELLS
import S_DIR_L2_SCHUR_KERNEL

set_option autoImplicit false
set_option maxHeartbeats 0

open scoped BigOperators

noncomputable section

namespace SDirL2

/-!
# S_DIR_L2 v0.7.1 FIX1 — unconditional infinite weighted Schur quadratic form

Scope: the actual nonzero integer-direction Fourier plane, with no
unresolved shell or row premise. We prove the infinite correlation bound
for every square-summable complex profile on that plane.

The separate physical heat synthesis / Serrin realization and the
Leray–Hopf uniqueness bridge are not assertions of this module.
-/

/-- Integer Fourier frequencies in the directional plane, excluding zero. -/
abbrev ActivePlaneMode (a : Mode3) : Type :=
  {k : Mode3 // directionalDot a k = 0 ∧ k ≠ 0}

/-- Positive Euclidean radius of a nonzero planar Fourier frequency. -/
def activeRadius (a : Mode3) (k : ActivePlaneMode a) : ℝ :=
  Real.sqrt (latticeRadiusSq k.1)

theorem S_DIR_L2_ACTIVE_RADIUS_POS (a : Mode3) (k : ActivePlaneMode a) :
    0 < activeRadius a k :=
  S_DIR_L2_NONZERO_RADIUS_POS k.1 k.2.2

/-- The physical heat kernel's Schur row integrand is the proved radial term. -/
theorem S_DIR_L2_ACTIVE_HEAT_KERNEL_ROW_EQ
    (a : Mode3) (i j : ActivePlaneMode a) :
    abstractHeatKernel (activeRadius a) i j * (activeRadius a j)⁻¹ =
      directionalRadialRowTerm (activeRadius a i) j.1 := by
  have hj : activeRadius a j ≠ 0 :=
    ne_of_gt (S_DIR_L2_ACTIVE_RADIUS_POS a j)
  have hs : activeRadius a i ^ 2 + activeRadius a j ^ 2 ≠ 0 := by
    have hi : 0 < activeRadius a i := S_DIR_L2_ACTIVE_RADIUS_POS a i
    have hjpos : 0 < activeRadius a j := S_DIR_L2_ACTIVE_RADIUS_POS a j
    positivity
  change (1 / (activeRadius a i ^ 2 + activeRadius a j ^ 2)) *
      (activeRadius a j)⁻¹ =
      1 / (activeRadius a j *
          (activeRadius a i ^ 2 + activeRadius a j ^ 2))
  field_simp [hj, hs] <;> ring

/-- The actual, previously proved finite plane row automatically gives
    the finite Schur row for a subset of the active-frequency subtype. -/
theorem S_DIR_L2_ACTIVE_FINITE_HEAT_ROW
    (a : Mode3) (ha : a ≠ 0)
    (F : Finset (ActivePlaneMode a)) (i : ActivePlaneMode a) :
    (∑ j ∈ F, abstractHeatKernel (activeRadius a) i j *
      (activeRadius a j)⁻¹) ≤ 64 * (activeRadius a i)⁻¹ := by
  classical
  let E : Finset Mode3 :=
    F.image (fun x : ActivePlaneMode a => x.1)
  have hplane : ∀ k ∈ E, directionalDot a k = 0 := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact x.2.1
  have hnz : ∀ k ∈ E, k ≠ 0 := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact x.2.2
  have himage :
      (∑ k ∈ E, directionalRadialRowTerm (activeRadius a i) k) =
        ∑ j ∈ F, directionalRadialRowTerm (activeRadius a i) j.1 := by
    simpa only [E] using
      (Finset.sum_image
        (s := F)
        (g := (fun x : ActivePlaneMode a => x.1))
        (f := directionalRadialRowTerm (activeRadius a i))
        (by intro x hx y hy hxy; exact Subtype.ext hxy))
  have hfinite := S_DIR_L2_ACTUAL_FINITE_PLANE_ROW a ha
    (activeRadius a i) (S_DIR_L2_ACTIVE_RADIUS_POS a i)
    E hplane hnz
  calc
    (∑ j ∈ F, abstractHeatKernel (activeRadius a) i j *
        (activeRadius a j)⁻¹)
        = ∑ j ∈ F, directionalRadialRowTerm (activeRadius a i) j.1 := by
            apply Finset.sum_congr rfl
            intro j hj
            exact S_DIR_L2_ACTIVE_HEAT_KERNEL_ROW_EQ a i j
    _ = ∑ k ∈ E, directionalRadialRowTerm (activeRadius a i) k :=
        himage.symm
    _ ≤ 64 / (activeRadius a i) := hfinite
    _ = 64 * (activeRadius a i)⁻¹ := by rw [div_eq_mul_inv]

/-- Fully unconditional finite heat-kernel Schur bound on actual plane modes.
    No row-bound premise remains. -/
theorem S_DIR_L2_ACTIVE_FINITE_HEAT_SCHUR
    (a : Mode3) (ha : a ≠ 0)
    (F : Finset (ActivePlaneMode a))
    (b : ActivePlaneMode a → ℝ) :
    (∑ i ∈ F, ∑ j ∈ F,
        abstractHeatKernel (activeRadius a) i j * b i * b j) ≤
      64 * ∑ i ∈ F, b i ^ 2 := by
  classical
  apply S_DIR_L2_FINITE_HEAT_KERNEL_SCHUR F (activeRadius a) b 64
  · intro i hi
    exact S_DIR_L2_ACTIVE_RADIUS_POS a i
  · intro i hi
    exact S_DIR_L2_ACTIVE_FINITE_HEAT_ROW a ha F i

/-- General infinite-square closure: a nonnegative double kernel with
    uniformly bounded finite square sums is summable on the product type,
    with the same bound. Only square-summability of the coefficient is needed. -/
theorem S_DIR_L2_GENERIC_INFINITE_SCHUR_FROM_FINITE_SQUARES
    {ι : Type*} [DecidableEq ι]
    (f : ι → ι → ℝ) (b : ι → ℝ) (C : ℝ)
    (hpos : ∀ i j, 0 ≤ f i j)
    (hC : 0 ≤ C)
    (hb : Summable (fun i => b i ^ 2))
    (hfinite : ∀ F : Finset ι,
      (∑ i ∈ F, ∑ j ∈ F, f i j) ≤
        C * ∑ i ∈ F, b i ^ 2) :
    Summable (fun p : ι × ι => f p.1 p.2) ∧
      (∑' p : ι × ι, f p.1 p.2) ≤ C * (∑' i : ι, b i ^ 2) := by
  classical
  have hbound (E : Finset (ι × ι)) :
      (∑ p ∈ E, f p.1 p.2) ≤ C * (∑' i : ι, b i ^ 2) := by
    let F : Finset ι := E.image Prod.fst ∪ E.image Prod.snd
    have hsub : E ⊆ F.product F := by
      intro p hp
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
    calc
      (∑ p ∈ E, f p.1 p.2)
          ≤ ∑ p ∈ F.product F, f p.1 p.2 := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub
              (by intro p hp hnot; exact hpos p.1 p.2)
      _ = ∑ i ∈ F, ∑ j ∈ F, f i j := by
        simpa only [Finset.product_eq_sprod] using
          (Finset.sum_product' F F f)
      _ ≤ C * ∑ i ∈ F, b i ^ 2 := hfinite F
      _ ≤ C * (∑' i : ι, b i ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (Summable.sum_le_tsum F
            (fun i hi => sq_nonneg (b i)) hb) hC
  exact S_DIR_L2_INFINITE_ROW_FROM_ALL_FINITE_BOUNDS
    (fun p : ι × ι => f p.1 p.2)
    (C * (∑' i : ι, b i ^ 2))
    (fun p => hpos p.1 p.2) hbound

/-- Actual infinite nonnegative coefficient Schur theorem. -/
theorem S_DIR_L2_INFINITE_NONNEG_WEIGHTED_SCHUR
    (a : Mode3) (ha : a ≠ 0)
    (b : ActivePlaneMode a → ℝ)
    (hbnonneg : ∀ k, 0 ≤ b k)
    (hbsq : Summable (fun k => b k ^ 2)) :
    Summable (fun p : ActivePlaneMode a × ActivePlaneMode a =>
      abstractHeatKernel (activeRadius a) p.1 p.2 * b p.1 * b p.2) ∧
    (∑' p : ActivePlaneMode a × ActivePlaneMode a,
      abstractHeatKernel (activeRadius a) p.1 p.2 * b p.1 * b p.2) ≤
      64 * (∑' k : ActivePlaneMode a, b k ^ 2) := by
  classical
  apply S_DIR_L2_GENERIC_INFINITE_SCHUR_FROM_FINITE_SQUARES
    (fun i j => abstractHeatKernel (activeRadius a) i j * b i * b j)
    b 64
  · intro i j
    exact mul_nonneg
      (mul_nonneg
        (S_DIR_L2_ABSTRACT_KERNEL_NONNEG
          (activeRadius a) i j
          (S_DIR_L2_ACTIVE_RADIUS_POS a i)
          (S_DIR_L2_ACTIVE_RADIUS_POS a j))
        (hbnonneg i))
      (hbnonneg j)
  · norm_num
  · exact hbsq
  · intro F
    exact S_DIR_L2_ACTIVE_FINITE_HEAT_SCHUR a ha F b

/-- Primary v0.7.0 root: infinite weighted Schur for arbitrary complex
    square-summable Fourier coefficients on a directional plane. -/
theorem S_DIR_L2_INFINITE_WEIGHTED_SCHUR
    (a : Mode3) (ha : a ≠ 0)
    (z : ActivePlaneMode a → ℂ)
    (hz : Summable (fun k => ‖z k‖ ^ 2)) :
    Summable (fun p : ActivePlaneMode a × ActivePlaneMode a =>
      abstractHeatKernel (activeRadius a) p.1 p.2 * ‖z p.1‖ * ‖z p.2‖) ∧
    (∑' p : ActivePlaneMode a × ActivePlaneMode a,
      abstractHeatKernel (activeRadius a) p.1 p.2 * ‖z p.1‖ * ‖z p.2‖) ≤
      64 * (∑' k : ActivePlaneMode a, ‖z k‖ ^ 2) := by
  exact S_DIR_L2_INFINITE_NONNEG_WEIGHTED_SCHUR
    a ha (fun k => ‖z k‖) (fun k => norm_nonneg _) hz

end SDirL2
