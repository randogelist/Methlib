import S_DIR_L2_DYADIC_ROW

set_option autoImplicit false
set_option maxHeartbeats 0

open scoped BigOperators

noncomputable section

namespace SDirL2

/-!
# S_DIR_L2 v0.6.0 — actual, unconditional directional-plane shell partition

The frequency label is the integer sup norm, not the Euclidean radius.
Its exact `Nat.log2` shell index is defined for every integer mode.
The shell counting estimate follows from the certified plane projection
and strict-cube bound, and the radial kernel is bounded from below by
that integer sup norm. No geometric shell-cover admission is required.

This module leaves physical Fourier synthesis and three-dimensional
Leray--Hopf uniqueness independent of the infinite row theorem.
-/

/-- Integer L-infinity frequency radius, valid for all three-dimensional integer modes. -/
def latticeSupNorm (k : Mode3) : ℕ :=
  max (k 0).natAbs (max (k 1).natAbs (k 2).natAbs)

/-- Every absolute integer coordinate is bounded by the frequency sup norm. -/
theorem S_DIR_L2_SUPNORM_COORD_LE (k : Mode3) (i : Fin 3) :
    (k i).natAbs ≤ latticeSupNorm k := by
  unfold latticeSupNorm
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- No nonzero integer mode has zero sup norm. -/
theorem S_DIR_L2_SUPNORM_POS (k : Mode3) (hk : k ≠ 0) :
    0 < latticeSupNorm k := by
  by_contra hn
  have hq : latticeSupNorm k = 0 := Nat.eq_zero_of_not_pos hn
  have h0 : (k 0).natAbs = 0 := by
    have h := S_DIR_L2_SUPNORM_COORD_LE k (0 : Fin 3)
    omega
  have h1 : (k 1).natAbs = 0 := by
    have h := S_DIR_L2_SUPNORM_COORD_LE k (1 : Fin 3)
    omega
  have h2 : (k 2).natAbs = 0 := by
    have h := S_DIR_L2_SUPNORM_COORD_LE k (2 : Fin 3)
    omega
  apply hk
  funext i
  fin_cases i
  · exact Int.natAbs_eq_zero.mp h0
  · exact Int.natAbs_eq_zero.mp h1
  · exact Int.natAbs_eq_zero.mp h2

/-- The exact integer dyadic shell index (including an arbitrary value at the origin). -/
def latticeShellIndex (k : Mode3) : ℕ :=
  Nat.log2 (latticeSupNorm k)

/-- At nonzero modes, the dyadic index gives an exact bracket on sup norm. -/
theorem S_DIR_L2_SUPNORM_DYADIC_BRACKET (k : Mode3) (hk : k ≠ 0) :
    (2 : ℕ) ^ latticeShellIndex k ≤ latticeSupNorm k ∧
      latticeSupNorm k < (2 : ℕ) ^ (latticeShellIndex k + 1) := by
  unfold latticeShellIndex
  exact (Nat.log2_eq_iff (ne_of_gt (S_DIR_L2_SUPNORM_POS k hk))).mp rfl

/-- Euclidean frequency radius dominates the integer sup norm. -/
theorem S_DIR_L2_SUPNORM_LE_EUCLIDEAN (k : Mode3) :
    (latticeSupNorm k : ℝ) ≤ Real.sqrt (latticeRadiusSq k) := by
  have h0sq : (k 0 : ℝ) ^ 2 ≤ latticeRadiusSq k := by
    unfold latticeRadiusSq
    nlinarith [sq_nonneg (k 1 : ℝ), sq_nonneg (k 2 : ℝ)]
  have h1sq : (k 1 : ℝ) ^ 2 ≤ latticeRadiusSq k := by
    unfold latticeRadiusSq
    nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 2 : ℝ)]
  have h2sq : (k 2 : ℝ) ^ 2 ≤ latticeRadiusSq k := by
    unfold latticeRadiusSq
    nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]
  have hcoord (z : ℤ) (hz : (z : ℝ) ^ 2 ≤ latticeRadiusSq k) :
      (z.natAbs : ℝ) ≤ Real.sqrt (latticeRadiusSq k) := by
    calc
      (z.natAbs : ℝ) = |(z : ℝ)| := by simp
      _ = Real.sqrt ((z : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (latticeRadiusSq k) := Real.sqrt_le_sqrt hz
  have h0 := hcoord (k 0) h0sq
  have h1 := hcoord (k 1) h1sq
  have h2 := hcoord (k 2) h2sq
  simpa only [latticeSupNorm, Nat.cast_max] using max_le h0 (max_le h1 h2)

/-- The exact sup-norm shell has the lower radial bound used by the Schur kernel. -/
theorem S_DIR_L2_SUPNORM_SHELL_RADIUS_LOWER (k : Mode3) (hk : k ≠ 0) :
    (2 : ℝ) ^ latticeShellIndex k ≤ Real.sqrt (latticeRadiusSq k) := by
  have hpow : (2 : ℝ) ^ latticeShellIndex k ≤ (latticeSupNorm k : ℝ) := by
    exact_mod_cast (S_DIR_L2_SUPNORM_DYADIC_BRACKET k hk).1
  exact hpow.trans (S_DIR_L2_SUPNORM_LE_EUCLIDEAN k)

/-- The upper dyadic shell bound constrains every signed integer coordinate. -/
theorem S_DIR_L2_SUPNORM_SHELL_COORD_UPPER
    (k : Mode3) (hk : k ≠ 0) (i : Fin 3) :
    -(((2 : ℕ) ^ (latticeShellIndex k + 1) : ℕ) : ℤ) < k i ∧
      k i < (((2 : ℕ) ^ (latticeShellIndex k + 1) : ℕ) : ℤ) := by
  have hsq := (S_DIR_L2_SUPNORM_DYADIC_BRACKET k hk).2
  have hcoord := S_DIR_L2_SUPNORM_COORD_LE k i
  have habs : (k i).natAbs < (2 : ℕ) ^ (latticeShellIndex k + 1) :=
    hcoord.trans_lt hsq
  have hcast : ((k i).natAbs : ℤ) <
      (((2 : ℕ) ^ (latticeShellIndex k + 1) : ℕ) : ℤ) := by
    exact_mod_cast habs
  rcases Int.natAbs_eq (k i) with h | h
  · constructor <;> omega
  · constructor <;> omega

/-- Actual shell: a finite set of precisely the frequencies with a given dyadic index. -/
def actualDyadicShell (F : Finset Mode3) (j : ℕ) : Finset Mode3 :=
  F.filter (fun k => latticeShellIndex k = j)

/-- Each finite set is the union of its actual dyadic shells; no cover premise. -/
theorem S_DIR_L2_ACTUAL_SHELL_PARTITION (F : Finset Mode3) :
    F = (Finset.range (F.sup latticeShellIndex + 1)).biUnion (actualDyadicShell F) := by
  classical
  ext k
  simp only [Finset.mem_biUnion, Finset.mem_range,
    actualDyadicShell, Finset.mem_filter]
  constructor
  · intro hk
    refine ⟨latticeShellIndex k, ?_, hk, rfl⟩
    exact Nat.lt_succ_of_le (Finset.le_sup (f := latticeShellIndex) hk)
  · rintro ⟨j, hj, hk, _⟩
    exact hk

/-- Different shell indices define disjoint subsets of each finite set. -/
theorem S_DIR_L2_ACTUAL_SHELL_DISJOINT (F : Finset Mode3) (N : ℕ) :
    (↑(Finset.range N) : Set ℕ).PairwiseDisjoint (actualDyadicShell F) := by
  classical
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro k hki hkj
  have hei : latticeShellIndex k = i := (Finset.mem_filter.mp hki).2
  have hej : latticeShellIndex k = j := (Finset.mem_filter.mp hkj).2
  exact hij (hei.symm.trans hej)

/-- Actual dyadic shells have the certified uniform rank-two cube count. -/
theorem S_DIR_L2_ACTUAL_SHELL_CARD
    (a : Mode3) (ha : a ≠ 0)
    (F : Finset Mode3)
    (hplane : ∀ k ∈ F, directionalDot a k = 0)
    (hnonzero : ∀ k ∈ F, k ≠ 0)
    (j : ℕ) :
    (actualDyadicShell F j).card ≤ 16 * ((2 : ℕ) ^ j) ^ 2 := by
  let R : ℕ := 2 ^ (j + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hp : ∀ k ∈ actualDyadicShell F j, directionalDot a k = 0 := by
    intro k hk
    exact hplane k (Finset.mem_filter.mp hk).1
  have hcoord : ∀ k ∈ actualDyadicShell F j, ∀ i : Fin 3,
      -(R : ℤ) < k i ∧ k i < (R : ℤ) := by
    intro k hk i
    have hmem := Finset.mem_filter.mp hk
    have hb := S_DIR_L2_SUPNORM_SHELL_COORD_UPPER k
      (hnonzero k hmem.1) i
    simpa only [hmem.2, R] using hb
  have hcount := S_DIR_L2_PLANE_STRICT_CUBE_CARD
    a ha (actualDyadicShell F j) R hR hp hcoord
  have hpow : R = 2 * (2 : ℕ) ^ j := by
    dsimp [R]
    rw [pow_succ]
    omega
  have hlin : 2 * R - 1 ≤ 4 * (2 : ℕ) ^ j := by
    rw [hpow]
    omega
  calc
    (actualDyadicShell F j).card ≤ (2 * R - 1) ^ 2 := hcount
    _ ≤ (4 * (2 : ℕ) ^ j) ^ 2 := by
      gcongr <;> exact hlin
    _ = 16 * ((2 : ℕ) ^ j) ^ 2 := by ring

/-- The radial bound applies to each actual shell member, without assumptions. -/
theorem S_DIR_L2_ACTUAL_SHELL_RADIUS_LOWER
    (F : Finset Mode3) (hnonzero : ∀ k ∈ F, k ≠ 0)
    (j : ℕ) (k : Mode3) (hk : k ∈ actualDyadicShell F j) :
    (2 : ℝ) ^ j ≤ Real.sqrt (latticeRadiusSq k) := by
  have hh := Finset.mem_filter.mp hk
  have h := S_DIR_L2_SUPNORM_SHELL_RADIUS_LOWER k (hnonzero k hh.1)
  simpa only [hh.2] using h

/-- The previous finite-shell theorem applies to actual, non-admitted shells. -/
theorem S_DIR_L2_ACTUAL_SHELL_ROW_BUDGET
    (a : Mode3) (ha : a ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (F : Finset Mode3)
    (hplane : ∀ k ∈ F, directionalDot a k = 0)
    (hnonzero : ∀ k ∈ F, k ≠ 0)
    (j : ℕ) :
    (∑ k ∈ actualDyadicShell F j, directionalRadialRowTerm r k) ≤
      16 * dyadicKernelTerm r j := by
  have hcardN := S_DIR_L2_ACTUAL_SHELL_CARD a ha F hplane hnonzero j
  have hcardR : ((actualDyadicShell F j).card : ℝ) ≤
      16 * (((2 : ℝ) ^ j) ^ 2) := by
    exact_mod_cast hcardN
  exact S_DIR_L2_DYADIC_FINITE_SHELL_BUDGET r hr j
    (actualDyadicShell F j) hcardR
    (S_DIR_L2_ACTUAL_SHELL_RADIUS_LOWER F hnonzero j)

/-- Actual finite directional-plane row bound: no partition or annulus premises. -/
theorem S_DIR_L2_ACTUAL_FINITE_PLANE_ROW
    (a : Mode3) (ha : a ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (F : Finset Mode3)
    (hplane : ∀ k ∈ F, directionalDot a k = 0)
    (hnonzero : ∀ k ∈ F, k ≠ 0) :
    (∑ k ∈ F, directionalRadialRowTerm r k) ≤ 64 / r := by
  classical
  let N := F.sup latticeShellIndex + 1
  have hpart : F = (Finset.range N).biUnion (actualDyadicShell F) :=
    S_DIR_L2_ACTUAL_SHELL_PARTITION F
  have hdisj : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint
      (actualDyadicShell F) := S_DIR_L2_ACTUAL_SHELL_DISJOINT F N
  rw [hpart, Finset.sum_biUnion hdisj]
  calc
    (∑ j ∈ Finset.range N,
      ∑ k ∈ actualDyadicShell F j, directionalRadialRowTerm r k)
        ≤ ∑ j ∈ Finset.range N, 16 * dyadicKernelTerm r j := by
          apply Finset.sum_le_sum
          intro j hj
          exact S_DIR_L2_ACTUAL_SHELL_ROW_BUDGET
            a ha r hr F hplane hnonzero j
    _ = 16 * (∑ j ∈ Finset.range N, dyadicKernelTerm r j) := by
      rw [Finset.mul_sum]
    _ ≤ 16 * (4 / r) := by
      exact mul_le_mul_of_nonneg_left
        (S_DIR_L2_DYADIC_KERNEL_PREFIX_BOUND r hr N) (by norm_num)
    _ = 64 / r := by ring

/-- The exact infinite-lattice radial term, zero off the nonzero plane. -/
def planeRadialRowTerm (a : Mode3) (r : ℝ) (k : Mode3) : ℝ :=
  if directionalDot a k = 0 ∧ k ≠ 0 then directionalRadialRowTerm r k else 0

/-- The radial denominator is strictly positive at every nonzero mode. -/
theorem S_DIR_L2_NONZERO_RADIUS_POS (k : Mode3) (hk : k ≠ 0) :
    0 < Real.sqrt (latticeRadiusSq k) := by
  have hp : (0 : ℝ) < (latticeSupNorm k : ℝ) := by
    exact_mod_cast S_DIR_L2_SUPNORM_POS k hk
  exact hp.trans_le (S_DIR_L2_SUPNORM_LE_EUCLIDEAN k)

/-- The infinite row is a nonnegative real series in the ambient integer lattice. -/
theorem S_DIR_L2_PLANE_RADIAL_ROW_NONNEG
    (a : Mode3) (r : ℝ) (hr : 0 < r) (k : Mode3) :
    0 ≤ planeRadialRowTerm a r k := by
  unfold planeRadialRowTerm
  split_ifs with h
  · unfold directionalRadialRowTerm
    have hs := S_DIR_L2_NONZERO_RADIUS_POS k h.2
    positivity
  · exact le_refl _

/-- Uniform finite bound for the plane kernel extended by zero to Z^3. -/
theorem S_DIR_L2_FINITE_AMBIENT_PLANE_ROW
    (a : Mode3) (ha : a ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (F : Finset Mode3) :
    (∑ k ∈ F, planeRadialRowTerm a r k) ≤ 64 / r := by
  classical
  let G : Finset Mode3 :=
    F.filter (fun k => directionalDot a k = 0 ∧ k ≠ 0)
  have hplane : ∀ k ∈ G, directionalDot a k = 0 := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2.1
  have hnonzero : ∀ k ∈ G, k ≠ 0 := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2.2
  calc
    (∑ k ∈ F, planeRadialRowTerm a r k)
      = ∑ k ∈ G, directionalRadialRowTerm r k := by
        simp [planeRadialRowTerm, G, Finset.sum_ite]
    _ ≤ 64 / r := S_DIR_L2_ACTUAL_FINITE_PLANE_ROW
      a ha r hr G hplane hnonzero

/-- Actual unconditional infinite rank-two row bound; no shell-cover premise. -/
theorem S_DIR_L2_ACTUAL_INFINITE_LATTICE_ROW
    (a : Mode3) (ha : a ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    Summable (planeRadialRowTerm a r) ∧
      (∑' k : Mode3, planeRadialRowTerm a r k) ≤ 64 / r := by
  exact S_DIR_L2_INFINITE_ROW_FROM_ALL_FINITE_BOUNDS
    (planeRadialRowTerm a r) (64 / r)
    (S_DIR_L2_PLANE_RADIAL_ROW_NONNEG a r hr)
    (S_DIR_L2_FINITE_AMBIENT_PLANE_ROW a ha r hr)

end SDirL2
