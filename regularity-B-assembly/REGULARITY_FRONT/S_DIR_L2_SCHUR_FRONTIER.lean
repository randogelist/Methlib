import S_DIR_L2_GLOBAL_REGULARITY

set_option autoImplicit false
set_option maxHeartbeats 0

open scoped BigOperators

noncomputable section

namespace SDirL2

/-!
# Independent rank-two lattice / weighted Schur proof frontier

No physical-NSE assertion and no analytic certificate is admitted here.
The exact frozen `S_DIR_L2_GLOBAL_REGULARITY` remains a target definition.

Two separable unconditional arithmetic/algebraic lemmas are formalized:
* Projection is injective on every integer-direction Fourier plane.
* Any finite plane set in a coordinate cube has a uniform O(N²) bound.
* An exact finite weighted-Schur inequality under its explicit row bound.

The exact geometric annulus bound, infinite Schur row estimate,
physical torus synthesis, and unrestricted weak-strong uniqueness remain
separately named obligations, not consequences of the finite lemmas alone.
-/

/-- Choose two coordinates complementary to a nonzero direction component. -/
def planeProjection (a k : Mode3) : ℤ × ℤ :=
  if a 0 ≠ 0 then (k 1, k 2)
  else if a 1 ≠ 0 then (k 0, k 2)
  else (k 0, k 1)

/-- Uniform injectivity on `a · k = 0`, without a primitive-axis assumption. -/
theorem S_DIR_L2_PLANE_PROJECTION_INJECTIVE
    (a : Mode3) (ha : a ≠ 0)
    (k l : Mode3)
    (hk : directionalDot a k = 0)
    (hl : directionalDot a l = 0)
    (hproj : planeProjection a k = planeProjection a l) : k = l := by
  by_cases ha0 : a 0 ≠ 0
  · simp only [planeProjection, if_pos ha0] at hproj
    have h1 : k 1 = l 1 := congrArg Prod.fst hproj
    have h2 : k 2 = l 2 := congrArg Prod.snd hproj
    have hmul : a 0 * k 0 = a 0 * l 0 := by
      unfold directionalDot at hk hl
      rw [h1, h2] at hk
      omega
    have h0 : k 0 = l 0 := mul_left_cancel₀ ha0 hmul
    funext i
    fin_cases i <;> assumption
  · by_cases ha1 : a 1 ≠ 0
    · simp only [planeProjection, if_neg ha0, if_pos ha1] at hproj
      have h0 : k 0 = l 0 := congrArg Prod.fst hproj
      have h2 : k 2 = l 2 := congrArg Prod.snd hproj
      have hmul : a 1 * k 1 = a 1 * l 1 := by
        unfold directionalDot at hk hl
        rw [h0, h2] at hk
        omega
      have h1 : k 1 = l 1 := mul_left_cancel₀ ha1 hmul
      funext i
      fin_cases i <;> assumption
    · have ha2 : a 2 ≠ 0 := by
        intro heq
        apply ha
        have h0 : a 0 = 0 := by simpa using ha0
        have h1 : a 1 = 0 := by simpa using ha1
        funext i
        fin_cases i <;> assumption
      simp only [planeProjection, if_neg ha0, if_neg ha1] at hproj
      have h0 : k 0 = l 0 := congrArg Prod.fst hproj
      have h1 : k 1 = l 1 := congrArg Prod.snd hproj
      have hmul : a 2 * k 2 = a 2 * l 2 := by
        unfold directionalDot at hk hl
        rw [h0, h1] at hk
        omega
      have h2 : k 2 = l 2 := mul_left_cancel₀ ha2 hmul
      funext i
      fin_cases i <;> assumption

/-- Cardinality is bounded by the square of the integer side interval. -/
theorem S_DIR_L2_PLANE_FINITE_CUBE_CARD
    (a : Mode3) (ha : a ≠ 0) (F : Finset Mode3) (N : ℕ)
    (hplane : ∀ k ∈ F, directionalDot a k = 0)
    (hcube : ∀ k ∈ F, ∀ i : Fin 3,
      -(N : ℤ) ≤ k i ∧ k i ≤ (N : ℤ)) :
    F.card ≤ (Finset.Icc (-(N : ℤ)) (N : ℤ)).card ^ 2 := by
  classical
  let side : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let square : Finset (ℤ × ℤ) := side.product side
  have hMaps : ∀ k ∈ F, planeProjection a k ∈ square := by
    intro k hk
    have h0 := hcube k hk 0
    have h1 := hcube k hk 1
    have h2 := hcube k hk 2
    by_cases ha0 : a 0 ≠ 0
    · simpa [planeProjection, ha0, square, side] using (And.intro h1 h2)
    · by_cases ha1 : a 1 ≠ 0
      · simpa [planeProjection, ha0, ha1, square, side] using (And.intro h0 h2)
      · simpa [planeProjection, ha0, ha1, square, side] using (And.intro h0 h1)
  have hInj : ∀ k ∈ F, ∀ l ∈ F,
      planeProjection a k = planeProjection a l → k = l := by
    intro k hk l hl hkl
    exact S_DIR_L2_PLANE_PROJECTION_INJECTIVE a ha k l
      (hplane k hk) (hplane l hl) hkl
  have hCard : F.card ≤ square.card :=
    Finset.card_le_card_of_injOn (planeProjection a) hMaps hInj
  simpa [square, side, pow_two] using hCard

/-! ## Denominator-free finite weighted Schur algebra -/

/-- Symmetric pointwise Young bound, valid without any sign assumption on x,y. -/
theorem schur_pair_young
    (A x y : ℝ) (hA : 0 ≤ A) :
    A * (x * y) ≤ (A * x ^ 2 + A * y ^ 2) / 2 := by
  have hsq : 0 ≤ A * (x - y) ^ 2 :=
    mul_nonneg hA (sq_nonneg _)
  nlinarith [hsq]

/--
An unconditional finite weighted Schur reduction. Its row-estimate
hypothesis is explicit; this theorem does *not* assert that the
rank-two lattice kernel automatically meets that hypothesis.

The unnormalized coefficient at i is `w i * c i`; hence this lemma
requires no division or hidden positivity premise on data c.
-/
theorem S_DIR_L2_WEIGHTED_FINITE_SCHUR
    {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (K : ι → ι → ℝ)
    (w c : ι → ℝ) (C : ℝ)
    (hK : ∀ i ∈ F, ∀ j ∈ F, 0 ≤ K i j)
    (hSym : ∀ i ∈ F, ∀ j ∈ F, K i j = K j i)
    (hW : ∀ i ∈ F, 0 < w i)
    (hRow : ∀ i ∈ F,
      (∑ j ∈ F, K i j * w j) ≤ C * w i) :
    (∑ i ∈ F, ∑ j ∈ F,
        (K i j * w i * w j) * (c i * c j))
      ≤ C * ∑ i ∈ F, (w i * c i) ^ 2 := by
  let A : ι → ι → ℝ := fun i j => K i j * w i * w j
  have hAn : ∀ i ∈ F, ∀ j ∈ F, 0 ≤ A i j := by
    intro i hi j hj
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (hK i hi j hj) (le_of_lt (hW i hi)))
      (le_of_lt (hW j hj))
  have hAsym : ∀ i ∈ F, ∀ j ∈ F, A i j = A j i := by
    intro i hi j hj
    dsimp [A]
    rw [hSym i hi j hj]
    ring
  have hSwitch :
      (∑ i ∈ F, ∑ j ∈ F, A i j * (c j) ^ 2) =
      (∑ i ∈ F, ∑ j ∈ F, A i j * (c i) ^ 2) := by
    calc
      (∑ i ∈ F, ∑ j ∈ F, A i j * (c j) ^ 2)
          = ∑ j ∈ F, ∑ i ∈ F, A i j * (c j) ^ 2 := Finset.sum_comm
      _ = ∑ j ∈ F, ∑ i ∈ F, A j i * (c j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        rw [hAsym i hi j hj]
      _ = ∑ i ∈ F, ∑ j ∈ F, A i j * (c i) ^ 2 := rfl
  have hPairSum :
      (∑ i ∈ F, ∑ j ∈ F, A i j * (c i * c j)) ≤
      (∑ i ∈ F, ∑ j ∈ F, A i j * (c i) ^ 2) := by
    calc
      (∑ i ∈ F, ∑ j ∈ F, A i j * (c i * c j))
          ≤ ∑ i ∈ F, ∑ j ∈ F,
              (A i j * (c i) ^ 2 + A i j * (c j) ^ 2) / 2 := by
                apply Finset.sum_le_sum
                intro i hi
                apply Finset.sum_le_sum
                intro j hj
                exact schur_pair_young (A i j) (c i) (c j) (hAn i hi j hj)
      _ = ((∑ i ∈ F, ∑ j ∈ F, A i j * (c i) ^ 2) +
            (∑ i ∈ F, ∑ j ∈ F, A i j * (c j) ^ 2)) / 2 := by
              -- First split each pairwise numerator by add_div; then distribute
              -- the finite sums, and finally pull out division by 2.
              -- No hypothesis or theorem type is modified by this normalization.
              simp_rw [add_div, Finset.sum_add_distrib, Finset.sum_div]
      _ = (∑ i ∈ F, ∑ j ∈ F, A i j * (c i) ^ 2) := by
        rw [hSwitch]
        ring
  have hFactor (i : ι) :
      (∑ j ∈ F, A i j * (c i) ^ 2) =
      (w i * (c i) ^ 2) * (∑ j ∈ F, K i j * w j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [A]
    ring
  have hRowsBound :
      (∑ i ∈ F, ∑ j ∈ F, A i j * (c i) ^ 2)
        ≤ C * ∑ i ∈ F, (w i * c i) ^ 2 := by
    calc
      (∑ i ∈ F, ∑ j ∈ F, A i j * (c i) ^ 2)
          = ∑ i ∈ F, (w i * (c i) ^ 2) * (∑ j ∈ F, K i j * w j) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hFactor i
      _ ≤ ∑ i ∈ F, (w i * (c i) ^ 2) * (C * w i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hRow i hi)
          (mul_nonneg (le_of_lt (hW i hi)) (sq_nonneg _))
      _ = C * ∑ i ∈ F, (w i * c i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  exact hPairSum.trans hRowsBound

end SDirL2
