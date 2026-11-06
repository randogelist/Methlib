import Main

/-!
Candidate bridge from a common-denominator integer encoding to the exact
`PoincareSecond.Certificate.check` in the imported original source. Integer
inputs may be arbitrarily large and G-coefficients remain signed. This file is
uncompiled and unaudited. It does not claim that any C program implements the
predicate below, nor that an accepted witness exists.
-/

open scoped BigOperators
open PoincareSecond

namespace CollatzIntegerBridge

abbrev ZVec (d : ℕ) := Fin d → ℤ

structure ZAffine (d : ℕ) where
  mat : Fin d → Fin d → ℤ
  offset : ZVec d

structure Encoding (d : ℕ) where
  den : ℤ
  B0 : ZAffine d
  B1 : ZAffine d
  G0 : ZAffine d
  G1 : ZAffine d
  G2 : ZAffine d
  seed : ZVec d
  weight : ZVec d

variable {d : ℕ}

def decodeAffine (D : ℤ) (F : ZAffine d) : Affine d where
  mat i j := (F.mat i j : ℚ) / (D : ℚ)
  offset i := (F.offset i : ℚ) / (D : ℚ)

def decodeVec (D : ℤ) (x : ZVec d) : Vec d :=
  fun i => (x i : ℚ) / (D : ℚ)

def decode (E : Encoding d) : Certificate d where
  B0 := decodeAffine E.den E.B0
  B1 := decodeAffine E.den E.B1
  G0 := decodeAffine E.den E.G0
  G1 := decodeAffine E.den E.G1
  G2 := decodeAffine E.den E.G2
  seed := decodeVec E.den E.seed
  weight := decodeVec E.den E.weight

/-- The exact integer numerator of a composition matrix entry. -/
def compMat (F G : ZAffine d) (i j : Fin d) : ℤ :=
  ∑ k, F.mat i k * G.mat k j

/-- The exact integer numerator of a composition offset. -/
def compOffset (D : ℤ) (F G : ZAffine d) (i : Fin d) : ℤ :=
  (∑ k, F.mat i k * G.offset k) + D * F.offset i

def compLE (D : ℤ) (F G K L : ZAffine d) : Prop :=
  (∀ i j, compMat F G i j ≤ compMat K L i j) ∧
  (∀ i, compOffset D F G i ≤ compOffset D K L i)

def nonnegative (F : ZAffine d) : Prop :=
  (∀ i j, 0 ≤ F.mat i j) ∧ (∀ i, 0 ≤ F.offset i)

/-- Numerator of `F(seed / D)` over `D²`. -/
def evalOne (D : ℤ) (F : ZAffine d) (s : ZVec d) (i : Fin d) : ℤ :=
  (∑ j, F.mat i j * s j) + D * F.offset i

/-- Numerator of `F(G(seed / D))` over `D³`. -/
def evalTwo (D : ℤ) (F G : ZAffine d) (s : ZVec d) (i : Fin d) : ℤ :=
  (∑ j, F.mat i j * evalOne D G s j) + D ^ 2 * F.offset i

def weighted (z : ZVec d) (F : ZAffine d) (j : Fin d) : ℤ :=
  ∑ i, z i * F.mat i j

def gap (z : ZVec d) (F G : ZAffine d) : ℤ :=
  ∑ i, z i * (F.offset i - G.offset i)

/-- Completely explicit integer-only version of the original predicate.
The auxiliary map matrices and offsets are intentionally not constrained to
be nonnegative. `den > 0` is part of the input contract. -/
def IntegerValid (E : Encoding d) : Prop :=
  0 < E.den ∧
  nonnegative E.B0 ∧ nonnegative E.B1 ∧
  (∀ i, 0 ≤ E.seed i) ∧ (∀ i, 0 ≤ E.weight i) ∧
  compLE E.den E.B0 E.G0 E.G0 E.B0 ∧
  compLE E.den E.B1 E.G0 E.G1 E.B0 ∧
  compLE E.den E.B0 E.G1 E.G2 E.B0 ∧
  compLE E.den E.B1 E.G1 E.G0 E.B1 ∧
  compLE E.den E.B0 E.G2 E.G1 E.B1 ∧
  compLE E.den E.B1 E.G2 E.G2 E.B1 ∧
  (∀ i, evalOne E.den E.B1 E.seed i ≤ evalOne E.den E.G0 E.seed i) ∧
  (∀ i, evalTwo E.den E.B0 E.B0 E.seed i ≤ E.den * evalOne E.den E.G1 E.seed i) ∧
  (∀ i, evalTwo E.den E.B1 E.B0 E.seed i ≤ E.den * evalOne E.den E.G2 E.seed i) ∧
  (∀ j, E.den * E.weight j ≤ weighted E.weight E.B0 j) ∧
  (∀ j, weighted E.weight E.G2 j ≤ weighted E.weight E.B1 j) ∧
  E.den ^ 2 ≤ gap E.weight E.B1 E.G2

instance (E : Encoding d) : Decidable (IntegerValid E) := by
  unfold IntegerValid nonnegative compLE
  infer_instance

def integerCheck (E : Encoding d) : Bool := decide (IntegerValid E)

@[simp] theorem integerCheck_eq_true_iff (E : Encoding d) :
    (integerCheck E) = true ↔ (IntegerValid E) := by
  simp [integerCheck]

private theorem castDiv_le_castDiv (a b : ℤ) (q : ℚ) (hq : 0 < q) :
    (a : ℚ) / q ≤ (b : ℚ) / q ↔ a ≤ b := by
  rw [div_le_div_iff_of_pos_right hq]
  constructor <;> intro h <;> exact_mod_cast h

private theorem cast_mul_div_sq (a b : ℤ) (q : ℚ) :
    (a : ℚ) / q * ((b : ℚ) / q) = ((a * b : ℤ) : ℚ) / q ^ 2 := by
  push_cast
  simp only [div_eq_mul_inv, inv_pow]
  ring

private theorem cast_mul_div_cube (a b : ℤ) (q : ℚ) :
    (a : ℚ) / q * ((b : ℚ) / q ^ 2) = ((a * b : ℤ) : ℚ) / q ^ 3 := by
  push_cast
  simp only [div_eq_mul_inv, inv_pow]
  ring

private theorem sum_div_sq (a b : Fin d → ℤ) (q : ℚ) :
    (∑ j, (a j : ℚ) / q * ((b j : ℚ) / q)) =
      (((∑ j, a j * b j) : ℤ) : ℚ) / q ^ 2 := by
  simp only [cast_mul_div_sq, Int.cast_sum, Finset.sum_div]

private theorem sum_div_cube (a b : Fin d → ℤ) (q : ℚ) :
    (∑ j, (a j : ℚ) / q * ((b j : ℚ) / q ^ 2)) =
      (((∑ j, a j * b j) : ℤ) : ℚ) / q ^ 3 := by
  simp only [cast_mul_div_cube, Int.cast_sum, Finset.sum_div]

private theorem decode_comp_mat (D : ℤ) (F G : ZAffine d) (i j : Fin d) :
    ((decodeAffine D F).comp (decodeAffine D G)).mat i j =
      (compMat F G i j : ℚ) / (D : ℚ) ^ 2 := by
  simpa [Affine.comp, decodeAffine, compMat] using
    (sum_div_sq (fun k => F.mat i k) (fun k => G.mat k j) (D : ℚ))

private theorem decode_comp_offset (D : ℤ) (hD : 0 < D)
    (F G : ZAffine d) (i : Fin d) :
    ((decodeAffine D F).comp (decodeAffine D G)).offset i =
      (compOffset D F G i : ℚ) / (D : ℚ) ^ 2 := by
  have hq : (D : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  change (∑ k, (F.mat i k : ℚ) / (D : ℚ) * ((G.offset k : ℚ) / (D : ℚ))) +
    (F.offset i : ℚ) / (D : ℚ) = _
  rw [sum_div_sq]
  dsimp [compOffset]
  push_cast
  field_simp
  <;> ring

private theorem decode_eval_one (D : ℤ) (hD : 0 < D)
    (F : ZAffine d) (s : ZVec d) (i : Fin d) :
    (decodeAffine D F).eval (decodeVec D s) i =
      (evalOne D F s i : ℚ) / (D : ℚ) ^ 2 := by
  have hq : (D : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  change (∑ j, (F.mat i j : ℚ) / (D : ℚ) * ((s j : ℚ) / (D : ℚ))) +
    (F.offset i : ℚ) / (D : ℚ) = _
  rw [sum_div_sq]
  dsimp [evalOne]
  push_cast
  field_simp
  <;> ring

private theorem decode_eval_two (D : ℤ) (hD : 0 < D)
    (F G : ZAffine d) (s : ZVec d) (i : Fin d) :
    (decodeAffine D F).eval ((decodeAffine D G).eval (decodeVec D s)) i =
      (evalTwo D F G s i : ℚ) / (D : ℚ) ^ 3 := by
  have hq : (D : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  change (∑ j, (F.mat i j : ℚ) / (D : ℚ) *
    ((decodeAffine D G).eval (decodeVec D s) j)) +
    (F.offset i : ℚ) / (D : ℚ) = _
  simp_rw [decode_eval_one D hD G s]
  rw [sum_div_cube]
  dsimp [evalTwo]
  push_cast
  field_simp
  <;> ring

private theorem decode_weighted (D : ℤ) (z : ZVec d) (F : ZAffine d)
    (j : Fin d) :
    Affine.weightedRow (decodeVec D z) (decodeAffine D F) j =
      (weighted z F j : ℚ) / (D : ℚ) ^ 2 := by
  simpa [Affine.weightedRow, decodeVec, decodeAffine, weighted] using
    (sum_div_sq z (fun i => F.mat i j) (D : ℚ))

private theorem decode_gap (D : ℤ) (z : ZVec d) (F G : ZAffine d) :
    dot (decodeVec D z) ((decodeAffine D F).offset - (decodeAffine D G).offset) =
      (gap z F G : ℚ) / (D : ℚ) ^ 2 := by
  simp only [dot, decodeVec, decodeAffine, Pi.sub_apply, ← sub_div, ← Int.cast_sub,
    cast_mul_div_sq, Int.cast_sum, Finset.sum_div, gap]

private theorem nonnegative_iff (D : ℤ) (hD : 0 < D) (F : ZAffine d) :
    (decodeAffine D F).Nonnegative ↔ nonnegative F := by
  have hq : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  simp only [Affine.Nonnegative, nonnegative, decodeAffine, Pi.le_def, Pi.zero_apply]
  constructor <;> intro h <;> constructor
  · intro i j
    have hh := h.1 i j
    have hh' : (0 : ℚ) / (D : ℚ) ≤ (F.mat i j : ℚ) / (D : ℚ) := by simpa using hh
    exact (castDiv_le_castDiv 0 _ _ hq).mp hh'
  · intro i
    have hh := h.2 i
    have hh' : (0 : ℚ) / (D : ℚ) ≤ (F.offset i : ℚ) / (D : ℚ) := by simpa using hh
    exact (castDiv_le_castDiv 0 _ _ hq).mp hh'
  · intro i j
    have hh := (castDiv_le_castDiv 0 (F.mat i j) _ hq).mpr (h.1 i j)
    simpa using hh
  · intro i
    have hh := (castDiv_le_castDiv 0 (F.offset i) _ hq).mpr (h.2 i)
    simpa using hh

private theorem vec_nonnegative_iff (D : ℤ) (hD : 0 < D) (z : ZVec d) :
    (0 : Vec d) ≤ decodeVec D z ↔ ∀ i, 0 ≤ z i := by
  have hq : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  simp only [Pi.le_def, Pi.zero_apply, decodeVec]
  constructor
  · intro h i
    have hh : (0 : ℚ) / (D : ℚ) ≤ (z i : ℚ) / (D : ℚ) := by simpa using h i
    exact (castDiv_le_castDiv 0 _ _ hq).mp hh
  · intro h i
    have hh := (castDiv_le_castDiv 0 (z i) _ hq).mpr (h i)
    simpa using hh

private theorem comp_iff (D : ℤ) (hD : 0 < D) (F G K L : ZAffine d) :
    ((decodeAffine D F).comp (decodeAffine D G)).CoeffLE
      ((decodeAffine D K).comp (decodeAffine D L)) ↔ compLE D F G K L := by
  have hq : (0 : ℚ) < (D : ℚ) ^ 2 := by
    have : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
    positivity
  simp only [Affine.CoeffLE, Pi.le_def, compLE, decode_comp_mat,
    decode_comp_offset D hD]
  constructor <;> intro h <;> constructor
  · intro i j; exact (castDiv_le_castDiv _ _ _ hq).mp (h.1 i j)
  · intro i; exact (castDiv_le_castDiv _ _ _ hq).mp (h.2 i)
  · intro i j; exact (castDiv_le_castDiv _ _ _ hq).mpr (h.1 i j)
  · intro i; exact (castDiv_le_castDiv _ _ _ hq).mpr (h.2 i)

private theorem eval_one_iff (D : ℤ) (hD : 0 < D) (F G : ZAffine d) (s : ZVec d) :
    (decodeAffine D F).eval (decodeVec D s) ≤ (decodeAffine D G).eval (decodeVec D s) ↔
      ∀ i, evalOne D F s i ≤ evalOne D G s i := by
  have hq : (0 : ℚ) < (D : ℚ) ^ 2 := by
    have : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
    positivity
  simp only [Pi.le_def, decode_eval_one D hD]
  constructor <;> intro h i
  · exact (castDiv_le_castDiv _ _ _ hq).mp (h i)
  · exact (castDiv_le_castDiv _ _ _ hq).mpr (h i)

private theorem eval_two_iff (D : ℤ) (hD : 0 < D) (F G K : ZAffine d) (s : ZVec d) :
    (decodeAffine D F).eval ((decodeAffine D G).eval (decodeVec D s)) ≤
      (decodeAffine D K).eval (decodeVec D s) ↔
      ∀ i, evalTwo D F G s i ≤ D * evalOne D K s i := by
  have hd : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  have hq : (0 : ℚ) < (D : ℚ) ^ 3 := by positivity
  have hne : (D : ℚ) ≠ 0 := ne_of_gt hd
  simp only [Pi.le_def, decode_eval_one D hD, decode_eval_two D hD]
  constructor <;> intro h i
  · have hk : (evalOne D K s i : ℚ) / (D : ℚ) ^ 2 =
        ((D * evalOne D K s i : ℤ) : ℚ) / (D : ℚ) ^ 3 := by
      push_cast; field_simp <;> ring
    have hi := h i
    rw [hk] at hi
    exact (castDiv_le_castDiv _ _ _ hq).mp hi
  · have hk : (evalOne D K s i : ℚ) / (D : ℚ) ^ 2 =
        ((D * evalOne D K s i : ℤ) : ℚ) / (D : ℚ) ^ 3 := by
      push_cast; field_simp <;> ring
    rw [hk]
    exact (castDiv_le_castDiv _ _ _ hq).mpr (h i)

private theorem weighted_left_iff (D : ℤ) (hD : 0 < D) (z : ZVec d) (F : ZAffine d) :
    decodeVec D z ≤ Affine.weightedRow (decodeVec D z) (decodeAffine D F) ↔
      ∀ j, D * z j ≤ weighted z F j := by
  have hd : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  have hq : (0 : ℚ) < (D : ℚ) ^ 2 := by positivity
  have hne : (D : ℚ) ≠ 0 := ne_of_gt hd
  change (∀ j, (z j : ℚ) / (D : ℚ) ≤
    Affine.weightedRow (decodeVec D z) (decodeAffine D F) j) ↔
    (∀ j, D * z j ≤ weighted z F j)
  simp only [decode_weighted]
  constructor <;> intro h j
  · have hk : (z j : ℚ) / (D : ℚ) = ((D * z j : ℤ) : ℚ) / (D : ℚ) ^ 2 := by
      push_cast; field_simp <;> ring
    have hj := h j
    rw [hk] at hj
    exact (castDiv_le_castDiv _ _ _ hq).mp hj
  · have hk : (z j : ℚ) / (D : ℚ) = ((D * z j : ℤ) : ℚ) / (D : ℚ) ^ 2 := by
      push_cast; field_simp <;> ring
    rw [hk]
    exact (castDiv_le_castDiv _ _ _ hq).mpr (h j)

private theorem weighted_iff (D : ℤ) (hD : 0 < D) (z : ZVec d) (F G : ZAffine d) :
    Affine.weightedRow (decodeVec D z) (decodeAffine D F) ≤
      Affine.weightedRow (decodeVec D z) (decodeAffine D G) ↔
      ∀ j, weighted z F j ≤ weighted z G j := by
  have hq : (0 : ℚ) < (D : ℚ) ^ 2 := by
    have : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
    positivity
  simp only [Pi.le_def, decode_weighted]
  constructor <;> intro h j
  · exact (castDiv_le_castDiv _ _ _ hq).mp (h j)
  · exact (castDiv_le_castDiv _ _ _ hq).mpr (h j)

private theorem gap_iff (D : ℤ) (hD : 0 < D) (z : ZVec d) (F G : ZAffine d) :
    1 ≤ dot (decodeVec D z) ((decodeAffine D F).offset - (decodeAffine D G).offset) ↔
      D ^ 2 ≤ gap z F G := by
  have hd : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  have hq : (0 : ℚ) < (D : ℚ) ^ 2 := by positivity
  have hne : (D : ℚ) ≠ 0 := ne_of_gt hd
  rw [decode_gap]
  have hone : (1 : ℚ) = ((D ^ 2 : ℤ) : ℚ) / (D : ℚ) ^ 2 := by
    push_cast; field_simp
  rw [hone]
  exact castDiv_le_castDiv _ _ _ hq

/-- The exact integer predicate is equivalent to the original rational check,
including positivity of the chosen common denominator. -/
theorem integerValid_iff_original_check (E : Encoding d) :
    (IntegerValid E) ↔ 0 < E.den ∧ (decode E).check = true := by
  constructor
  · intro h
    have hD := h.1
    refine ⟨hD, ?_⟩
    apply (Certificate.check_eq_true_iff _).mpr
    simpa only [decode, Certificate.Valid, IntegerValid,
      nonnegative_iff E.den hD, vec_nonnegative_iff E.den hD,
      comp_iff E.den hD, eval_one_iff E.den hD, eval_two_iff E.den hD,
      weighted_left_iff E.den hD, weighted_iff E.den hD, gap_iff E.den hD] using h.2
  · rintro ⟨hD, hcheck⟩
    have hv := (Certificate.check_eq_true_iff _).mp hcheck
    refine ⟨hD, ?_⟩
    simpa only [decode, Certificate.Valid, IntegerValid,
      nonnegative_iff E.den hD, vec_nonnegative_iff E.den hD,
      comp_iff E.den hD, eval_one_iff E.den hD, eval_two_iff E.den hD,
      weighted_left_iff E.den hD, weighted_iff E.den hD, gap_iff E.den hD] using hv

theorem integerCheck_iff_original_check (E : Encoding d) :
    (integerCheck E) = true ↔ 0 < E.den ∧ (decode E).check = true := by
  rw [integerCheck_eq_true_iff, integerValid_iff_original_check]

theorem integerValid_implies_collatz (E : Encoding d) (hE : (IntegerValid E)) :
    ∀ n : ℕ, 0 < n → OrdinaryReachesOne n := by
  exact CHECKER_SOUND (decode E) ((integerValid_iff_original_check E).mp hE).2

#print axioms integerValid_iff_original_check
#print axioms integerCheck_iff_original_check
#print axioms integerValid_implies_collatz

end CollatzIntegerBridge
