import Mathlib

open scoped BigOperators

namespace PoincareSecond

abbrev Vec (d : ℕ) := Fin d → ℚ

-- Decide vector inequalities by checking finitely many rational coordinates.
instance instDecidableLEVec (d : ℕ) : DecidableLE (Vec d) :=
  fun x y => inferInstanceAs (Decidable (∀ i : Fin d, x i ≤ y i))

def dot {d : ℕ} (u v : Vec d) : ℚ :=
  ∑ i, u i * v i

@[simp] theorem dot_zero_right {d : ℕ} (u : Vec d) : dot u 0 = 0 := by
  simp [dot]

theorem dot_nonneg {d : ℕ} {u v : Vec d}
    (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ dot u v := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hu i) (hv i))

theorem dot_mono_right {d : ℕ} {u x y : Vec d}
    (hu : 0 ≤ u) (hxy : x ≤ y) : dot u x ≤ dot u y := by
  exact Finset.sum_le_sum
    (fun i _ => mul_le_mul_of_nonneg_left (hxy i) (hu i))

theorem dot_mono_left {d : ℕ} {u v x : Vec d}
    (hx : 0 ≤ x) (huv : u ≤ v) : dot u x ≤ dot v x := by
  exact Finset.sum_le_sum
    (fun i _ => mul_le_mul_of_nonneg_right (huv i) (hx i))

theorem dot_sub_right {d : ℕ} (u x y : Vec d) :
    dot u (x - y) = dot u x - dot u y := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

structure Affine (d : ℕ) where
  mat : Fin d → Fin d → ℚ
  offset : Vec d

namespace Affine

variable {d : ℕ}

def eval (F : Affine d) (x : Vec d) : Vec d :=
  fun i => (∑ j, F.mat i j * x j) + F.offset i

def comp (F G : Affine d) : Affine d where
  mat i j := ∑ k, F.mat i k * G.mat k j
  offset i := (∑ k, F.mat i k * G.offset k) + F.offset i

theorem eval_comp (F G : Affine d) (x : Vec d) :
    (F.comp G).eval x = F.eval (G.eval x) := by
  funext i
  simp only [comp, eval, Finset.sum_mul, Finset.mul_sum, mul_add,
    Finset.sum_add_distrib, mul_assoc]
  rw [Finset.sum_comm]
  ring

def Nonnegative (F : Affine d) : Prop :=
  (∀ i j, 0 ≤ F.mat i j) ∧ 0 ≤ F.offset

def CoeffLE (F G : Affine d) : Prop :=
  (∀ i j, F.mat i j ≤ G.mat i j) ∧ F.offset ≤ G.offset

theorem eval_nonneg {F : Affine d} (hF : F.Nonnegative)
    {x : Vec d} (hx : 0 ≤ x) : 0 ≤ F.eval x := by
  intro i
  exact add_nonneg
    (Finset.sum_nonneg (fun j _ => mul_nonneg (hF.1 i j) (hx j)))
    (hF.2 i)

theorem eval_mono {F : Affine d} (hF : F.Nonnegative)
    {x y : Vec d} (hxy : x ≤ y) : F.eval x ≤ F.eval y := by
  intro i
  change (∑ j, F.mat i j * x j) + F.offset i ≤
    (∑ j, F.mat i j * y j) + F.offset i
  exact add_le_add
    (Finset.sum_le_sum
      (fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hF.1 i j)))
    (le_refl (F.offset i))

theorem coeffLE_eval_le {F G : Affine d} (hFG : F.CoeffLE G)
    {x : Vec d} (hx : 0 ≤ x) : F.eval x ≤ G.eval x := by
  intro i
  exact add_le_add
    (Finset.sum_le_sum
      (fun j _ => mul_le_mul_of_nonneg_right (hFG.1 i j) (hx j)))
    (hFG.2 i)

def weightedRow (w : Vec d) (F : Affine d) : Vec d :=
  fun j => ∑ i, w i * F.mat i j

theorem dot_eval (w : Vec d) (F : Affine d) (x : Vec d) :
    dot w (F.eval x) = dot (weightedRow w F) x + dot w F.offset := by
  simp only [dot, eval, weightedRow, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

end Affine

structure Certificate (d : ℕ) where
  B0 : Affine d
  B1 : Affine d
  G0 : Affine d
  G1 : Affine d
  G2 : Affine d
  seed : Vec d
  weight : Vec d

namespace Certificate

variable {d : ℕ}

def observe (W : Certificate d) (x : Vec d) : ℚ := dot W.weight x

@[simp] theorem observe_zero (W : Certificate d) :
    W.observe (0 : Vec d) = 0 := by
  simp [observe]

def Valid (W : Certificate d) : Prop :=
  W.B0.Nonnegative ∧
  W.B1.Nonnegative ∧
  0 ≤ W.seed ∧
  0 ≤ W.weight ∧
  (W.B0.comp W.G0).CoeffLE (W.G0.comp W.B0) ∧
  (W.B1.comp W.G0).CoeffLE (W.G1.comp W.B0) ∧
  (W.B0.comp W.G1).CoeffLE (W.G2.comp W.B0) ∧
  (W.B1.comp W.G1).CoeffLE (W.G0.comp W.B1) ∧
  (W.B0.comp W.G2).CoeffLE (W.G1.comp W.B1) ∧
  (W.B1.comp W.G2).CoeffLE (W.G2.comp W.B1) ∧
  W.B1.eval W.seed ≤ W.G0.eval W.seed ∧
  W.B0.eval (W.B0.eval W.seed) ≤ W.G1.eval W.seed ∧
  W.B1.eval (W.B0.eval W.seed) ≤ W.G2.eval W.seed ∧
  W.weight ≤ Affine.weightedRow W.weight W.B0 ∧
  Affine.weightedRow W.weight W.G2 ≤ Affine.weightedRow W.weight W.B1 ∧
  1 ≤ dot W.weight (W.B1.offset - W.G2.offset)

instance validDecidable (W : Certificate d) : Decidable W.Valid := by
  unfold Valid Affine.Nonnegative Affine.CoeffLE
  infer_instance

def check (W : Certificate d) : Bool := decide W.Valid

@[simp] theorem check_eq_true_iff (W : Certificate d) :
    W.check = true ↔ W.Valid := by
  simp [check]

structure Semantics (W : Certificate d) : Prop where
  B0_nonneg : ∀ x, 0 ≤ x → 0 ≤ W.B0.eval x
  B1_nonneg : ∀ x, 0 ≤ x → 0 ≤ W.B1.eval x
  B0_mono : ∀ {x y}, x ≤ y → W.B0.eval x ≤ W.B0.eval y
  B1_mono : ∀ {x y}, x ≤ y → W.B1.eval x ≤ W.B1.eval y
  seed_nonneg : 0 ≤ W.seed
  weight_nonneg : 0 ≤ W.weight
  observe_mono : ∀ {x y}, x ≤ y → W.observe x ≤ W.observe y
  recode00 : ∀ x, 0 ≤ x →
    W.B0.eval (W.G0.eval x) ≤ W.G0.eval (W.B0.eval x)
  recode10 : ∀ x, 0 ≤ x →
    W.B1.eval (W.G0.eval x) ≤ W.G1.eval (W.B0.eval x)
  recode20 : ∀ x, 0 ≤ x →
    W.B0.eval (W.G1.eval x) ≤ W.G2.eval (W.B0.eval x)
  recode01 : ∀ x, 0 ≤ x →
    W.B1.eval (W.G1.eval x) ≤ W.G0.eval (W.B1.eval x)
  recode11 : ∀ x, 0 ≤ x →
    W.B0.eval (W.G2.eval x) ≤ W.G1.eval (W.B1.eval x)
  recode21 : ∀ x, 0 ≤ x →
    W.B1.eval (W.G2.eval x) ≤ W.G2.eval (W.B1.eval x)
  base0 : W.B1.eval W.seed ≤ W.G0.eval W.seed
  base1 : W.B0.eval (W.B0.eval W.seed) ≤ W.G1.eval W.seed
  base2 : W.B1.eval (W.B0.eval W.seed) ≤ W.G2.eval W.seed
  even_rank : ∀ x, 0 ≤ x → W.observe x ≤ W.observe (W.B0.eval x)
  odd_rank : ∀ x, 0 ≤ x →
    W.observe (W.G2.eval x) + 1 ≤ W.observe (W.B1.eval x)

theorem Semantics.observe_nonneg {W : Certificate d} (h : W.Semantics)
    {x : Vec d} (hx : 0 ≤ x) : 0 ≤ W.observe x := by
  exact dot_nonneg h.weight_nonneg hx

theorem valid_semantics (W : Certificate d) (h : W.Valid) : W.Semantics := by
  rcases h with ⟨hB0, hB1, hseed, hweight, h00, h10, h20, h01, h11,
    h21, hbase0, hbase1, hbase2, heven, hodd, hgap⟩
  refine {
    B0_nonneg := fun _ hx => Affine.eval_nonneg hB0 hx
    B1_nonneg := fun _ hx => Affine.eval_nonneg hB1 hx
    B0_mono := fun {_x _y} hxy => Affine.eval_mono hB0 hxy
    B1_mono := fun {_x _y} hxy => Affine.eval_mono hB1 hxy
    seed_nonneg := hseed
    weight_nonneg := hweight
    observe_mono := fun {_x _y} hxy => dot_mono_right hweight hxy
    recode00 := ?_
    recode10 := ?_
    recode20 := ?_
    recode01 := ?_
    recode11 := ?_
    recode21 := ?_
    base0 := hbase0
    base1 := hbase1
    base2 := hbase2
    even_rank := ?_
    odd_rank := ?_
  }
  · intro x hx
    simpa only [Affine.eval_comp] using Affine.coeffLE_eval_le h00 hx
  · intro x hx
    simpa only [Affine.eval_comp] using Affine.coeffLE_eval_le h10 hx
  · intro x hx
    simpa only [Affine.eval_comp] using Affine.coeffLE_eval_le h20 hx
  · intro x hx
    simpa only [Affine.eval_comp] using Affine.coeffLE_eval_le h01 hx
  · intro x hx
    simpa only [Affine.eval_comp] using Affine.coeffLE_eval_le h11 hx
  · intro x hx
    simpa only [Affine.eval_comp] using Affine.coeffLE_eval_le h21 hx
  · intro x hx
    change dot W.weight x ≤ dot W.weight (W.B0.eval x)
    rw [Affine.dot_eval]
    have hrow := dot_mono_left hx heven
    have hoff := dot_nonneg hweight hB0.2
    linarith
  · intro x hx
    change dot W.weight (W.G2.eval x) + 1 ≤ dot W.weight (W.B1.eval x)
    rw [Affine.dot_eval, Affine.dot_eval]
    have hrow := dot_mono_left hx hodd
    rw [dot_sub_right] at hgap
    linarith

end Certificate

end PoincareSecond
