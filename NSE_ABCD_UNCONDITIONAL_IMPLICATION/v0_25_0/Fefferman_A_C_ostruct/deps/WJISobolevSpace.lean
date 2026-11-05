import WJIDifferentialDomain
import WJILocalSlab

namespace CondFeffA.WJISobolev

open Fefferman Fefferman.ConcreteReal MeasureTheory WJISmooth
open scoped ContDiff
noncomputable section

/-- Scalar smooth representatives in L² ∩ L∞. -/
private def base : Submodule ℝ scalarSpace where
  carrier := {f | MemLp f.val 2 volume ∧ MemLp f.val ⊤ volume}
  zero_mem' := ⟨MemLp.zero, MemLp.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' c _ hf := ⟨hf.1.const_mul c, hf.2.const_mul c⟩

/-- Coordinate words up to order n, with every derivative in L² ∩ L∞. -/
def order : ℕ → Submodule ℝ scalarSpace
  | 0 => base
  | n+1 => order n ⊓ ⨅ i : Fin 3, (order n).comap (partialMap i)

private lemma order_succ {f : scalarSpace} {n : ℕ} :
    f ∈ order (n+1) ↔ f ∈ order n ∧ ∀ i : Fin 3, partialMap i f ∈ order n := by
  simp only [order, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]

/-- All-order regularity on actual scalar functions. -/
def scalar : Submodule ℝ (RSpace → ℝ) :=
  (⨅ n : ℕ, order n).map scalarSpace.subtype

private lemma mem_scalar {f : RSpace → ℝ} :
    f ∈ scalar ↔ ∃ g : scalarSpace, (∀ n : ℕ, g ∈ order n) ∧ g.val = f := by
  simp only [scalar, Submodule.mem_map, Submodule.mem_iInf, Submodule.subtype_apply]

theorem scalar_smooth {f : RSpace → ℝ} (hf : f ∈ scalar) : ContDiff ℝ ∞ f := by
  obtain ⟨g, _, rfl⟩ := mem_scalar.mp hf
  exact g.property

theorem scalar_memLp {f : RSpace → ℝ} (hf : f ∈ scalar) :
    MemLp f 2 volume ∧ MemLp f ⊤ volume := by
  obtain ⟨g, hg, rfl⟩ := mem_scalar.mp hf
  exact hg 0

theorem scalar_partial {f : RSpace → ℝ} (hf : f ∈ scalar) (i : Fin 3) :
    spatialDerivative i f ∈ scalar := by
  obtain ⟨g, hg, rfl⟩ := mem_scalar.mp hf
  exact mem_scalar.mpr ⟨partialMap i g, fun n => (order_succ.mp (hg (n+1))).2 i, rfl⟩

private lemma product_mem_order (n : ℕ) (f g : scalarSpace)
    (hf : f ∈ order n) (hg : g ∈ order n) : scalarProduct f g ∈ order n := by
  induction n generalizing f g with
  | zero =>
    change MemLp f.val 2 volume ∧ MemLp f.val ⊤ volume at hf
    change MemLp g.val 2 volume ∧ MemLp g.val ⊤ volume at hg
    exact ⟨hg.1.mul' hf.2, hg.2.mul' hf.2⟩
  | succ n ih =>
    obtain ⟨hf, hfD⟩ := order_succ.mp hf
    obtain ⟨hg, hgD⟩ := order_succ.mp hg
    refine order_succ.mpr ⟨ih f g hf hg, fun i => ?_⟩
    rw [partialMap_product]
    exact (order n).add_mem (ih f _ hf (hgD i)) (ih g _ hg (hfD i))

theorem scalar_mul {f g : RSpace → ℝ} (hf : f ∈ scalar) (hg : g ∈ scalar) :
    (fun x => f x * g x) ∈ scalar := by
  obtain ⟨u, hu, rfl⟩ := mem_scalar.mp hf
  obtain ⟨v, hv, rfl⟩ := mem_scalar.mp hg
  exact mem_scalar.mpr ⟨scalarProduct u v, fun n => product_mem_order n u v (hu n) (hv n), rfl⟩

private lemma schwartz_order (n : ℕ) (f : SchwartzMap RSpace ℝ) :
    (⟨(f : RSpace → ℝ), f.smooth'⟩ : scalarSpace) ∈ order n := by
  induction n generalizing f with
  | zero => exact ⟨f.memLp 2 volume, f.memLp_top volume⟩
  | succ n ih =>
    refine order_succ.mpr ⟨ih f, fun i => ?_⟩
    exact ih (SchwartzMap.evalCLM ℝ RSpace ℝ (basisDirection i) (SchwartzMap.fderivCLM ℝ RSpace ℝ f))

theorem schwartz_mem_scalar (f : SchwartzMap RSpace ℝ) : (f : RSpace → ℝ) ∈ scalar :=
  mem_scalar.mpr ⟨⟨(f : RSpace → ℝ), f.smooth'⟩, fun n => schwartz_order n f, rfl⟩

/-- Componentwise pointwise fields whose derivatives of all orders belong to L² ∩ L∞. -/
def space : Submodule ℝ RInitial where
  carrier := {v | ∀ i : Fin 3, (fun x => v x i) ∈ scalar}
  zero_mem' := fun _ => scalar.zero_mem
  add_mem' hv hw := fun i => scalar.add_mem (hv i) (hw i)
  smul_mem' c _ hv := fun i => scalar.smul_mem c (hv i)

theorem space_smooth : space ≤ WJISmooth.fieldSpace := fun _ hv i => scalar_smooth (hv i)

theorem datum_mem (c : ℝ) : datum c ∈ space := by
  intro i
  obtain ⟨f, hf⟩ := WJISlab.datum_schwartz c i
  rw [← hf]
  exact schwartz_mem_scalar f

theorem profile_mem : profile ∈ space := by
  have he : datum 1 = profile := by
    funext x i
    simp only [datum, one_mul]
  exact he ▸ datum_mem 1

theorem heat_mem (v : space) : heatStep v.val ∈ space := by
  intro i
  let f := fun x : RSpace => v.val x i
  have hf : f ∈ scalar := v.property i
  have hh (j : Fin 3) := scalar_partial (scalar_partial hf j) j
  exact scalar.add_mem (scalar.add_mem (hh 0) (hh 1)) (hh 2)

theorem transport_mem (v w : space) : transport v.val w.val ∈ space := by
  intro i
  have h (j : Fin 3) := scalar_mul (v.property j) (scalar_partial (w.property i) j)
  exact scalar.add_mem (scalar.add_mem (h 0) (h 1)) (h 2)

theorem memLp_coord (v : space) (i : Fin 3) :
    MemLp (fun x => v.val x i) 2 volume :=
  (scalar_memLp (v.property i)).1

theorem memLp_partial (v : space) (i j : Fin 3) :
    MemLp (spatialDerivative j (fun x => v.val x i)) 2 volume :=
  (scalar_memLp (scalar_partial (v.property i) j)).1

/-- On these continuous representatives the essential supremum is a pointwise bound. -/
theorem scalar_bounded {f : RSpace → ℝ} (hf : f ∈ scalar) : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M := by
  let M := lpNorm f ⊤ volume
  have hd : Dense {x : RSpace | ‖f x‖ ≤ M} :=
    Measure.dense_of_ae (ae_le_lpNorm_exponent_top (scalar_memLp hf).2)
  have hc : IsClosed {x : RSpace | ‖f x‖ ≤ M} :=
    isClosed_le (scalar_smooth hf).continuous.norm continuous_const
  exact ⟨M, fun x => hc.closure_subset (hd x)⟩

private lemma product_partial_integrable (f g : scalarSpace) (hf : f.val ∈ scalar)
    (hg : g.val ∈ scalar) (i : Fin 3) :
    Integrable (partialMap i (scalarProduct f g)).val := by
  rw [partialMap_product]
  have h1 : Integrable (fun x => f.val x * spatialDerivative i g.val x) :=
    memLp_one_iff_integrable.mp ((scalar_memLp (scalar_partial hg i)).1.mul' (scalar_memLp hf).1)
  have h2 : Integrable (fun x => g.val x * spatialDerivative i f.val x) :=
    memLp_one_iff_integrable.mp ((scalar_memLp (scalar_partial hf i)).1.mul' (scalar_memLp hg).1)
  exact h1.add h2

/-- The source of the literal Newton potential is in L¹. The product rule supplies
two L²×L² terms in each coordinate. -/
theorem transport_div_integrable (v w : space) : Integrable (fieldDiv (transport v.val w.val)) := by
  let C (z : space) (j : Fin 3) : scalarSpace :=
    ⟨fun x => z.val x j, scalar_smooth (z.property j)⟩
  let term (i j : Fin 3) := scalarProduct (C v j) (partialMap j (C w i))
  have hterm (i j : Fin 3) : Integrable (partialMap i (term i j)).val :=
    product_partial_integrable (C v j) (partialMap j (C w i))
      (v.property j) (scalar_partial (w.property i) j) i
  have hdiag (i : Fin 3) : Integrable (partialMap i (term i 0 + term i 1 + term i 2)).val := by
    rw [map_add, map_add]
    exact ((hterm i 0).add (hterm i 1)).add (hterm i 2)
  exact ((hdiag 0).add (hdiag 1)).add (hdiag 2)

/-- The same Newton source has a pointwise global bound. -/
theorem transport_div_bounded (v w : space) :
    ∃ M : ℝ, ∀ x, ‖fieldDiv (transport v.val w.val) x‖ ≤ M := by
  apply scalar_bounded
  have ht := transport_mem v w
  have hd (i : Fin 3) := scalar_partial (ht i) i
  exact scalar.add_mem (scalar.add_mem (hd 0) (hd 1)) (hd 2)

end
end CondFeffA.WJISobolev
