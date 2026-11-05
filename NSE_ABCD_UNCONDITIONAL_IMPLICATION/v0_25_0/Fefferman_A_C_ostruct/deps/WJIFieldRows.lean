import CondExpansion
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal
open scoped BigOperators
noncomputable section

/-- A subspace of actual spatial fields on which the heat and Newton-projected
transport operators are closed and have their usual algebraic laws. -/
structure JetOperatorDomain where
  space : Submodule ℝ RInitial
  profile_mem : profile ∈ space
  heat : space →ₗ[ℝ] space
  projected : space →ₗ[ℝ] space →ₗ[ℝ] space
  heat_eq : ∀ v : space, (heat v : RInitial) = heatStep v
  projected_eq : ∀ v w : space,
    (projected v w : RInitial) = projectedTransport v w

namespace JetOperatorDomain

variable (D : JetOperatorDomain)

private theorem heat_mem {v : RInitial} (hv : v ∈ D.space) : heatStep v ∈ D.space :=
  (D.heat_eq ⟨v, hv⟩) ▸ (D.heat ⟨v, hv⟩).property

private theorem projected_mem {v w : RInitial} (hv : v ∈ D.space) (hw : w ∈ D.space) :
    projectedTransport v w ∈ D.space :=
  (D.projected_eq ⟨v, hv⟩ ⟨w, hw⟩) ▸ (D.projected ⟨v, hv⟩ ⟨w, hw⟩).property

private theorem nextRow_mem (n : ℕ) (T : JetTable)
    (hT : ∀ j l, T j l ∈ D.space) (k : ℕ) : nextRow n T k ∈ D.space := by
  cases k with
  | zero => exact D.heat_mem (hT n 0)
  | succ r =>
    have fieldEq : nextRow n T (r+1) =
        heatStep (T n (r+1)) -
          ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) •
            ∑ l ∈ Finset.range (r+1),
              projectedTransport (T j l) (T (n-j) (r-l)) := by
      funext x i
      simp only [nextRow, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [fieldEq]
    apply D.space.sub_mem (D.heat_mem (hT n (r+1)))
    apply D.space.sum_mem
    intro j _
    apply D.space.smul_mem
    apply D.space.sum_mem
    intro l _
    exact D.projected_mem (hT j l) (hT (n-j) (r-l))

/-- All coefficient fields stay in the chosen operator domain, including the
zero columns above the amplitude degree of each row. -/
theorem jetTable_mem (n j k : ℕ) : jetTable n j k ∈ D.space := by
  induction n generalizing j k with
  | zero =>
    by_cases hk : k = 0
    · simpa [jetTable, hk] using D.profile_mem
    · simpa [jetTable, hk] using D.space.zero_mem
  | succ n ih =>
    by_cases hj : j = n+1
    · subst j
      by_cases hk : k ≤ n+1
      · simpa only [jetTable, if_pos rfl, if_true, if_pos hk] using
          (D.nextRow_mem n (jetTable n) ih k)
      · simpa only [jetTable, if_pos rfl, if_true, if_neg hk] using D.space.zero_mem
    · simpa only [jetTable, if_neg hj] using ih j k

theorem evalField_mem (c : ℝ) (n : ℕ) : evalField c n ∈ D.space := by
  rw [evalField_eq_row_sum c (le_refl n) (le_refl n)]
  exact D.space.sum_mem fun k _ => D.space.smul_mem _ (D.jetTable_mem n n k)

private def sample (x : RSpace) (i : Fin 3) : D.space →ₗ[ℝ] ℝ :=
  (LinearMap.proj i : RVector →ₗ[ℝ] ℝ).comp
    ((LinearMap.proj x : RInitial →ₗ[ℝ] RVector).comp D.space.subtype)

private theorem retract_of_mem {v : RInitial} (hv : v ∈ D.space) :
    D.space.subtype.leftInverse v = ⟨v, hv⟩ :=
  LinearMap.leftInverse_apply_of_inj D.space.ker_subtype (⟨v, hv⟩ : D.space)

private def ambientHeat (x : RSpace) (i : Fin 3) : RInitial →ₗ[ℝ] ℝ :=
  ((D.sample x i).comp D.heat).comp D.space.subtype.leftInverse

private theorem ambientHeat_agrees {v : RInitial} (hv : v ∈ D.space)
    (x : RSpace) (i : Fin 3) : D.ambientHeat x i v = heatStep v x i := by
  change (D.heat (D.space.subtype.leftInverse v) : RInitial) x i = _
  rw [D.retract_of_mem hv]
  exact congrFun (congrFun (D.heat_eq ⟨v, hv⟩) x) i

private def ambientProjected (x : RSpace) (i : Fin 3) : RInitial →ₗ[ℝ] RInitial →ₗ[ℝ] ℝ :=
  (D.projected.compr₂ (D.sample x i)).compl₁₂
    D.space.subtype.leftInverse D.space.subtype.leftInverse

private theorem ambientProjected_agrees {v w : RInitial}
    (hv : v ∈ D.space) (hw : w ∈ D.space) (x : RSpace) (i : Fin 3) :
    D.ambientProjected x i v w = projectedTransport v w x i := by
  change (D.projected (D.space.subtype.leftInverse v)
    (D.space.subtype.leftInverse w) : RInitial) x i = _
  rw [D.retract_of_mem hv, D.retract_of_mem hw]
  exact congrFun (congrFun (D.projected_eq ⟨v, hv⟩ ⟨w, hw⟩) x) i

include D

theorem heatRowLinearity (δ : ℝ) : HeatRowLinearity δ := by
  intro c _ n x i
  exact ⟨D.ambientHeat x i, D.ambientHeat_agrees (D.evalField_mem c n) x i,
    fun l _ => D.ambientHeat_agrees (D.jetTable_mem n n l) x i⟩

theorem projectedRowBilinearity (δ : ℝ) : ProjectedRowBilinearity δ := by
  intro c _ n j _ x i
  refine ⟨D.ambientProjected x i,
    D.ambientProjected_agrees (D.evalField_mem c j) (D.evalField_mem c (n-j)) x i, ?_⟩
  intro l _ r _
  exact D.ambientProjected_agrees (D.jetTable_mem n j l) (D.jetTable_mem n (n-j) r) x i

theorem finiteExpansionLaw (δ : ℝ) : FiniteExpansionLaw δ :=
  finiteExpansionLaw_of_row_operators (D.heatRowLinearity δ) (D.projectedRowBilinearity δ)

end JetOperatorDomain
end
end CondFeffA
