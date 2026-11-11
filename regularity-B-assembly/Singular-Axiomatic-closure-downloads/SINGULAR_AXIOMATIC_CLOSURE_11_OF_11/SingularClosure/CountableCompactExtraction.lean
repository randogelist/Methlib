import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Sequences

/-!
# One subsequence for a countable family of compact ranges

The index type may be the product of a time-horizon index and a Sobolev-order
index. The target spaces may depend on both indices. Compactness of each
coordinate range gives simultaneous convergence along a single increasing
subsequence. Continuous compatibility maps preserve the resulting limits.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace SingularClosure

theorem countable_compact_family_subsequence
    {ι : Type*} [Countable ι] {E : ι → Type*}
    [∀ i, TopologicalSpace (E i)] [∀ i, FirstCountableTopology (E i)]
    (F : ∀ i, ℕ → E i) (K : ∀ i, Set (E i))
    (hK : ∀ i, IsCompact (K i)) (hmem : ∀ i n, F i n ∈ K i) :
    ∃ u : ∀ i, E i, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ i, u i ∈ K i) ∧
      ∀ i, Tendsto (fun n => F i (φ n)) atTop (𝓝 (u i)) := by
  have hprod : IsCompact {u : ∀ i, E i | ∀ i, u i ∈ K i} :=
    isCompact_pi_infinite hK
  obtain ⟨u, hu, φ, hφ, hconv⟩ := hprod.tendsto_subseq
    (x := fun n i => F i n) (fun n i => hmem i n)
  refine ⟨u, φ, hφ, hu, ?_⟩
  intro i
  simpa only [Function.comp_def] using tendsto_pi_nhds.mp hconv i

theorem countable_precompact_family_subsequence
    {ι : Type*} [Countable ι] {E : ι → Type*}
    [∀ i, TopologicalSpace (E i)] [∀ i, FirstCountableTopology (E i)]
    (F : ∀ i, ℕ → E i)
    (hcompact : ∀ i, IsCompact (closure (Set.range (F i)))) :
    ∃ u : ∀ i, E i, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, Tendsto (fun n => F i (φ n)) atTop (𝓝 (u i)) := by
  obtain ⟨u, φ, hφ, _, hconv⟩ := countable_compact_family_subsequence F
    (fun i => closure (Set.range (F i))) hcompact
    (fun i n => subset_closure (Set.mem_range_self n))
  exact ⟨u, φ, hφ, hconv⟩

/-- Continuous restriction or Sobolev inclusion maps preserve the common limit. -/
theorem simultaneous_subsequence_limit_compatible
    {ι : Type*} {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
    (F : ∀ i, ℕ → E i) (u : ∀ i, E i) (φ : ℕ → ℕ)
    (hconv : ∀ i, Tendsto (fun n => F i (φ n)) atTop (𝓝 (u i)))
    (i j : ι) [T2Space (E j)] (R : E i → E j) (hR : Continuous R)
    (hcompat : ∀ n, R (F i n) = F j n) :
    R (u i) = u j := by
  have hmap : Tendsto (fun n => R (F i (φ n))) atTop (𝓝 (R (u i))) :=
    hR.continuousAt.tendsto.comp (hconv i)
  have hmap' : Tendsto (fun n => F j (φ n)) atTop (𝓝 (R (u i))) := by
    simpa only [hcompat] using hmap
  exact tendsto_nhds_unique hmap' (hconv j)

end SingularClosure
