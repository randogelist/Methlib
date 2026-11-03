import Mathlib.NumberTheory.Divisors

/-! A scoped finite-set reconstruction. The argument adapts Mathlib's
`disjoint_divisors_filter_isPrimePow` proof in `NumberTheory/Divisors.lean`
from the pinned revision, licensed under Apache 2.0. This candidate has not
yet been externally compiled or audited. -/

namespace HVRSimplePrimePowDisjoint

theorem disjoint_divisors {a b : ℕ} (hab : a.Coprime b) :
    Disjoint (a.divisors.filter IsPrimePow) (b.divisors.filter IsPrimePow) := by
  apply Finset.disjoint_left.mpr
  intro n hnA hnB
  have ha : n ∣ a := (Nat.mem_divisors.mp (Finset.mem_filter.mp hnA).1).1
  have hb : n ∣ b := (Nat.mem_divisors.mp (Finset.mem_filter.mp hnB).1).1
  have hpow : IsPrimePow n := (Finset.mem_filter.mp hnA).2
  exact hpow.ne_one (Nat.eq_one_of_dvd_coprimes hab ha hb)

end HVRSimplePrimePowDisjoint
