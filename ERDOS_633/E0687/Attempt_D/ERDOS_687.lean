/-!
Erdos #687, Attempt_D: finite two-scale sieve implication.
This file does NOT assert the still-open uniform sieve margin.
All quantified residue assignments are arbitrary functions Nat -> Nat.
-/
import Mathlib

namespace Erdos687AttemptD

def primesUpTo (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter Nat.Prime

def lowPrimes (x z : ℕ) : Finset ℕ :=
  (primesUpTo x).filter (fun p => p ≤ z)

def highPrimes (x z : ℕ) : Finset ℕ :=
  (primesUpTo x).filter (fun p => z < p)

theorem prime_partition (x z : ℕ) :
    lowPrimes x z ∪ highPrimes x z = primesUpTo x := by
  classical
  ext p
  simp only [lowPrimes, highPrimes, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  · intro hp
    rcases le_or_gt p z with hle | hgt
    · exact Or.inl ⟨hp, hle⟩
    · exact Or.inr ⟨hp, hgt⟩

def Avoids (S : Finset ℕ) (n : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ p ∈ S, n % p ≠ a p % p

def survivors (S : Finset ℕ) (y : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  (Finset.range y).filter (fun n => Avoids S n a)

def forbidden (p y : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  (Finset.range y).filter (fun n => n % p = a p % p)

def Covered (S : Finset ℕ) (y : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ n ∈ Finset.range y, ∃ p ∈ S, n % p = a p % p

/-- !! Every low-prime survivor must belong to a high-prime forbidden set
    if the combined set covers the interval. The reverse inequality
    therefore excludes complete coverage. -/
theorem finite_margin_excludes_cover (lo hi : Finset ℕ)
    (y : ℕ) (a : ℕ → ℕ)
    (hMargin : (∑ p ∈ hi, (forbidden p y a).card) <
      (survivors lo y a).card) :
    ¬ Covered (lo ∪ hi) y a := by
  classical
  intro hCover
  have hSub : survivors lo y a ⊆
      hi.biUnion (fun p => forbidden p y a) := by
    intro n hn
    obtain ⟨hRange, hAvoid⟩ := Finset.mem_filter.mp hn
    obtain ⟨p, hpUnion, hpHit⟩ := hCover n hRange
    rcases Finset.mem_union.mp hpUnion with hpLow | hpHigh
    · exact False.elim ((hAvoid p hpLow) hpHit)
    · exact Finset.mem_biUnion.mpr
        ⟨p, hpHigh, Finset.mem_filter.mpr ⟨hRange, hpHit⟩⟩
  have hCard1 : (survivors lo y a).card ≤
      (hi.biUnion (fun p => forbidden p y a)).card :=
    Finset.card_le_card hSub
  have hCard2 : (hi.biUnion (fun p => forbidden p y a)).card ≤
      ∑ p ∈ hi, (forbidden p y a).card :=
    Finset.card_biUnion_le
  exact (not_lt_of_ge (le_trans hCard1 hCard2)) hMargin

/-- ! Exact budget criterion, with separately named residue-count cap. -/
theorem finite_budget_excludes_cover (x z y : ℕ) (a : ℕ → ℕ)
    (hCap : ∀ p ∈ highPrimes x z,
      (forbidden p y a).card ≤ y / p + 1)
    (hBudget : (∑ p ∈ highPrimes x z, (y / p + 1)) <
      (survivors (lowPrimes x z) y a).card) :
    ¬ Covered (primesUpTo x) y a := by
  have hMargin :
      (∑ p ∈ highPrimes x z, (forbidden p y a).card) <
        (survivors (lowPrimes x z) y a).card := by
    calc
      (∑ p ∈ highPrimes x z, (forbidden p y a).card)
          ≤ ∑ p ∈ highPrimes x z, (y / p + 1) := by
              apply Finset.sum_le_sum
              intro p hp
              exact hCap p hp
      _ < (survivors (lowPrimes x z) y a).card := hBudget
  have hNo := finite_margin_excludes_cover
    (lowPrimes x z) (highPrimes x z) y a hMargin
  simpa only [prime_partition] using hNo

noncomputable def targetWidth (ε : ℝ) (x : ℕ) : ℕ :=
  Nat.ceil ((x : ℝ) ^ (1 + ε))

/-- The strong x^(1+o(1)) covering objective. NOT PROVED unconditionally. -/
def StrongNoCover : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X : ℕ,
    ∀ x : ℕ, X ≤ x → ∀ a : ℕ → ℕ,
      ¬ Covered (primesUpTo x) (targetWidth ε x) a

/-- OPEN analytic premise, stated transparently as a proposition. -/
def UniformExactMargin : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X : ℕ,
    ∀ x : ℕ, X ≤ x → ∀ a : ℕ → ℕ,
      (∑ p ∈ highPrimes x (9 * x / 10),
        (forbidden p (targetWidth ε x) a).card) <
        (survivors (lowPrimes x (9 * x / 10))
          (targetWidth ε x) a).card

/-- !! Conditional conclusion with exact, visible analytic dependency. -/
theorem strong_of_exact_margin
    (hMargin : UniformExactMargin) : StrongNoCover := by
  intro ε hε
  obtain ⟨X, hX⟩ := hMargin ε hε
  refine ⟨X, ?_⟩
  intro x hx a
  have hNo := finite_margin_excludes_cover
    (lowPrimes x (9 * x / 10))
    (highPrimes x (9 * x / 10))
    (targetWidth ε x) a (hX x hx a)
  simpa only [prime_partition] using hNo

/-- OPEN uniform budget; distinct from the exact margin. -/
def UniformShortBudget : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X : ℕ,
    ∀ x : ℕ, X ≤ x → ∀ a : ℕ → ℕ,
      (∑ p ∈ highPrimes x (9 * x / 10),
        (targetWidth ε x / p + 1)) <
        (survivors (lowPrimes x (9 * x / 10))
          (targetWidth ε x) a).card

def ResidueCountCap : Prop :=
  ∀ (p y : ℕ) (a : ℕ → ℕ),
    (forbidden p y a).card ≤ y / p + 1

theorem strong_of_short_budget
    (hCap : ResidueCountCap)
    (hBudget : UniformShortBudget) : StrongNoCover := by
  intro ε hε
  obtain ⟨X, hX⟩ := hBudget ε hε
  refine ⟨X, ?_⟩
  intro x hx a
  exact finite_budget_excludes_cover x (9 * x / 10)
    (targetWidth ε x) a
    (by
      intro p hp
      exact hCap p (targetWidth ε x) a)
    (hX x hx a)

#print axioms Erdos687AttemptD.prime_partition
#print axioms Erdos687AttemptD.finite_margin_excludes_cover
#print axioms Erdos687AttemptD.finite_budget_excludes_cover
#print axioms Erdos687AttemptD.strong_of_exact_margin
#print axioms Erdos687AttemptD.strong_of_short_budget

end Erdos687AttemptD
