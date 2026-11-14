/-!
Erdős #687 / Methlib Attempt_J
Exact integer Gram propagation, discharged through the externally formalized
Jacobsthal-to-covering CRT theorem, and exact Formal Conjectures part (ii).

External source is *imported*, not assumed as an axiom:
  pw/erdosproblemaday-verification/.../Bridge687.lean
  openai/math OAI.NumberTheory.Jacobsthal.Main

All conclusions below are scoped. In particular, no claim is made that
Y(x) = O(x^(1+o(1))) has been proved.
-/
import Bridge687

open Filter Asymptotics

namespace MethlibErdos687.AttemptJ

/-- Integer Gram detector: unordered pairs in different residue classes. -/
def pairCount (A : Finset ℕ) (q : ℕ) : ℕ :=
  ((A.product A).filter
    (fun uv => uv.1 < uv.2 ∧ uv.1 % q ≠ uv.2 % q)).card

theorem pairCount_pos_iff (A : Finset ℕ) (q : ℕ) :
    0 < pairCount A q ↔
      ∃ u ∈ A, ∃ v ∈ A, u % q ≠ v % q := by
  unfold pairCount
  rw [Finset.card_pos]
  constructor
  · rintro ⟨⟨u, v⟩, hp⟩
    obtain ⟨hprod, huv⟩ := Finset.mem_filter.mp hp
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hprod
    exact ⟨u, hu, v, hv, huv.2⟩
  · rintro ⟨u, hu, v, hv, hdiff⟩
    rcases lt_trichotomy u v with huv | heq | hvu
    · exact ⟨(u, v), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hu, hv⟩, ⟨huv, hdiff⟩⟩⟩
    · subst v
      exact False.elim (hdiff rfl)
    · exact ⟨(v, u), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hv, hu⟩, ⟨hvu, hdiff.symm⟩⟩⟩

/-- Positive Gram count iff *every* deleted residue leaves a survivor. -/
theorem pairCount_pos_iff_universal (A : Finset ℕ) (q : ℕ) :
    0 < pairCount A q ↔
      ∀ b : ℕ, ∃ u ∈ A, u % q ≠ b % q := by
  rw [pairCount_pos_iff]
  constructor
  · rintro ⟨u, hu, v, hv, hdiff⟩ b
    by_cases hub : u % q = b % q
    · refine ⟨v, hv, ?_⟩
      intro hvb
      exact hdiff (hub.trans hvb.symm)
    · exact ⟨u, hu, hub⟩
  · intro h
    obtain ⟨u, hu, _⟩ := h 0
    obtain ⟨v, hv, hvu⟩ := h u
    exact ⟨u, hu, v, hv, hvu.symm⟩

/-- The same 1-indexed interval as the published Erdős #687 bridge. -/
def survivors (ps : Finset ℕ) (a : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 m).filter (fun i => ∀ p ∈ ps, i % p ≠ a p % p)

def noCover (ps : Finset ℕ) (m : ℕ) : Prop :=
  ∀ a : ℕ → ℕ, (survivors ps a m).Nonempty

/-- Exact one-modulus admission: an N→N+1 Gram equivalence. -/
theorem noCover_insert_iff_gram
    (ps : Finset ℕ) (q m : ℕ) (hq : q ∉ ps) :
    noCover (insert q ps) m ↔
      ∀ a : ℕ → ℕ, 0 < pairCount (survivors ps a m) q := by
  constructor
  · intro h a
    apply (pairCount_pos_iff_universal (survivors ps a m) q).2
    intro b
    let a' : ℕ → ℕ := fun p => if p = q then b else a p
    obtain ⟨i, hi⟩ := h a'
    obtain ⟨hiRange, hiAvoid⟩ := Finset.mem_filter.mp hi
    refine ⟨i, Finset.mem_filter.mpr ⟨hiRange, ?_⟩, ?_⟩
    · intro p hp
      have hpq : p ≠ q := by
        intro he
        exact hq (he ▸ hp)
      have h := hiAvoid p (Finset.mem_insert_of_mem hp)
      simpa [a', hpq] using h
    · have h := hiAvoid q (Finset.mem_insert_self q ps)
      simpa [a'] using h
  · intro h a
    obtain ⟨i, hi, hqAvoid⟩ :=
      (pairCount_pos_iff_universal (survivors ps a m) q).1 (h a) (a q)
    obtain ⟨hiRange, hiAvoid⟩ := Finset.mem_filter.mp hi
    refine ⟨i, Finset.mem_filter.mpr ⟨hiRange, ?_⟩⟩
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hqAvoid
    · exact hiAvoid p hp

/-- No new CRT hypothesis: the published external theorem
Erdos687.lt_of_covered has already discharged the Chinese remainder step. -/
theorem noCover_primes_of_jacobsthal
    (x k m : ℕ) (hk : Nat.primeCounting x ≤ k)
    (hm : OAI.Erdos970.NumberTheoryLean.Targets.IsJacobsthalBound k m) :
    noCover (Nat.primesLE x) m := by
  classical
  intro a
  by_contra hNot
  have hc : Green46.IsCoveredByResidues x m := by
    refine ⟨a, ?_⟩
    intro i hi
    by_contra hNone
    have hsur : i ∈ survivors (Nat.primesLE x) a m := by
      apply Finset.mem_filter.mpr
      constructor
      · exact hi
      · intro p hp hEq
        obtain ⟨hpx, hprime⟩ := Nat.mem_primesLE.mp hp
        apply hNone
        exact ⟨p, hpx, hprime, hEq⟩
    exact hNot ⟨i, hsur⟩
  exact (Nat.lt_irrefl m) (Erdos687.lt_of_covered hc hk hm)

/-- External Jacobsthal certificate implies robust positive Gram admission
at every prime q among the primes <= x. No semantic admission premise. -/
theorem gram_of_jacobsthal
    (x k m : ℕ) (hk : Nat.primeCounting x ≤ k)
    (hm : OAI.Erdos970.NumberTheoryLean.Targets.IsJacobsthalBound k m)
    (ps : Finset ℕ) (q : ℕ)
    (hps : ps ⊆ Nat.primesLE x) (hq : q ∈ Nat.primesLE x)
    (hqnot : q ∉ ps) :
    ∀ a : ℕ → ℕ, 0 < pairCount (survivors ps a m) q := by
  have hfull := noCover_primes_of_jacobsthal x k m hk hm
  have hins : noCover (insert q ps) m := by
    intro a
    obtain ⟨i, hi⟩ := hfull a
    obtain ⟨hiRange, hiAvoid⟩ := Finset.mem_filter.mp hi
    refine ⟨i, Finset.mem_filter.mpr ⟨hiRange, ?_⟩⟩
    intro p hp
    have hpfull : p ∈ Nat.primesLE x := by
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact hq
      · exact hps hp'
    exact hiAvoid p hpfull
  exact (noCover_insert_iff_gram ps q m hqnot).mp hins

/-- Uniform quadratic finite Gram witness, from external kernel-backed
Jacobsthal theorem and the external CRT bridge; no added axioms. -/
theorem quadratic_uniform_gram :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      ∃ m : ℕ, (m : ℝ) ≤ C * (k : ℝ) ^ 2 ∧
        ∀ x : ℕ, Nat.primeCounting x ≤ k →
          ∀ (ps : Finset ℕ) (q : ℕ),
            ps ⊆ Nat.primesLE x → q ∈ Nat.primesLE x → q ∉ ps →
              ∀ a : ℕ → ℕ, 0 < pairCount (survivors ps a m) q := by
  obtain ⟨C, hC, hK⟩ := OAI.Erdos970.Erdos970Final.erdos_970_quadratic
  refine ⟨C, hC, ?_⟩
  intro k hk
  obtain ⟨m, hm, hBound⟩ := hK k hk
  refine ⟨m, hBound, ?_⟩
  intro x hx ps q hps hq hqnot a
  exact (gram_of_jacobsthal x k m hx hm ps q hps hq hqnot) a

/-- Unconditional derivation of the exact externally verified
Formal Conjectures Erdős 687 part (ii), not the stronger open part (i). -/
theorem erdos_687_part_ii :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =o[atTop]
      (fun x : ℕ => (x : ℝ) ^ 2) :=
  Erdos687.erdos_687.parts.ii

/-- Externally verified stronger quantitative bound. -/
theorem erdos_687_quantitative :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x : ℝ) ^ 2 /
        (Real.log x * Real.log (Real.log x)) ^ 2) :=
  Erdos687.Y_isBigO

end MethlibErdos687.AttemptJ
