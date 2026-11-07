import Mathlib

/-!
Erdos #687: finite primorial survivor certificates and Hankel noncollapse.
Candidate for Lean 4.34.0-rc1 / pinned Mathlib cached CI.
No new prime-gap estimate is assumed or established.
All root arithmetic premises are visible in the theorem statements.
-/

namespace Erdos687

/-- Surviving integers in the interval b + [1,T] modulo P. -/
def survivors (P b T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 T).filter (fun n => Nat.Coprime (b + n) P)

/-- Nonnegative power moments supported on those survivors. -/
def moment (P b T k : ℕ) : ℕ :=
  ∑ n ∈ survivors P b T, n ^ k

/-- The T × T Hankel moment matrix. -/
def hankel (P b T : ℕ) : Matrix (Fin T) (Fin T) ℕ :=
  fun i j => moment P b T (i.val + j.val)

theorem moment_zero (P b T : ℕ) :
    moment P b T 0 = (survivors P b T).card := by
  simp [moment]

theorem hankel_eq_zero_of_no_survivors (P b T : ℕ)
    (h : survivors P b T = ∅) : hankel P b T = 0 := by
  ext i j
  simp [hankel, moment, h]

/-- The exact spectral noncollapse endpoint. T > 0 supplies index 0. -/
theorem hankel_ne_zero_iff_card_pos (P b T : ℕ) (hT : 0 < T) :
    hankel P b T ≠ 0 ↔ 0 < (survivors P b T).card := by
  constructor
  · intro hne
    by_contra hnot
    have hcard : (survivors P b T).card = 0 := by omega
    have hempty : survivors P b T = ∅ := Finset.card_eq_zero.mp hcard
    exact hne (hankel_eq_zero_of_no_survivors P b T hempty)
  · intro hpos hzero
    have hentry : moment P b T 0 = 0 := by
      have h := congrArg
        (fun M : Matrix (Fin T) (Fin T) ℕ => M ⟨0, hT⟩ ⟨0, hT⟩)
        hzero
      simpa [hankel] using h
    rw [moment_zero] at hentry
    omega

/-- A computable exhaustive finite checker using gcd and finite ranges. -/
def check (P T : ℕ) : Bool :=
  decide (∀ b ∈ Finset.range P, 0 < (survivors P b T).card)

theorem check_iff_card_pos (P T : ℕ) :
    check P T = true ↔ ∀ b < P, 0 < (survivors P b T).card := by
  simp [check]

theorem check_iff_hankel_nonzero (P T : ℕ) (hT : 0 < T) :
    check P T = true ↔ ∀ b < P, hankel P b T ≠ 0 := by
  constructor
  · intro hc b hb
    exact (hankel_ne_zero_iff_card_pos P b T hT).mpr
      ((check_iff_card_pos P T).mp hc b hb)
  · intro hh
    apply (check_iff_card_pos P T).mpr
    intro b hb
    exact (hankel_ne_zero_iff_card_pos P b T hT).mp (hh b hb)

/-- Every block of T consecutive integers has a unit modulo P. -/
def good (P T : ℕ) : Prop :=
  ∀ b < P, ∃ n : ℕ, 1 ≤ n ∧ n ≤ T ∧ Nat.Coprime (b + n) P

theorem check_iff_good (P T : ℕ) :
    check P T = true ↔ good P T := by
  constructor
  · intro hc b hb
    obtain ⟨n, hn⟩ :=
      Finset.card_pos.mp ((check_iff_card_pos P T).mp hc b hb)
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hcop⟩
    rcases Finset.mem_Icc.mp hnIcc with ⟨h1, h2⟩
    exact ⟨n, h1, h2, hcop⟩
  · intro hg
    apply (check_iff_card_pos P T).mpr
    intro b hb
    obtain ⟨n, h1, h2, hc⟩ := hg b hb
    apply Finset.card_pos.mpr
    exact ⟨n, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, hc⟩⟩

theorem good_mono {P T U : ℕ} (hTU : T ≤ U) :
    good P T → good P U := by
  intro hg b hb
  obtain ⟨n, h1, h2, hc⟩ := hg b hb
  exact ⟨n, h1, le_trans h2 hTU, hc⟩

theorem check_mono {P T U : ℕ} (hTU : T ≤ U)
    (hc : check P T = true) : check P U = true := by
  exact (check_iff_good P U).mpr
    (good_mono hTU ((check_iff_good P T).mp hc))

/-- Elementary periodic upper bound; independent of any conjecture. -/
theorem good_self (P : ℕ) (hP : 0 < P) : good P P := by
  intro b hb
  by_cases hb0 : b = 0
  · refine ⟨1, by omega, by omega, ?_⟩
    simp [hb0]
  · refine ⟨P - b + 1, by omega, by omega, ?_⟩
    have hsum : b + (P - b + 1) = P + 1 := by omega
    rw [hsum]
    simpa [Nat.add_comm] using
      (show Nat.Coprime (1 + P) P by simp)

theorem check_self (P : ℕ) (hP : 0 < P) : check P P = true :=
  (check_iff_good P P).mpr (good_self P hP)

theorem check_zero_false (P : ℕ) (hP : 0 < P) :
    check P 0 = false := by
  have hnot : check P 0 ≠ true := by
    intro hc
    obtain ⟨n, h1, h2, _⟩ :=
      (check_iff_good P 0).mp hc 0 hP
    omega
  cases h : check P 0 with
  | false => rfl
  | true => exact False.elim (hnot h)

/-- Largest bad length in a full period. It is a finite supremum. -/
def yMod (P : ℕ) : ℕ :=
  (Finset.range (P + 1)).sup
    (fun t : ℕ => if check P t = true then 0 else t)

theorem yMod_lt_of_check (P T : ℕ) (hP : 0 < P)
    (hc : check P T = true) : yMod P < T := by
  have hT : 0 < T := by
    by_contra hn
    have hz : T = 0 := by omega
    rw [hz] at hc
    have hf := check_zero_false P hP
    simp [hf] at hc
  have hbd : yMod P ≤ T - 1 := by
    unfold yMod
    apply Finset.sup_le
    intro t ht
    by_cases hlt : t < T
    · by_cases hct : check P t = true
      · simp [hct]
      · simp [hct]
        omega
    · have hTt : T ≤ t := by omega
      have hct : check P t = true := check_mono hTt hc
      simp [hct]
  omega

theorem check_of_yMod_lt (P T : ℕ) (hP : 0 < P)
    (hY : yMod P < T) : check P T = true := by
  by_cases hTP : T ≤ P
  · by_cases hc : check P T = true
    · exact hc
    · have hf : check P T = false := by
        cases h : check P T with
        | false => rfl
        | true => exact False.elim (hc h)
      have hmem : T ∈ Finset.range (P + 1) := by
        simp only [Finset.mem_range]
        omega
      have hle : T ≤ yMod P := by
        unfold yMod
        simpa [hf] using
          (Finset.le_sup (s := Finset.range (P + 1))
            (f := fun t : ℕ => if check P t = true then 0 else t) hmem)
      omega
  · have hPT : P ≤ T := by omega
    exact check_mono hPT (check_self P hP)

/-- Exact numerical gap/check equivalence for every length. -/
theorem yMod_lt_iff_check (P T : ℕ) (hP : 0 < P) :
    yMod P < T ↔ check P T = true := by
  exact ⟨check_of_yMod_lt P T hP, yMod_lt_of_check P T hP⟩

/-- Finite coordinate witness: one survivor for every residue class. -/
def verify (P T : ℕ) (W : Fin P → ℕ) : Bool :=
  decide (∀ b : Fin P,
    1 ≤ W b ∧ W b ≤ T ∧ Nat.Coprime (b.val + W b) P)

theorem verify_iff (P T : ℕ) (W : Fin P → ℕ) :
    verify P T W = true ↔
    ∀ b : Fin P, 1 ≤ W b ∧ W b ≤ T ∧
      Nat.Coprime (b.val + W b) P := by
  simp [verify]

theorem verify_sound (P T : ℕ) (W : Fin P → ℕ)
    (hv : verify P T W = true) : check P T = true := by
  apply (check_iff_good P T).mpr
  intro b hb
  let fb : Fin P := ⟨b, hb⟩
  have hw := (verify_iff P T W).mp hv fb
  exact ⟨W fb, hw.1, hw.2.1, hw.2.2⟩

theorem verify_complete (P T : ℕ) (hc : check P T = true) :
    ∃ W : Fin P → ℕ, verify P T W = true := by
  classical
  have hg : good P T := (check_iff_good P T).mp hc
  let W : Fin P → ℕ := fun b => Classical.choose (hg b.val b.isLt)
  refine ⟨W, ?_⟩
  apply (verify_iff P T W).mpr
  intro b
  exact Classical.choose_spec (hg b.val b.isLt)

/-- Exact finite-witness equivalence with the maximal gap. -/
theorem exists_verified_iff_yMod_lt (P T : ℕ) (hP : 0 < P) :
    (∃ W : Fin P → ℕ, verify P T W = true) ↔ yMod P < T := by
  constructor
  · rintro ⟨W, hv⟩
    exact (yMod_lt_iff_check P T hP).mpr (verify_sound P T W hv)
  · intro hY
    exact verify_complete P T ((yMod_lt_iff_check P T hP).mp hY)

/-- Primorial of primes up to x, with empty-product convention. -/
def primorial (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter Nat.Prime).prod id

theorem primorial_pos (x : ℕ) : 0 < primorial x := by
  unfold primorial
  apply Finset.prod_pos
  intro p hp
  exact ((Finset.mem_filter.mp hp).2).pos

/-- Jacobsthal maximal non-unit run for the primorial. -/
def erdosY (x : ℕ) : ℕ := yMod (primorial x)

/-- Executable finite checker for the prime interval endpoint. -/
def check687 (x T : ℕ) : Bool := check (primorial x) T

theorem check687_iff_y (x T : ℕ) :
    check687 x T = true ↔ erdosY x < T := by
  exact (yMod_lt_iff_check (primorial x) T (primorial_pos x)).symm

theorem check687_iff_hankel (x T : ℕ) (hT : 0 < T) :
    check687 x T = true ↔
    ∀ b < primorial x, hankel (primorial x) b T ≠ 0 := by
  exact check_iff_hankel_nonzero (primorial x) T hT

/-- Exact primorial finite-witness equivalence, no asymptotic admission. -/
theorem erdos687_finite_witness_iff (x T : ℕ) :
    (∃ W : Fin (primorial x) → ℕ,
      verify (primorial x) T W = true) ↔ erdosY x < T := by
  exact exists_verified_iff_yMod_lt (primorial x) T (primorial_pos x)

/-- The real-exponent threshold for arbitrary positive epsilon. -/
def threshold (ε : ℝ) (x : ℕ) : ℕ :=
  Nat.ceil ((x : ℝ) ^ (1 + ε))

/-- Unresolved uniform finite-checker acceptance premise. -/
def uniformAcceptance : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
    check687 x (threshold ε x) = true

/-- The Erdős #687 upper-exponent target for integer x. -/
def erdos687Target : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
    (erdosY x : ℝ) < (x : ℝ) ^ (1 + ε)

/-- Conditional root: uniform checker acceptance yields exponent inequality. -/
theorem uniformAcceptance_implies_erdos687
    (h : uniformAcceptance) : erdos687Target := by
  intro ε hε
  obtain ⟨X, hX⟩ := h ε hε
  refine ⟨X, ?_⟩
  intro x hx
  have hY : erdosY x < threshold ε x :=
    (check687_iff_y x (threshold ε x)).mp (hX x hx)
  exact (Nat.lt_ceil).mp hY

/-- Converse: no claim that the unresolved premise is discharged. -/
theorem erdos687_iff_uniformAcceptance :
    erdos687Target ↔ uniformAcceptance := by
  constructor
  · intro ht ε hε
    obtain ⟨X, hX⟩ := ht ε hε
    refine ⟨X, ?_⟩
    intro x hx
    exact (check687_iff_y x (threshold ε x)).mpr
      ((Nat.lt_ceil).mpr (hX x hx))
  · exact uniformAcceptance_implies_erdos687

end Erdos687
