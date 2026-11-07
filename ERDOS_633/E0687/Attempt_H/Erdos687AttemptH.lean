import Mathlib

/-!
Attempt_H: sifted Toda finite-checker implication.
Unconditional arithmetic lemmas; spectral separation explicitly hypothesized.
-/
namespace Erdos687AttemptH

def gap (r : ℕ → ℕ) (i : ℕ) : ℕ := r (i + 1) - r i

def maxGap (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => max (maxGap r m) (gap r m)

def siftedY (r : ℕ → ℕ) (m : ℕ) : ℕ := maxGap r m - 1

theorem maxGap_le_iff (r : ℕ → ℕ) (m L : ℕ) :
    maxGap r m ≤ L ↔ ∀ i, i < m → gap r i ≤ L := by
  induction m with
  | zero => simp [maxGap]
  | succ m ih =>
      constructor
      · intro h i hi
        have hh : maxGap r m ≤ L ∧ gap r m ≤ L := (max_le_iff).mp h
        by_cases heq : i = m
        · simpa [heq] using hh.2
        · exact (ih.mp hh.1) i (by omega)
      · intro h
        have h0 : maxGap r m ≤ L :=
          ih.mpr (by intro i hi; exact h i (by omega))
        have h1 : gap r m ≤ L := h m (by omega)
        change max (maxGap r m) (gap r m) ≤ L
        exact max_le h0 h1

def gapCheck (r : ℕ → ℕ) (m L : ℕ) : Bool :=
  (List.range m).all (fun i => decide (gap r i ≤ L))

theorem gapCheck_iff (r : ℕ → ℕ) (m L : ℕ) :
    gapCheck r m L = true ↔ ∀ i, i < m → gap r i ≤ L := by
  simp [gapCheck, List.all_eq_true, List.mem_range]

theorem gapCheck_iff_siftedY (r : ℕ → ℕ) (m L : ℕ)
    (hL : 1 ≤ L) (hpos : 1 ≤ maxGap r m) :
    gapCheck r m L = true ↔ siftedY r m ≤ L - 1 := by
  rw [gapCheck_iff]
  constructor
  · intro h
    have hm : maxGap r m ≤ L := (maxGap_le_iff r m L).mpr h
    dsimp [siftedY]
    omega
  · intro h
    apply (maxGap_le_iff r m L).mp
    dsimp [siftedY] at h
    omega

def prefix (r : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => prefix r n + r n

theorem prefix_second_difference (r : ℕ → ℤ) (n : ℕ) :
    prefix r (n + 2) + prefix r n - 2 * prefix r (n + 1)
      = r (n + 1) - r n := by
  change (prefix r (n + 1) + r (n + 1)) + prefix r n -
    2 * (prefix r n + r n) = r (n + 1) - r n
  ring

def sampleCheck (m b L : ℕ) (a d : ℕ → ℚ) : Bool :=
  (List.range m).all
    (fun i => decide (d i < a i * (2 : ℚ) ^ (4 * b * L + 2 * b)))

theorem sampleCheck_iff (m b L : ℕ) (a d : ℕ → ℚ) :
    sampleCheck m b L a d = true ↔
      ∀ i, i < m → d i < a i * (2 : ℚ) ^ (4 * b * L + 2 * b) := by
  simp [sampleCheck, List.all_eq_true, List.mem_range]

structure SeparationMargin (r : ℕ → ℕ) (m b : ℕ)
    (a d : ℕ → ℚ) : Prop where
  nonneg : ∀ i, i < m → 0 ≤ a i
  lower : ∀ i, i < m →
    d i < a i * (2 : ℚ) ^ (4 * b * gap r i + b)
  upper : ∀ i, i < m →
    a i * (2 : ℚ) ^ (4 * b * gap r i) < d i * (2 : ℚ) ^ b

theorem threshold_iff_gap (b g L : ℕ) (a d : ℚ)
    (ha : 0 ≤ a)
    (hlo : d < a * (2 : ℚ) ^ (4 * b * g + b))
    (hhi : a * (2 : ℚ) ^ (4 * b * g) < d * (2 : ℚ) ^ b) :
    d < a * (2 : ℚ) ^ (4 * b * L + 2 * b) ↔ g ≤ L := by
  constructor
  · intro htest
    by_contra hnot
    have hg : L + 1 ≤ g := by omega
    have hmul : (4 * b) * (L + 1) ≤ (4 * b) * g :=
      Nat.mul_le_mul_left (4 * b) hg
    have hexp : 4 * b * L + 2 * b + b ≤ 4 * b * g := by
      nlinarith [hmul]
    have hpow :
        (2 : ℚ) ^ (4 * b * L + 2 * b + b) ≤ (2 : ℚ) ^ (4 * b * g) :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hscaled :
        a * (2 : ℚ) ^ (4 * b * L + 2 * b + b) ≤
          a * (2 : ℚ) ^ (4 * b * g) :=
      mul_le_mul_of_nonneg_left hpow ha
    have hlt :
        a * (2 : ℚ) ^ (4 * b * L + 2 * b + b) <
          d * (2 : ℚ) ^ b := lt_of_le_of_lt hscaled hhi
    have hfactor :
        (2 : ℚ) ^ (4 * b * L + 2 * b + b) =
          (2 : ℚ) ^ (4 * b * L + 2 * b) * (2 : ℚ) ^ b := by
      rw [pow_add]
    rw [hfactor] at hlt
    have hp : (0 : ℚ) < (2 : ℚ) ^ b := by positivity
    have hbad : a * (2 : ℚ) ^ (4 * b * L + 2 * b) < d := by
      apply (mul_lt_mul_right hp).mp
      simpa only [mul_assoc] using hlt
    linarith
  · intro hg
    have hmul : (4 * b) * g ≤ (4 * b) * L :=
      Nat.mul_le_mul_left (4 * b) hg
    have hexp : 4 * b * g + b ≤ 4 * b * L + 2 * b := by
      nlinarith [hmul]
    have hpow :
        (2 : ℚ) ^ (4 * b * g + b) ≤
          (2 : ℚ) ^ (4 * b * L + 2 * b) :=
      pow_le_pow_right₀ (by norm_num) hexp
    exact lt_of_lt_of_le hlo (mul_le_mul_of_nonneg_left hpow ha)

theorem sampleCheck_iff_gapCheck (r : ℕ → ℕ) (m b L : ℕ)
    (a d : ℕ → ℚ) (h : SeparationMargin r m b a d) :
    sampleCheck m b L a d = true ↔ gapCheck r m L = true := by
  rw [sampleCheck_iff, gapCheck_iff]
  constructor
  · intro hs i hi
    exact (threshold_iff_gap b (gap r i) L (a i) (d i)
      (h.nonneg i hi) (h.lower i hi) (h.upper i hi)).mp (hs i hi)
  · intro hg i hi
    exact (threshold_iff_gap b (gap r i) L (a i) (d i)
      (h.nonneg i hi) (h.lower i hi) (h.upper i hi)).mpr (hg i hi)

theorem certified_sample_iff_siftedY (r : ℕ → ℕ) (m b L : ℕ)
    (a d : ℕ → ℚ) (h : SeparationMargin r m b a d)
    (hL : 1 ≤ L) (hpos : 1 ≤ maxGap r m) :
    sampleCheck m b L a d = true ↔ siftedY r m ≤ L - 1 := by
  exact (sampleCheck_iff_gapCheck r m b L a d h).trans
    (gapCheck_iff_siftedY r m L hL hpos)

structure SiftedPeriod (P m : ℕ) where
  residue : ℕ → ℕ
  strict : StrictMono residue
  first : residue 0 = 1
  last : residue m = P + 1
  sound : ∀ j, j ≤ m → Nat.Coprime (residue j) P
  complete : ∀ k, 1 ≤ k → k ≤ P + 1 →
    Nat.Coprime k P → ∃ j, j ≤ m ∧ residue j = k

theorem SiftedPeriod.interior_not_coprime {P m : ℕ}
    (S : SiftedPeriod P m) (i k : ℕ)
    (hi : i < m) (hl : S.residue i < k)
    (hr : k < S.residue (i + 1)) : ¬ Nat.Coprime k P := by
  intro hc
  have hleft : S.residue 0 ≤ S.residue i :=
    S.strict.monotone (Nat.zero_le i)
  have hright : S.residue (i + 1) ≤ S.residue m :=
    S.strict.monotone (by omega)
  have hk1 : 1 ≤ k := by rw [S.first] at hleft; omega
  have hkP : k ≤ P + 1 := by rw [S.last] at hright; omega
  obtain ⟨j, hj, hkj⟩ := S.complete k hk1 hkP hc
  have hjcases : j ≤ i ∨ i + 1 ≤ j := by omega
  rcases hjcases with hji | hij
  · have hle : S.residue j ≤ S.residue i := S.strict.monotone hji
    omega
  · have hle : S.residue (i + 1) ≤ S.residue j := S.strict.monotone hij
    omega

theorem SiftedPeriod.maxGap_pos {P m : ℕ}
    (S : SiftedPeriod P m) (hm : 0 < m) :
    0 < maxGap S.residue m := by
  by_contra h
  have hm0 : maxGap S.residue m ≤ 0 := by omega
  have hgap := (maxGap_le_iff S.residue m 0).mp hm0 0 hm
  have hstrict : S.residue 0 < S.residue 1 := S.strict (by omega)
  unfold gap at hgap
  omega

def siftedResidues (P : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (P + 1)).filter (fun z => Nat.Coprime z P)

def squaredVandermonde (I : Finset ℕ) : ℕ :=
  ∏ u ∈ I, ∏ v ∈ I.filter (fun v => u < v), (v - u) ^ 2

def tauExpansion (P n : ℕ) (q : ℚ) : ℚ :=
  ∑ I ∈ Finset.powersetCard n (siftedResidues P),
    (squaredVandermonde I : ℚ) * q ^ (I.sum id)

def sampleQ (b : ℕ) : ℚ := 1 / (2 : ℚ) ^ (4 * b)
def tauNumerator (P b i : ℕ) : ℚ :=
  tauExpansion P (i + 2) (sampleQ b) * tauExpansion P i (sampleQ b)
def tauDenominator (P b i : ℕ) : ℚ :=
  (tauExpansion P (i + 1) (sampleQ b)) ^ 2

def curvatureCheck (P m b L : ℕ) : Bool :=
  sampleCheck m b L (tauNumerator P b) (tauDenominator P b)

def CertifiedCurvatureMargin (P m b : ℕ) (r : ℕ → ℕ) : Prop :=
  SeparationMargin r m b (tauNumerator P b) (tauDenominator P b)

theorem curvatureCheck_iff_certifiedPeriod {P m b L : ℕ}
    (S : SiftedPeriod P m) (hm : 0 < m) (hL : 1 ≤ L)
    (hmargin : CertifiedCurvatureMargin P m b S.residue) :
    curvatureCheck P m b L = true ↔ siftedY S.residue m ≤ L - 1 := by
  have hpos : 1 ≤ maxGap S.residue m := by
    have := S.maxGap_pos hm
    omega
  exact certified_sample_iff_siftedY S.residue m b L
    (tauNumerator P b) (tauDenominator P b) hmargin hL hpos

def primorialAt (x : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, p

def sampleBits (P : ℕ) : ℕ := Nat.size (2 * (P + 1) - 1)
def canonicalScale (P m : ℕ) : ℕ :=
  4 * (m + 1) ^ 2 * sampleBits P

def erdosPrimeCheck (x m L : ℕ) : Bool :=
  let P := primorialAt x
  curvatureCheck P m (canonicalScale P m) L

theorem erdosPrimeCheck_iff_certifiedPeriod (x m L : ℕ)
    (S : SiftedPeriod (primorialAt x) m)
    (hm : 0 < m) (hL : 1 ≤ L)
    (hmargin : CertifiedCurvatureMargin (primorialAt x) m
      (canonicalScale (primorialAt x) m) S.residue) :
    erdosPrimeCheck x m L = true ↔ siftedY S.residue m ≤ L - 1 := by
  exact curvatureCheck_iff_certifiedPeriod S hm hL hmargin

end Erdos687AttemptH
