import Bridge687
import Erdos687Spectral

open Filter Asymptotics

namespace MethlibErdos687.AttemptB

open Erdos687Spectral

/-- Positive finite sieve determinants, deduced from the pinned OpenAI
Jacobsthal quadratic theorem rather than introduced as a premise. -/
theorem jacobsthal_spectral_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, 0 < k →
        ∃ m : ℕ, (m : ℝ) ≤ C * (k : ℝ) ^ 2 ∧
          ∀ q : ℕ, 0 < q → q.primeFactors.card ≤ k →
            ∀ E : Finset ℤ, 0 < gramDet q m E := by
  rcases OAI.Erdos970.Erdos970Final.erdos_970_quadratic with
    ⟨C, hC, hBound⟩
  refine ⟨C, hC, ?_⟩
  intro k hk
  obtain ⟨m, hJacob, hm⟩ := hBound k hk
  refine ⟨m, hm, ?_⟩
  intro q hq hFactors E
  apply (gramDet_pos_iff q m E).2
  intro a ha
  obtain ⟨i, hi, hcop⟩ := hJacob q hq hFactors a
  exact (survivorCount_pos_iff q m a).2 ⟨i, hi, hcop⟩

/-- Spectral nonvanishing excludes all completely covered translated blocks. -/
theorem jacobsthal_no_cover :
    ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, 0 < k →
        ∃ m : ℕ, (m : ℝ) ≤ C * (k : ℝ) ^ 2 ∧
          ∀ q : ℕ, 0 < q → q.primeFactors.card ≤ k →
            ∀ a : ℤ, ¬ Covered q m a := by
  rcases jacobsthal_spectral_bound with ⟨C, hC, hBound⟩
  refine ⟨C, hC, ?_⟩
  intro k hk
  obtain ⟨m, hm, hSpectral⟩ := hBound k hk
  refine ⟨m, hm, ?_⟩
  intro q hq hFactors a hc
  have hpos : 0 < gramDet q m ({a} : Finset ℤ) :=
    hSpectral q hq hFactors {a}
  have hzero : gramDet q m ({a} : Finset ℤ) = 0 :=
    (gramDet_zero_iff_covered q m {a}).2 ⟨a, by simp, hc⟩
  linarith

/-- Formal-Conjectures Erdős 687 part (ii), via the pinned external
CRT/primorial/analytic bridge and the published OpenAI input. -/
theorem erdos_687_part_ii :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =o[atTop]
      (fun x : ℕ => (x : ℝ) ^ 2) :=
  Erdos687.erdos_687.parts.ii

/-- A quantitative external consequence stronger than little-o(x^2). -/
theorem erdos_687_quantitative :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x : ℝ) ^ 2 /
        (Real.log x * Real.log (Real.log x)) ^ 2) :=
  Erdos687.Y_isBigO

end MethlibErdos687.AttemptB
