import Bridge687
import FiniteCore

/-!
External Jacobsthal and Formal Conjectures #687 root.
The exact external proof is pinned by CI, not postulated as an axiom.
-/
set_option autoImplicit false
open Filter Asymptotics

namespace MethlibErdos687.AttemptF

/-- Direct proof import of the externally formalized Erdős #687 part (ii). -/
theorem external_part_ii :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =o[atTop]
      (fun x : ℕ => (x : ℝ) ^ 2) :=
  Erdos687.erdos_687.parts.ii

/-- Quantitative, externally proved improvement. -/
theorem external_quantitative :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x : ℝ) ^ 2 /
        (Real.log x * Real.log (Real.log x)) ^ 2) :=
  Erdos687.Y_isBigO

/-- Additional, uniform two-survivor consequence of the externally proved
Jacobsthal iterated-log theorem; the denominator remains exactly pinned. -/
theorem external_two_blocks :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      ∃ m : ℕ,
        (m : ℝ) ≤ C * (k : ℝ) ^ 2 /
          (Real.log (Real.log (3 * (k : ℝ)))) ^ 2 ∧
        ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
          ∀ a : ℤ, ∃ i j : ℕ, i < j ∧ j < 2 * m ∧
            (a + (i : ℤ)).natAbs.Coprime n ∧
            (a + (j : ℤ)).natAbs.Coprime n := by
  obtain ⟨C, hC, hAll⟩ :=
    OAI.Erdos970.Erdos970Final.erdos_970_iterated_log
  refine ⟨C, hC, ?_⟩
  intro k hk
  obtain ⟨m, hm, hmb⟩ := hAll k hk
  refine ⟨m, hmb, ?_⟩
  intro n hn hcard a
  exact two_blocks k m n hm hn hcard a

/-- Combined exact root. The only unresolved edge is hCRT,
not the external result or finite moment soundness. -/
theorem external_plus_certificate {P q y : ℕ}
    (hCRT : CRTDispersionBridge P q y)
    (hCert : (P - 1) * B P q y < (U P q y) ^ 2) :
    ((fun x : ℕ => (Erdos687.Y x : ℝ)) =o[atTop]
      (fun x : ℕ => (x : ℝ) ^ 2)) ∧
      ¬ FullyCovered (P * q) y :=
  ⟨external_part_ii, certificate_excludes_cover hCRT hCert⟩

end MethlibErdos687.AttemptF
