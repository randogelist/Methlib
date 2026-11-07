import RHShiftedHausdorff.NSEJoint.SingleModeWitness

set_option autoImplicit false
noncomputable section

namespace RHShiftedHausdorff.NSEJoint

open RH_HilbertLimit

structure MarginExclusion where
  K : ℕ
  N : ℕ
  j : ℕ
  hj : j ≤ N
  fail :
    bernsteinWeight actualShiftedMoment4 N j <
      singleModeMargin K N j

namespace MarginExclusion

theorem no_singleModeWitness
    (E : MarginExclusion) :
    ¬ ∃ W : SingleModeWitness, W.K = E.K := by
  rintro ⟨W, hWK⟩
  have hm := W.margin E.N E.j E.hj
  rw [hWK] at hm
  exact (not_lt_of_ge hm) E.fail

theorem no_accepted_kernel_certificate
    (E : MarginExclusion)
    (Q : SingleModeKernel)
    (c : Q.Cert)
    (hK : Q.K c = E.K) :
    Q.check c ≠ true := by
  intro hc
  have hm := Q.marginSound c hc E.N E.j E.hj
  rw [hK] at hm
  exact (not_lt_of_ge hm) E.fail

end MarginExclusion

structure MarginCrossoutDatabase where
  excluded : Finset ℕ
  certified :
    ∀ K : ℕ, K ∈ excluded →
      ∃ E : MarginExclusion, E.K = K

namespace MarginCrossoutDatabase

def excludedBool
    (DB : MarginCrossoutDatabase)
    (K : ℕ) : Bool :=
  decide (K ∈ DB.excluded)

theorem excludedBool_true_iff
    (DB : MarginCrossoutDatabase)
    (K : ℕ) :
    DB.excludedBool K = true ↔ K ∈ DB.excluded := by
  simp [excludedBool]

theorem no_accepted_at_excluded_K
    (DB : MarginCrossoutDatabase)
    (Q : SingleModeKernel)
    (K : ℕ)
    (hK : DB.excludedBool K = true) :
    ¬ ∃ c : Q.Cert, Q.K c = K ∧ Q.check c = true := by
  have hmem : K ∈ DB.excluded :=
    (DB.excludedBool_true_iff K).mp hK
  obtain ⟨E, hEK⟩ := DB.certified K hmem
  rintro ⟨c, hcK, hc⟩
  have hbad := E.no_accepted_kernel_certificate Q c
    (hcK.trans hEK.symm)
  exact hbad hc

def filteredCheck
    (DB : MarginCrossoutDatabase)
    (Q : SingleModeKernel)
    (c : Q.Cert) : Bool :=
  if DB.excludedBool (Q.K c) then false else Q.check c

theorem filteredCheck_true_implies_baseCheck
    (DB : MarginCrossoutDatabase)
    (Q : SingleModeKernel)
    (c : Q.Cert)
    (h : DB.filteredCheck Q c = true) :
    Q.check c = true := by
  unfold filteredCheck at h
  by_cases hx : DB.excludedBool (Q.K c) = true
  · simp [hx] at h
  · simpa [hx] using h

theorem baseCheck_true_implies_not_excluded
    (DB : MarginCrossoutDatabase)
    (Q : SingleModeKernel)
    (c : Q.Cert)
    (h : Q.check c = true) :
    DB.excludedBool (Q.K c) = false := by
  by_contra hx
  have hx' : DB.excludedBool (Q.K c) = true := by
    cases hval : DB.excludedBool (Q.K c) <;> simp_all
  have hnone := DB.no_accepted_at_excluded_K Q (Q.K c) hx'
  exact hnone ⟨c, rfl, h⟩

theorem filteredCheck_eq_baseCheck
    (DB : MarginCrossoutDatabase)
    (Q : SingleModeKernel)
    (c : Q.Cert) :
    DB.filteredCheck Q c = Q.check c := by
  by_cases h : Q.check c = true
  · have hx := DB.baseCheck_true_implies_not_excluded Q c h
    simp [filteredCheck, hx, h]
  · have hcfalse : Q.check c = false := by
      cases hq : Q.check c <;> simp_all
    by_cases hx : DB.excludedBool (Q.K c) = true
    · simp [filteredCheck, hx, hcfalse]
    · simp [filteredCheck, hx, hcfalse]

theorem filteredCheck_sound
    (DB : MarginCrossoutDatabase)
    (Q : SingleModeKernel)
    (c : Q.Cert)
    (h : DB.filteredCheck Q c = true) :
    _root_.RiemannHypothesis := by
  exact Q.check_sound c
    (DB.filteredCheck_true_implies_baseCheck Q c h)

structure Decoder (Q : SingleModeKernel) where
  decode : ByteArray → Option Q.Cert

def filteredVerify
    (DB : MarginCrossoutDatabase)
    (Q : SingleModeKernel)
    (D : Decoder Q)
    (blob : ByteArray) : Bool :=
  match D.decode blob with
  | none => false
  | some c => DB.filteredCheck Q c

theorem filteredVerify_sound
    (DB : MarginCrossoutDatabase)
    (Q : SingleModeKernel)
    (D : Decoder Q)
    (blob : ByteArray)
    (h : DB.filteredVerify Q D blob = true) :
    _root_.RiemannHypothesis := by
  unfold filteredVerify at h
  cases hdec : D.decode blob with
  | none =>
      simp [hdec] at h
  | some c =>
      have hc : DB.filteredCheck Q c = true := by
        simpa [hdec] using h
      exact DB.filteredCheck_sound Q c hc

end MarginCrossoutDatabase
end RHShiftedHausdorff.NSEJoint
