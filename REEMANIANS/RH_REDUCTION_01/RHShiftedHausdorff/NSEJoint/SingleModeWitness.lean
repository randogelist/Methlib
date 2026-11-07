import RHShiftedHausdorff.NSEJoint.JointRH

set_option autoImplicit false
noncomputable section

namespace RHShiftedHausdorff.NSEJoint

open RH_HilbertLimit
open RH_HilbertLimit.TwoRoutes

def singleModeGeometric (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n

def singleModeScale (K : ℕ) : ℝ :=
  1 / (K : ℝ)

def singleModeMargin (K N j : ℕ) : ℝ :=
  singleModeScale K * ((Nat.choose N j : ℝ) * (1 / 2 : ℝ) ^ N)

def singleModeResidual (K : ℕ) (n : ℕ) : ℝ :=
  actualShiftedMoment4 n - singleModeScale K * singleModeGeometric n

theorem singleModeScale_nonneg
    (K : ℕ) (hK : 1 ≤ K) :
    0 ≤ singleModeScale K := by
  have hKposNat : 0 < K := lt_of_lt_of_le Nat.zero_lt_one hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast hKposNat
  exact (one_div_pos.mpr hKpos).le

theorem singleModeGeometric_bernsteinPositive :
    BernsteinPositive singleModeGeometric := by
  unfold singleModeGeometric
  exact geometric_bernsteinPositive (by norm_num) (by norm_num)

theorem bernsteinWeight_sub_smul
    (u v : ℕ → ℝ) (a : ℝ) (N j : ℕ) :
    bernsteinWeight (fun n => u n - a * v n) N j =
      bernsteinWeight u N j - a * bernsteinWeight v N j := by
  have hfun :
      (fun n => u n - a * v n) =
        (fun n => u n + (-a) * v n) := by
    funext n
    ring
  rw [hfun, bernsteinWeight_add, bernsteinWeight_smul]
  ring

theorem bernsteinWeight_singleModeGeometric
    (N j : ℕ) (hj : j ≤ N) :
    bernsteinWeight singleModeGeometric N j =
      (Nat.choose N j : ℝ) * (1 / 2 : ℝ) ^ N := by
  unfold singleModeGeometric
  rw [bernsteinWeight_geometric]
  have hhalf : (1 : ℝ) - (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
    norm_num
  rw [hhalf]
  have hpow :
      (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (N - j) =
        (1 / 2 : ℝ) ^ N := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  calc
    (Nat.choose N j : ℝ) * (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (N - j) =
        (Nat.choose N j : ℝ) *
          ((1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (N - j)) := by
      ring
    _ = (Nat.choose N j : ℝ) * (1 / 2 : ℝ) ^ N := by
      rw [hpow]

structure SingleModeWitness where
  K : ℕ
  hK : 1 ≤ K
  margin :
    ∀ N j : ℕ, j ≤ N →
      singleModeMargin K N j ≤
        bernsteinWeight actualShiftedMoment4 N j

namespace SingleModeWitness

theorem residual_bernsteinPositive
    (W : SingleModeWitness) :
    BernsteinPositive (singleModeResidual W.K) := by
  intro N j hj
  change 0 ≤
    bernsteinWeight
      (fun n =>
        actualShiftedMoment4 n -
          singleModeScale W.K * singleModeGeometric n) N j
  rw [bernsteinWeight_sub_smul]
  rw [bernsteinWeight_singleModeGeometric N j hj]
  exact sub_nonneg.mpr (W.margin N j hj)

theorem scaled_reference_bernsteinPositive
    (W : SingleModeWitness) :
    BernsteinPositive
      (fun n => singleModeScale W.K * singleModeGeometric n) := by
  exact bernsteinPositive_smul
    (singleModeScale_nonneg W.K W.hK)
    singleModeGeometric_bernsteinPositive

theorem shifted_eq_residual_add_reference
    (W : SingleModeWitness) :
    actualShiftedMoment4 =
      (fun n =>
        singleModeResidual W.K n +
          singleModeScale W.K * singleModeGeometric n) := by
  funext n
  unfold singleModeResidual
  ring

theorem shifted_bernsteinPositive
    (W : SingleModeWitness) :
    BernsteinPositive actualShiftedMoment4 := by
  have hres := W.residual_bernsteinPositive
  have href := W.scaled_reference_bernsteinPositive
  have hadd := bernsteinPositive_add hres href
  rw [W.shifted_eq_residual_add_reference]
  exact hadd

theorem nativeRH
    (W : SingleModeWitness) :
    _root_.RiemannHypothesis := by
  exact actual_shifted_bernsteinPositive_implies_nativeRH
    W.shifted_bernsteinPositive

end SingleModeWitness

structure SingleModeKernel where
  Cert : Type
  K : Cert → ℕ
  check : Cert → Bool
  positiveK :
    ∀ c : Cert,
      check c = true →
      1 ≤ K c
  marginSound :
    ∀ c : Cert,
      check c = true →
      ∀ N j : ℕ, j ≤ N →
        singleModeMargin (K c) N j ≤
          bernsteinWeight actualShiftedMoment4 N j

namespace SingleModeKernel

def witnessOfAccepted
    (Q : SingleModeKernel)
    (c : Q.Cert)
    (h : Q.check c = true) :
    SingleModeWitness where
  K := Q.K c
  hK := Q.positiveK c h
  margin := Q.marginSound c h

theorem check_sound
    (Q : SingleModeKernel)
    (c : Q.Cert)
    (h : Q.check c = true) :
    _root_.RiemannHypothesis := by
  exact (Q.witnessOfAccepted c h).nativeRH

structure Decoder (Q : SingleModeKernel) where
  decode : ByteArray → Option Q.Cert

def verify
    (Q : SingleModeKernel)
    (D : Decoder Q)
    (blob : ByteArray) : Bool :=
  match D.decode blob with
  | none => false
  | some c => Q.check c

theorem verify_sound
    (Q : SingleModeKernel)
    (D : Decoder Q)
    (blob : ByteArray)
    (h : verify Q D blob = true) :
    _root_.RiemannHypothesis := by
  unfold verify at h
  cases hdec : D.decode blob with
  | none =>
      simp [hdec] at h
  | some c =>
      have hc : Q.check c = true := by
        simpa [hdec] using h
      exact Q.check_sound c hc

end SingleModeKernel
end RHShiftedHausdorff.NSEJoint
