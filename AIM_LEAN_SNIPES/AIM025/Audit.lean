import Lean.Util.CollectAxioms
import Lean.Elab.Command
import AIM025CholletNonnegative

/-!
External native Lean 4.33.0 evidence module.
Each prepared theorem receives one complete signature and one kernel-derived
axiom-dependency report. This file itself supplies no compiler evidence.
-/

set_option pp.universes true

#check @AIM025.mass_mul_eq_diagonal_add_offDiagonal
#print axioms AIM025.mass_mul_eq_diagonal_add_offDiagonal

#check @AIM025.mass_mul_sub_diagonal_eq_offDiagonal
#print axioms AIM025.mass_mul_sub_diagonal_eq_offDiagonal

#check @AIM025.mass_nonneg
#print axioms AIM025.mass_nonneg

#check @AIM025.diagonalPair_nonneg
#print axioms AIM025.diagonalPair_nonneg

#check @AIM025.offDiagonalPair_nonneg
#print axioms AIM025.offDiagonalPair_nonneg

#check @AIM025.diagonalPair_le_mass_mul
#print axioms AIM025.diagonalPair_le_mass_mul

#check @AIM025.mass_eq_zero_iff
#print axioms AIM025.mass_eq_zero_iff

#check @AIM025.exists_pos_of_mass_ne_zero
#print axioms AIM025.exists_pos_of_mass_ne_zero

#check @AIM025.offDiagonalPair_eq_zero_iff
#print axioms AIM025.offDiagonalPair_eq_zero_iff

#check @AIM025.offDiagonalPair_eq_zero_iff_zero_or_commonUnique
#print axioms AIM025.offDiagonalPair_eq_zero_iff_zero_or_commonUnique

#check @AIM025.normalized_nonneg
#print axioms AIM025.normalized_nonneg

#check @AIM025.mass_normalized
#print axioms AIM025.mass_normalized

#check @AIM025.normalized_overlap
#print axioms AIM025.normalized_overlap

#check @AIM025.normalized_overlap_le_one
#print axioms AIM025.normalized_overlap_le_one

#check @AIM025.permanent_eq_mass_permTerm
#print axioms AIM025.permanent_eq_mass_permTerm

#check @AIM025.permTerm_nonneg
#print axioms AIM025.permTerm_nonneg

#check @AIM025.permanent_nonneg
#print axioms AIM025.permanent_nonneg

#check @AIM025.permTerm_hadamard
#print axioms AIM025.permTerm_hadamard

#check @AIM025.permanent_hadamard_eq_diagonalPair
#print axioms AIM025.permanent_hadamard_eq_diagonalPair

#check @AIM025.cholletGap_eq_offDiagonal
#print axioms AIM025.cholletGap_eq_offDiagonal

#check @AIM025.cholletGap_nonneg
#print axioms AIM025.cholletGap_nonneg

#check @AIM025.permanent_hadamard_le
#print axioms AIM025.permanent_hadamard_le

#check @AIM025.cholletGap_eq_zero_iff_crossTerms
#print axioms AIM025.cholletGap_eq_zero_iff_crossTerms

#check @AIM025.cholletGap_eq_zero_iff
#print axioms AIM025.cholletGap_eq_zero_iff

#check @AIM025.permanent_hadamard_eq_iff
#print axioms AIM025.permanent_hadamard_eq_iff

#check @AIM025.cholletGap_eq_zero_iff_commonUnique
#print axioms AIM025.cholletGap_eq_zero_iff_commonUnique

#check @AIM025.permutationDistribution_eq_normalized
#print axioms AIM025.permutationDistribution_eq_normalized

#check @AIM025.permutationDistribution_nonneg
#print axioms AIM025.permutationDistribution_nonneg

#check @AIM025.permutationDistribution_sum
#print axioms AIM025.permutationDistribution_sum

#check @AIM025.normalized_permanent_overlap
#print axioms AIM025.normalized_permanent_overlap

#check @AIM025.normalized_cholletGap
#print axioms AIM025.normalized_cholletGap

#check @AIM025.permutation_overlap_bounds
#print axioms AIM025.permutation_overlap_bounds

#check @AIM025.permutation_overlap_eq_one_iff
#print axioms AIM025.permutation_overlap_eq_one_iff

#check @AIM025.AIM025_CHOLLET_NONNEGATIVE
#print axioms AIM025.AIM025_CHOLLET_NONNEGATIVE

#check @AIM025.weightedGram_entrywise_nonneg
#print axioms AIM025.weightedGram_entrywise_nonneg

#check @AIM025.weightedGram_chollet
#print axioms AIM025.weightedGram_chollet

/-!
Native theorem-level axiom allowlist gate.
This runs in the same imported environment used by #print axioms above.
It adds no premise, axiom, theorem, or replacement proof to the mathematics.
The exact source hash and native compiler exit status remain evidence gates.
-/

open Lean in
run_cmd do
  let targets : Array Name := #[
    ``AIM025.mass_mul_eq_diagonal_add_offDiagonal,
    ``AIM025.mass_mul_sub_diagonal_eq_offDiagonal,
    ``AIM025.mass_nonneg,
    ``AIM025.diagonalPair_nonneg,
    ``AIM025.offDiagonalPair_nonneg,
    ``AIM025.diagonalPair_le_mass_mul,
    ``AIM025.mass_eq_zero_iff,
    ``AIM025.exists_pos_of_mass_ne_zero,
    ``AIM025.offDiagonalPair_eq_zero_iff,
    ``AIM025.offDiagonalPair_eq_zero_iff_zero_or_commonUnique,
    ``AIM025.normalized_nonneg,
    ``AIM025.mass_normalized,
    ``AIM025.normalized_overlap,
    ``AIM025.normalized_overlap_le_one,
    ``AIM025.permanent_eq_mass_permTerm,
    ``AIM025.permTerm_nonneg,
    ``AIM025.permanent_nonneg,
    ``AIM025.permTerm_hadamard,
    ``AIM025.permanent_hadamard_eq_diagonalPair,
    ``AIM025.cholletGap_eq_offDiagonal,
    ``AIM025.cholletGap_nonneg,
    ``AIM025.permanent_hadamard_le,
    ``AIM025.cholletGap_eq_zero_iff_crossTerms,
    ``AIM025.cholletGap_eq_zero_iff,
    ``AIM025.permanent_hadamard_eq_iff,
    ``AIM025.cholletGap_eq_zero_iff_commonUnique,
    ``AIM025.permutationDistribution_eq_normalized,
    ``AIM025.permutationDistribution_nonneg,
    ``AIM025.permutationDistribution_sum,
    ``AIM025.normalized_permanent_overlap,
    ``AIM025.normalized_cholletGap,
    ``AIM025.permutation_overlap_bounds,
    ``AIM025.permutation_overlap_eq_one_iff,
    ``AIM025.AIM025_CHOLLET_NONNEGATIVE,
    ``AIM025.weightedGram_entrywise_nonneg,
    ``AIM025.weightedGram_chollet
  ]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  if targets.size != 36 then
    throwError "AIM025_NATIVE_AXIOM_AUDIT=INVALID_TARGET_COUNT"
  for target in targets do
    let env ← getEnv
    match env.find? target with
    | none => throwError "AIM025_NATIVE_AXIOM_AUDIT=MISSING_TARGET:{target}"
    | some _ => pure ()
    let axioms ← collectAxioms target
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "AIM025_NATIVE_AXIOM_AUDIT=UNAPPROVED_AXIOM:{target}:{axiomName}"
    logInfo m!"AXIOM_AUDIT_PASS=[{target}]"
  logInfo "AIM025_NATIVE_AXIOM_AUDIT_COUNT=36"
  logInfo "AIM025_NATIVE_AXIOM_AUDIT=PASS_STANDARD_ONLY"
