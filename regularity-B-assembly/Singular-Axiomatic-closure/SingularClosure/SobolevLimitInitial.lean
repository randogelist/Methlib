import SingularClosure.SobolevFourierConstraints
import SingularClosure.SobolevL2Realization
import SingularClosure.PeriodicFourierRealization

/-!
# The actual physical initial datum of a canonical H0 limit

Every fixed nonzero frequency eventually lies in the increasing canonical
cutoff. Continuity of H0 coefficient evaluation passes the actual Galerkin
initial condition to the limit. The zero mode follows from the proved physical
mean condition. Fourier uniqueness then identifies the initial H0 state with
the literal periodic datum in the torus L² space.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace SingularClosure

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def torusPhysicalDatumL2 (a : Field) (ha : Continuous a) : TorusVectorL2 :=
  WithLp.toLp 2 (fun i : Fin 3 => torusDatumL2 a ha i)

theorem torusPhysicalDatumL2_fourierCoeff (a : Field) (ha : Continuous a) :
    torusVectorFourierCoeff (torusPhysicalDatumL2 a ha) = datumFourierCoeff a := by
  funext k i
  change UnitAddTorus.mFourierCoeff (torusDatumL2 a ha i) k = datumFourierCoeff a k i
  rw [← UnitAddTorus.mFourierBasis_repr]
  exact torusDatumL2_fourierBasis_repr a ha i k

theorem eventually_mem_cutoffModes_strictMono
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (k : Frequency) (hk : k ≠ 0) :
    ∀ᶠ n in atTop, k ∈ cutoffModes (φ n + 1) := by
  have hid (n : ℕ) : n ≤ φ n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hφ (Nat.lt_succ_self n)))
  obtain ⟨M, hM⟩ := exists_nat_gt (galerkinFreqSq k)
  filter_upwards [eventually_ge_atTop M] with n hn
  apply mem_cutoffModes_of_freqSq_le hk
  have hmn : M ≤ φ n + 1 := by
    have hnφ := hid n
    omega
  have hmnZ : (M : ℤ) ≤ (φ n + 1 : ℕ) := by exact_mod_cast hmn
  have hN : (1 : ℤ) ≤ (φ n + 1 : ℕ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le (φ n)))
  nlinarith [sq_nonneg (((φ n + 1 : ℕ) : ℤ) - 1)]

/-- The initial coefficients of any actual canonical uniform H0 limit. -/
theorem canonicalSobolevLimit_initial_coeff
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, TorusSobolev 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : TendstoUniformly
      (fun n (t : Icc (0 : ℝ) T) =>
        (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t.val)
      u atTop) :
    (u ⟨0, le_rfl, hT⟩).val = datumFourierCoeff a := by
  funext k i
  have hc := (torusSobolevH0Coeff_continuous k i).tendsto
      (u ⟨0, le_rfl, hT⟩) |>.comp (hconv.tendsto_at ⟨0, le_rfl, hT⟩)
  apply tendsto_nhds_unique hc
  have he : (fun n =>
      ((canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 0).val k i) =ᶠ[atTop]
        (fun _ => datumFourierCoeff a k i) := by
    by_cases hk : k = 0
    · subst k
      exact Filter.Eventually.of_forall fun n => by
        rw [(canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState_zero_mode
          0 0 le_rfl i, smoothSigmaZero_fourier_meanZero ha i]
    · filter_upwards [eventually_mem_cutoffModes_strictMono φ hφ k hk] with n hn
      rw [(canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState_coeff 0 le_rfl,
        (canonicalGalerkinSolution ν hν a ha (φ n + 1)).initial k i, if_pos hn]
  exact tendsto_const_nhds.congr' he.symm

/-- The H0 limit at time zero is the actual physical periodic datum in torus L². -/
theorem canonicalSobolevLimit_initial_physical
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, TorusSobolev 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : TendstoUniformly
      (fun n (t : Icc (0 : ℝ) T) =>
        (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t.val)
      u atTop) :
    torusSobolevL2 (u ⟨0, le_rfl, hT⟩) = torusPhysicalDatumL2 a ha.smooth.continuous := by
  apply torusSobolevL2_eq_of_fourierCoeff
  rw [torusPhysicalDatumL2_fourierCoeff,
    canonicalSobolevLimit_initial_coeff ν hν a ha T hT u φ hφ hconv]

end

end SingularClosure
