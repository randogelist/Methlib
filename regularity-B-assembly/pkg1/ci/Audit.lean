import H12_SIGMA_ZERO_SMALL_PACKAGE

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal Interval
noncomputable section

namespace H12CriticalAbsorption

example : CriticalAbsorptionBundle := @H12CriticalAbsorption.H12_CRITICAL_ABSORPTION
end H12CriticalAbsorption
#eval "EXACT_TYPE_PASS:H12CriticalAbsorption.H12_CRITICAL_ABSORPTION"
#print axioms H12CriticalAbsorption.H12_CRITICAL_ABSORPTION

namespace H12CriticalPairingIntegral
open scoped ENNReal
open MeasureTheory
open H12CriticalTrilinearCompiler
open H12HolderLpAdapter
example :
    ∀ {α : Type*} [MeasurableSpace α]
      {μ : Measure α}
      {s : CriticalState},
      CriticalIntegralRealization μ s →
      CriticalHolder s := @H12CriticalPairingIntegral.H12_CRITICAL_PAIRING_INTEGRAL
end H12CriticalPairingIntegral
#eval "EXACT_TYPE_PASS:H12CriticalPairingIntegral.H12_CRITICAL_PAIRING_INTEGRAL"
#print axioms H12CriticalPairingIntegral.H12_CRITICAL_PAIRING_INTEGRAL

namespace H12CriticalTrilinearCompiler
open H12CriticalAbsorption
example :
    CriticalTrilinearCompilerBundle := @H12CriticalTrilinearCompiler.H12_CRITICAL_TRILINEAR_COMPILER
end H12CriticalTrilinearCompiler
#eval "EXACT_TYPE_PASS:H12CriticalTrilinearCompiler.H12_CRITICAL_TRILINEAR_COMPILER"
#print axioms H12CriticalTrilinearCompiler.H12_CRITICAL_TRILINEAR_COMPILER

namespace H12FourierFoundations
open scoped BigOperators
open MeasureTheory
example : FoundationBundle := @H12FourierFoundations.H12_FOURIER_FOUNDATIONS
end H12FourierFoundations
#eval "EXACT_TYPE_PASS:H12FourierFoundations.H12_FOURIER_FOUNDATIONS"
#print axioms H12FourierFoundations.H12_FOURIER_FOUNDATIONS

namespace H12HolderLpAdapter
open scoped ENNReal
open MeasureTheory
open H12CriticalTrilinearCompiler
example :
    ∀ {α : Type*} [MeasurableSpace α]
      {μ : Measure α}
      {s : CriticalState},
      CriticalPairingRealization μ s →
      CriticalHolder s := @H12HolderLpAdapter.H12_HOLDER_LP_ADAPTER
end H12HolderLpAdapter
#eval "EXACT_TYPE_PASS:H12HolderLpAdapter.H12_HOLDER_LP_ADAPTER"
#print axioms H12HolderLpAdapter.H12_HOLDER_LP_ADAPTER

namespace H12PointwiseConvectionSquare
open scoped BigOperators
example :
    PointwiseConvectionSquareBundle := @H12PointwiseConvectionSquare.H12_POINTWISE_CONVECTION_SQUARE
end H12PointwiseConvectionSquare
#eval "EXACT_TYPE_PASS:H12PointwiseConvectionSquare.H12_POINTWISE_CONVECTION_SQUARE"
#print axioms H12PointwiseConvectionSquare.H12_POINTWISE_CONVECTION_SQUARE

namespace H12SpectralEnergyBridge
open scoped BigOperators
open MeasureTheory
open H12FourierFoundations
example : SpectralEnergyBundle := @H12SpectralEnergyBridge.H12_SPECTRAL_ENERGY_BRIDGE
end H12SpectralEnergyBridge
#eval "EXACT_TYPE_PASS:H12SpectralEnergyBridge.H12_SPECTRAL_ENERGY_BRIDGE"
#print axioms H12SpectralEnergyBridge.H12_SPECTRAL_ENERGY_BRIDGE

namespace NSEPairingPointwiseLpLift
open scoped ENNReal
open MeasureTheory
open H12CriticalTrilinearCompiler
open H12HolderLpAdapter
open NSEPointwisePairingIdentification
example :
    ∀ {α : Type*} [MeasurableSpace α]
      {μ : Measure α}
      {s : CriticalState},
      PhysicalLpData μ s →
      CriticalHolder s := @NSEPairingPointwiseLpLift.NSE_PAIRING_POINTWISE_LP_LIFT
end NSEPairingPointwiseLpLift
#eval "EXACT_TYPE_PASS:NSEPairingPointwiseLpLift.NSE_PAIRING_POINTWISE_LP_LIFT"
#print axioms NSEPairingPointwiseLpLift.NSE_PAIRING_POINTWISE_LP_LIFT

namespace NSEPhysicalLpDataConstruction
open scoped ENNReal
open MeasureTheory
open H12CriticalTrilinearCompiler
open H12HolderLpAdapter
open NSEPointwisePairingIdentification
open NSEPairingPointwiseLpLift
example :
    ∀ {α : Type*} [MeasurableSpace α]
      {μ : Measure α}
      (R : RawPhysicalFields μ)
      (E D : ℝ)
      (hE : 0 ≤ E)
      (hD : 0 ≤ D),
      CriticalHolder (physicalState R E D hE hD) := @NSEPhysicalLpDataConstruction.NSE_PHYSICAL_LP_DATA_CONSTRUCTION
end NSEPhysicalLpDataConstruction
#eval "EXACT_TYPE_PASS:NSEPhysicalLpDataConstruction.NSE_PHYSICAL_LP_DATA_CONSTRUCTION"
#print axioms NSEPhysicalLpDataConstruction.NSE_PHYSICAL_LP_DATA_CONSTRUCTION

namespace NSEPointwisePairingIdentification
open scoped ENNReal
open MeasureTheory
open H12CriticalTrilinearCompiler
open H12HolderLpAdapter
example :
    ∀ {α : Type*} [MeasurableSpace α]
      {μ : Measure α}
      {s : CriticalState},
      NSEPairingRealization μ s →
      CriticalHolder s := @NSEPointwisePairingIdentification.NSE_POINTWISE_PAIRING_IDENTIFICATION
end NSEPointwisePairingIdentification
#eval "EXACT_TYPE_PASS:NSEPointwisePairingIdentification.NSE_POINTWISE_PAIRING_IDENTIFICATION"
#print axioms NSEPointwisePairingIdentification.NSE_POINTWISE_PAIRING_IDENTIFICATION

namespace PeriodicHhalfL3ComponentCompiler
open H12CriticalTrilinearCompiler
open NSEPhysicalLpDataConstruction
open PeriodicStrongSliceToRawPhysicalFields
example :
    ∀ {s : CriticalState}
      (h : ScalarEndpointCertificate s),
      ∃ hS : PeriodicHhalfL3 s,
        hS.C3 = compiledConstant h := @PeriodicHhalfL3ComponentCompiler.PERIODIC_HHALF_L3_COMPONENT_COMPILER
end PeriodicHhalfL3ComponentCompiler
#eval "EXACT_TYPE_PASS:PeriodicHhalfL3ComponentCompiler.PERIODIC_HHALF_L3_COMPONENT_COMPILER"
#print axioms PeriodicHhalfL3ComponentCompiler.PERIODIC_HHALF_L3_COMPONENT_COMPILER

namespace PeriodicStrongSliceToRawPhysicalFields
open scoped ENNReal
open MeasureTheory
open H12CriticalTrilinearCompiler
open NSEPointwisePairingIdentification
open NSEPairingPointwiseLpLift
open NSEPhysicalLpDataConstruction
example :
    ∀ S : PeriodicStrongSlice,
      ∃ R : RawPhysicalFields (volume : Measure Torus3),
        R.J = S.J ∧
        R.u = S.u ∧
        R.w = S.w := @PeriodicStrongSliceToRawPhysicalFields.PERIODIC_STRONG_SLICE_TO_RAW_PHYSICAL_FIELDS
end PeriodicStrongSliceToRawPhysicalFields
#eval "EXACT_TYPE_PASS:PeriodicStrongSliceToRawPhysicalFields.PERIODIC_STRONG_SLICE_TO_RAW_PHYSICAL_FIELDS"
#print axioms PeriodicStrongSliceToRawPhysicalFields.PERIODIC_STRONG_SLICE_TO_RAW_PHYSICAL_FIELDS

namespace ScalarPeriodicHhalfL3HLSCompiler
open scoped ENNReal
open MeasureTheory
open H12CriticalTrilinearCompiler
open NSEPhysicalLpDataConstruction
open PeriodicStrongSliceToRawPhysicalFields
open PeriodicHhalfL3ComponentCompiler
example :
    ∀ {s : CriticalState}
      (H : PeriodicRieszHalfCertificate)
      (D : HLSComponentData s H),
      ∃ hS : PeriodicHhalfL3 s,
        hS.C3 = 9 * H.Cscalar := @ScalarPeriodicHhalfL3HLSCompiler.SCALAR_PERIODIC_HHALF_L3_HLS_COMPILER
end ScalarPeriodicHhalfL3HLSCompiler
#eval "EXACT_TYPE_PASS:ScalarPeriodicHhalfL3HLSCompiler.SCALAR_PERIODIC_HHALF_L3_HLS_COMPILER"
#print axioms ScalarPeriodicHhalfL3HLSCompiler.SCALAR_PERIODIC_HHALF_L3_HLS_COMPILER

namespace H12SigmaZeroSmallClass
open H12FourierFoundations H12SpectralEnergyBridge
example :
    (∀ (ν C3 : ℝ), 0 < ν → 0 < C3 → Nonempty (SmallDatum ν C3)) ∧
    (∀ {ν C3 t : ℝ} (a : RealH12Datum) (ha : Small ν C3 a)
      (ht : 0 ≤ t), Small ν C3 (heatRealDatum ν t ha.1.le ht a)) ∧
    (∀ {ν C3 : ℝ} (S : Finset Mode3) (hS : SymmetricCutoff S)
      (a : RealH12Datum), Small ν C3 a →
        Small ν C3 (cutoffRealDatum S hS a)) := @H12SigmaZeroSmallClass.H12_SIGMA_ZERO_SMALL_CLASS
end H12SigmaZeroSmallClass
#eval "EXACT_TYPE_PASS:H12SigmaZeroSmallClass.H12_SIGMA_ZERO_SMALL_CLASS"
#print axioms H12SigmaZeroSmallClass.H12_SIGMA_ZERO_SMALL_CLASS

namespace H12CriticalEnergyBudget
example :
    ∀ {H D E : ℝ → ℝ} {ν θ T H₀ : ℝ}
    (hν : 0 < ν) (hθ : θ < 1) (hT : 0 ≤ T) (hH₀ : 0 ≤ H₀)
    (hD : ContinuousOn D (Icc 0 T))
    (hE : ContinuousOn E (Icc 0 T))
    (hH_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ H t)
    (hD_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (henergy : ∀ t ∈ Icc 0 T,
      H t + dissipationCoefficient ν θ * (∫ s in (0 : ℝ)..t, D s) ≤ H₀)
    (hinterpolation : ∀ t ∈ Icc 0 T, (E t) ^ 2 ≤ H t * D t),
    (∀ t ∈ Icc 0 T, H t ≤ H₀) ∧
      (∫ s in (0 : ℝ)..T, D s) ≤ H₀ / dissipationCoefficient ν θ ∧
      (∫ s in (0 : ℝ)..T, (E s) ^ 2) ≤
        H₀ ^ 2 / dissipationCoefficient ν θ :=
  @H12CriticalEnergyBudget.H12_SQUARE_ENSTROPHY_OF_CRITICAL_ENERGY
end H12CriticalEnergyBudget
#eval "EXACT_TYPE_PASS:H12CriticalEnergyBudget.H12_SQUARE_ENSTROPHY_OF_CRITICAL_ENERGY"
#print axioms H12CriticalEnergyBudget.H12_SQUARE_ENSTROPHY_OF_CRITICAL_ENERGY

namespace H12CriticalEnergyBudget
example :
    ∀ {ι : Type*} {H D E : ι → ℝ → ℝ} {ν θ T H₀ : ℝ}
    (hν : 0 < ν) (hθ : θ < 1) (hT : 0 ≤ T) (hH₀ : 0 ≤ H₀)
    (hD : ∀ n, ContinuousOn (D n) (Icc 0 T))
    (hE : ∀ n, ContinuousOn (E n) (Icc 0 T))
    (hH_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ H n t)
    (hD_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ D n t)
    (henergy : ∀ n t, t ∈ Icc 0 T →
      H n t + dissipationCoefficient ν θ * (∫ s in (0 : ℝ)..t, D n s) ≤ H₀)
    (hinterpolation : ∀ n t, t ∈ Icc 0 T → (E n t) ^ 2 ≤ H n t * D n t),
    ∀ n, (∫ s in (0 : ℝ)..T, (E n s) ^ 2) ≤
      H₀ ^ 2 / (2 * (1 - θ) * ν) :=
  @H12CriticalEnergyBudget.H12_UNIFORM_SQUARE_ENSTROPHY_OF_CRITICAL_ENERGY
end H12CriticalEnergyBudget
#eval "EXACT_TYPE_PASS:H12CriticalEnergyBudget.H12_UNIFORM_SQUARE_ENSTROPHY_OF_CRITICAL_ENERGY"
#print axioms H12CriticalEnergyBudget.H12_UNIFORM_SQUARE_ENSTROPHY_OF_CRITICAL_ENERGY

namespace H12CriticalEnergyBudget
example :
    ∀ {H d : ℝ → ℝ} {T H₀ R : ℝ}
    (hT : 0 ≤ T) (hH : ContinuousOn H (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivAt H (d t) t)
    (h_initial : H 0 ≤ H₀) (hgap : H₀ < R)
    (hbelow : ∀ t ∈ Ico 0 T, H t ≤ R → d t ≤ 0),
    ∀ t ∈ Icc 0 T, H t ≤ H₀ :=
  @H12CriticalEnergyBudget.energy_bound_of_deriv_nonpos_below_barrier
end H12CriticalEnergyBudget
#eval "EXACT_TYPE_PASS:H12CriticalEnergyBudget.energy_bound_of_deriv_nonpos_below_barrier"
#print axioms H12CriticalEnergyBudget.energy_bound_of_deriv_nonpos_below_barrier

namespace H12CriticalEnergyBudget
example :
    ∀ {H D d : ℝ → ℝ} {ν C θ T H₀ : ℝ}
    (hν : 0 < ν) (hC : 0 < C) (hθ : θ < 1)
    (hT : 0 ≤ T) (hH₀ : 0 ≤ H₀)
    (hH : ContinuousOn H (Icc 0 T))
    (hD : ContinuousOn D (Icc 0 T))
    (hH_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ H t)
    (hD_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivAt H (d t) t)
    (h_initial : H 0 ≤ H₀)
    (hsmall : C * Real.sqrt H₀ ≤ θ * ν)
    (hcritical : ∀ t ∈ Ico 0 T,
      d t + 2 * ν * D t ≤ 2 * C * Real.sqrt (H t) * D t),
    ∀ t ∈ Icc 0 T,
      H t + dissipationCoefficient ν θ * (∫ s in (0 : ℝ)..t, D s) ≤ H₀ :=
  @H12CriticalEnergyBudget.H12_CRITICAL_ENERGY_OF_SMALL_DATA
end H12CriticalEnergyBudget
#eval "EXACT_TYPE_PASS:H12CriticalEnergyBudget.H12_CRITICAL_ENERGY_OF_SMALL_DATA"
#print axioms H12CriticalEnergyBudget.H12_CRITICAL_ENERGY_OF_SMALL_DATA

namespace H12CriticalEnergyBudget
example :
    ∀ {H D E d : ℝ → ℝ} {ν C θ T H₀ : ℝ}
    (hν : 0 < ν) (hC : 0 < C) (hθ : θ < 1)
    (hT : 0 ≤ T) (hH₀ : 0 ≤ H₀)
    (hH : ContinuousOn H (Icc 0 T))
    (hD : ContinuousOn D (Icc 0 T))
    (hE : ContinuousOn E (Icc 0 T))
    (hH_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ H t)
    (hD_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivAt H (d t) t)
    (h_initial : H 0 ≤ H₀)
    (hsmall : C * Real.sqrt H₀ ≤ θ * ν)
    (hcritical : ∀ t ∈ Ico 0 T,
      d t + 2 * ν * D t ≤ 2 * C * Real.sqrt (H t) * D t)
    (hinterpolation : ∀ t ∈ Icc 0 T, (E t) ^ 2 ≤ H t * D t),
    (∫ s in (0 : ℝ)..T, (E s) ^ 2) ≤ H₀ ^ 2 / (2 * (1 - θ) * ν) :=
  @H12CriticalEnergyBudget.H12_SQUARE_ENSTROPHY_OF_SMALL_DATA
end H12CriticalEnergyBudget
#eval "EXACT_TYPE_PASS:H12CriticalEnergyBudget.H12_SQUARE_ENSTROPHY_OF_SMALL_DATA"
#print axioms H12CriticalEnergyBudget.H12_SQUARE_ENSTROPHY_OF_SMALL_DATA

namespace H12CriticalEnergyBudget
example :
    ∀ {ι : Type*} {H D E d : ι → ℝ → ℝ} {ν C θ T H₀ : ℝ}
    (hν : 0 < ν) (hC : 0 < C) (hθ : θ < 1)
    (hT : 0 ≤ T) (hH₀ : 0 ≤ H₀)
    (hH : ∀ n, ContinuousOn (H n) (Icc 0 T))
    (hD : ∀ n, ContinuousOn (D n) (Icc 0 T))
    (hE : ∀ n, ContinuousOn (E n) (Icc 0 T))
    (hH_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ H n t)
    (hD_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ D n t)
    (hderiv : ∀ n t, t ∈ Ico 0 T → HasDerivAt (H n) (d n t) t)
    (h_initial : ∀ n, H n 0 ≤ H₀)
    (hsmall : C * Real.sqrt H₀ ≤ θ * ν)
    (hcritical : ∀ n t, t ∈ Ico 0 T →
      d n t + 2 * ν * D n t ≤ 2 * C * Real.sqrt (H n t) * D n t)
    (hinterpolation : ∀ n t, t ∈ Icc 0 T → (E n t) ^ 2 ≤ H n t * D n t),
    ∀ n, (∫ s in (0 : ℝ)..T, (E n s) ^ 2) ≤
      H₀ ^ 2 / (2 * (1 - θ) * ν) :=
  @H12CriticalEnergyBudget.H12_UNIFORM_SQUARE_ENSTROPHY_OF_SMALL_DATA
end H12CriticalEnergyBudget
#eval "EXACT_TYPE_PASS:H12CriticalEnergyBudget.H12_UNIFORM_SQUARE_ENSTROPHY_OF_SMALL_DATA"
#print axioms H12CriticalEnergyBudget.H12_UNIFORM_SQUARE_ENSTROPHY_OF_SMALL_DATA

namespace H12SmallScaling
open H12FourierFoundations H12SpectralEnergyBridge H12SigmaZeroSmallClass
example :
    ∀ (r : ℝ) (a : RealH12Datum),
    criticalNorm (scaleDatum r a) = |r| * criticalNorm a :=
  @H12SmallScaling.criticalNorm_scale
end H12SmallScaling
#eval "EXACT_TYPE_PASS:H12SmallScaling.criticalNorm_scale"
#print axioms H12SmallScaling.criticalNorm_scale

namespace H12SmallScaling
open H12FourierFoundations H12SpectralEnergyBridge H12SigmaZeroSmallClass
example :
    ∀ (ν C3 ε : ℝ)
    (hν : 0 < ν) (hC3 : 0 < C3) (hε : 0 < ε)
    (a : RealH12Datum),
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ Small ν C3 (scaleDatum r a) :=
  @H12SmallScaling.exists_small_positive_scale
end H12SmallScaling
#eval "EXACT_TYPE_PASS:H12SmallScaling.exists_small_positive_scale"
#print axioms H12SmallScaling.exists_small_positive_scale

namespace H12SmallScaling
open H12FourierFoundations H12SpectralEnergyBridge H12SigmaZeroSmallClass
example :
    (∀ (r : ℝ) (a : RealH12Datum),
      criticalSq (scaleDatum r a) = r ^ 2 * criticalSq a) ∧
    (∀ {ν C3 r : ℝ} (a : RealH12Datum),
      Small ν C3 a → |r| ≤ 1 → Small ν C3 (scaleDatum r a)) ∧
    (∀ (ν C3 : ℝ), 0 < ν → 0 < C3 →
      ∃ a : SmallDatum ν C3, a.val.coeff ≠ 0) :=
  @H12SmallScaling.H12_SMALL_SCALING
end H12SmallScaling
#eval "EXACT_TYPE_PASS:H12SmallScaling.H12_SMALL_SCALING"
#print axioms H12SmallScaling.H12_SMALL_SCALING

namespace H12L2CoefficientEmbedding
open H12FourierFoundations H12SpectralEnergyBridge H12SigmaZeroSmallClass
example :
    ∀ {k : Mode3} (hk : k ≠ 0),
    2 * Real.pi ≤ freq k :=
  @H12L2CoefficientEmbedding.physical_frequency_gap
end H12L2CoefficientEmbedding
#eval "EXACT_TYPE_PASS:H12L2CoefficientEmbedding.physical_frequency_gap"
#print axioms H12L2CoefficientEmbedding.physical_frequency_gap

namespace H12L2CoefficientEmbedding
open H12FourierFoundations H12SpectralEnergyBridge H12SigmaZeroSmallClass
example :
    ∀ (a : RealH12Datum),
    criticalNorm a = 0 ↔ ∀ k : Mode3, a.coeff k = 0 :=
  @H12L2CoefficientEmbedding.criticalNorm_eq_zero_iff
end H12L2CoefficientEmbedding
#eval "EXACT_TYPE_PASS:H12L2CoefficientEmbedding.criticalNorm_eq_zero_iff"
#print axioms H12L2CoefficientEmbedding.criticalNorm_eq_zero_iff

namespace H12L2CoefficientEmbedding
open H12FourierFoundations H12SpectralEnergyBridge H12SigmaZeroSmallClass
example :
    ∀ (a : RealH12Datum),
    Summable (fun k : Mode3 => ‖a.coeff k‖ ^ 2) ∧
      coefficientL2Sq a ≤ criticalSq a / (2 * Real.pi) ∧
      (criticalSq a = 0 ↔ ∀ k : Mode3, a.coeff k = 0) :=
  @H12L2CoefficientEmbedding.H12_L2_COEFFICIENT_EMBEDDING
end H12L2CoefficientEmbedding
#eval "EXACT_TYPE_PASS:H12L2CoefficientEmbedding.H12_L2_COEFFICIENT_EMBEDDING"
#print axioms H12L2CoefficientEmbedding.H12_L2_COEFFICIENT_EMBEDDING

namespace H12SmallClassBudget
open H12SigmaZeroSmallClass H12CriticalEnergyBudget
example :
    ∀ {ν C3 : ℝ} {a : RealH12Datum} (ha : Small ν C3 a),
    C3 ^ 3 * Real.sqrt (criticalSq a) ≤ (1 / 4 : ℝ) * ν :=
  @H12SmallClassBudget.small_critical_coefficient_le
end H12SmallClassBudget
#eval "EXACT_TYPE_PASS:H12SmallClassBudget.small_critical_coefficient_le"
#print axioms H12SmallClassBudget.small_critical_coefficient_le

namespace H12SmallClassBudget
open H12SigmaZeroSmallClass H12CriticalEnergyBudget
example :
    ∀ {ι : Type*} {H D E d : ι → ℝ → ℝ} {ν C3 T : ℝ}
    (a : RealH12Datum) (ha : Small ν C3 a) (hT : 0 ≤ T)
    (hH : ∀ n, ContinuousOn (H n) (Icc 0 T))
    (hD : ∀ n, ContinuousOn (D n) (Icc 0 T))
    (hE : ∀ n, ContinuousOn (E n) (Icc 0 T))
    (hH_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ H n t)
    (hD_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ D n t)
    (hderiv : ∀ n t, t ∈ Ico 0 T → HasDerivAt (H n) (d n t) t)
    (h_initial : ∀ n, H n 0 ≤ criticalSq a)
    (hcritical : ∀ n t, t ∈ Ico 0 T →
      d n t + 2 * ν * D n t ≤ 2 * C3 ^ 3 * Real.sqrt (H n t) * D n t)
    (hinterpolation : ∀ n t, t ∈ Icc 0 T → (E n t) ^ 2 ≤ H n t * D n t),
    ∀ n, (∫ s in (0 : ℝ)..T, (E n s) ^ 2) ≤
      criticalSq a ^ 2 / (2 * (1 - (1 / 4 : ℝ)) * ν) :=
  @H12SmallClassBudget.H12_SMALL_CLASS_UNIFORM_SQUARE_ENSTROPHY
end H12SmallClassBudget
#eval "EXACT_TYPE_PASS:H12SmallClassBudget.H12_SMALL_CLASS_UNIFORM_SQUARE_ENSTROPHY"
#print axioms H12SmallClassBudget.H12_SMALL_CLASS_UNIFORM_SQUARE_ENSTROPHY

namespace H12SmallClassBudget
open H12SigmaZeroSmallClass H12CriticalEnergyBudget
example :
    ∀ {ι : Type*} {H D E d : ι → ℝ → ℝ} {ν C3 T : ℝ}
    (a : RealH12Datum) (ha : Small ν C3 a) (hT : 0 ≤ T)
    (hH : ∀ n, ContinuousOn (H n) (Icc 0 T))
    (hD : ∀ n, ContinuousOn (D n) (Icc 0 T))
    (hE : ∀ n, ContinuousOn (E n) (Icc 0 T))
    (hH_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ H n t)
    (hD_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ D n t)
    (hderiv : ∀ n t, t ∈ Ico 0 T → HasDerivAt (H n) (d n t) t)
    (h_initial : ∀ n, H n 0 ≤ criticalSq a)
    (hcritical : ∀ n t, t ∈ Ico 0 T →
      d n t + 2 * ν * D n t ≤ 2 * C3 ^ 3 * Real.sqrt (H n t) * D n t)
    (hinterpolation : ∀ n t, t ∈ Icc 0 T → (E n t) ^ 2 ≤ H n t * D n t),
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n, (∫ s in (0 : ℝ)..T, (E n s) ^ 2) ≤ M :=
  @H12SmallClassBudget.H12_SMALL_CLASS_EXISTS_UNIFORM_BUDGET
end H12SmallClassBudget
#eval "EXACT_TYPE_PASS:H12SmallClassBudget.H12_SMALL_CLASS_EXISTS_UNIFORM_BUDGET"
#print axioms H12SmallClassBudget.H12_SMALL_CLASS_EXISTS_UNIFORM_BUDGET
