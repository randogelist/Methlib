import H12_SIGMA_ZERO_SMALL_PACKAGE

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
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
