import SingularClosure.Contracts
import SingularClosure.CriticalSpaces
import SingularClosure.CriticalSpacesEmbedding
import SingularClosure.CriticalWeakGradient
import SingularClosure.CriticalSmoothEnergy
import SingularClosure.CriticalClassicalWeakMomentum
import SingularClosure.CriticalLerayHopf
import SingularClosure.GalerkinTimeDerivative
import SingularClosure.PeriodicFourierRealization
import SingularClosure.CriticalUniformBounds
import SingularClosure.CriticalFourierInterpolation
import SingularClosure.CriticalSerrinUniqueness
import SingularClosure.CriticalPositiveFlow
import SingularClosure.CriticalH1Algebra

/-
R8 SOURCE-ONLY API PROBE.
PINNED_LEAN = 4.33.0.
PINNED_MATHLIB = db584cd6d46c92f209a44c0f1c829460d327499d.
PINNED_FOUNDATION = 09dfe94a1ef150e21d09df3013fbe09002ef139c.
EXECUTION_STATUS = NOT_EXECUTED.
SOURCE_SNAPSHOTS_ARE_NOT_A_COMPLETE_DEPENDENCY_INSTALLATION.
-/

-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/Contracts.lean:56; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.coordinateDerivative
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/Contracts.lean:64; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.gradient
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalSpaces.lean:228; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.criticalSobolev_norm_sq
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalSpaces.lean:223; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.criticalSobolevOfCoeff_coeff
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalSpacesEmbedding.lean:89; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.criticalH0Equiv_coeff
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalSpacesEmbedding.lean:73; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.criticalSobolevLower_coeff
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalWeakGradient.lean:85; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.critical_physicalFieldInner_compCLM_tendsto
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalWeakGradient.lean:109; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.CRITICAL_WEAK_GRADIENT_OF_SMOOTH_APPROXIMATION
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalSmoothEnergy.lean:31; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.critical_hasDerivAt_real_cube_integral
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalSmoothEnergy.lean:216; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.CRITICAL_SMOOTH_NSE_ENERGY_IDENTITY
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalClassicalWeakMomentum.lean:115; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.critical_positive_pairing_hasDerivAt
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalLerayHopf.lean:38; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.CriticalLerayHopf
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/GalerkinTimeDerivative.lean:29; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.GalerkinSolution.velocity_hasDerivWithinAt
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/GalerkinTimeDerivative.lean:64; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.GalerkinSolution.timeDerivative_eq_finiteSynthesis
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/PeriodicFourierRealization.lean:31; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.torusDatumRepresentative
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalUniformBounds.lean:17; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.GalerkinSolution.criticalState_norm_sq_nat
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalFourierInterpolation.lean:107; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.criticalEnergy_two_eq_coefficientDissipation
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalSerrinUniqueness.lean:37; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalPositiveFlow.lean:17; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.CriticalPositiveSobolevFlow
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalPositiveFlow.lean:109; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.CRITICAL_POSITIVE_PHYSICAL_NSE
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalH1Algebra.lean:43; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.criticalGradientEnergy
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalH1Algebra.lean:57; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.criticalGradientEnergy_fderiv
-- regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalH1Algebra.lean:50; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.SingularClosure.criticalGradientEnergy_nonneg
