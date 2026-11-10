import NSE_NOH_FourierWeakTest
import NSE_NOH_FourierSpectral
import NSE_NOH_Geometry
import NSE_NOH_Modes
import NSE_NOH_Jet
import NSE_NOH_Derivative
import NSE_NOH_Laplacian
import NSE_NOH_Classical
import NSE_NOH_Energy
import NSE_NOH_TorusMass
import NSE_NOH_L2Pullback
import NSE_NOH_L2Closure

/-!
NSE_NOH FIX10: theorem-level audit of the existing conditional composition
and the NEW independent pointwise 2D3C geometry.  This audit does not prove
that GeometryPorts exists or that the unconditional NSE_NOH root holds.
-/

#check NSE_NOH.NSE_NOH
#print NSE_NOH.NSE_NOH
#check NSE_NOH.AnalyticPorts
#check NSE_NOH.from_analytic_ports
#print axioms NSE_NOH.from_analytic_ports
#check NSE_NOH.realProjection2_realEmbedding2
#print axioms NSE_NOH.realProjection2_realEmbedding2
#check NSE_NOH.realProjection2_update_zero
#print axioms NSE_NOH.realProjection2_update_zero
#check NSE_NOH.realEmbedding2_realProjection2
#print axioms NSE_NOH.realEmbedding2_realProjection2
#check NSE_NOH.liftedVelocity_x1_invariant
#print axioms NSE_NOH.liftedVelocity_x1_invariant
#check NSE_NOH.liftedPressure_x1_invariant
#print axioms NSE_NOH.liftedPressure_x1_invariant
#check NSE_NOH.sliceScalar_liftedVelocity
#print axioms NSE_NOH.sliceScalar_liftedVelocity
#check NSE_NOH.slicePlanar_liftedVelocity
#print axioms NSE_NOH.slicePlanar_liftedVelocity
#check NSE_NOH.liftedVelocity_slice_of_invariant
#print axioms NSE_NOH.liftedVelocity_slice_of_invariant
#check NSE_NOH.pointwiseX1Invariant_iff_exists_lift
#print axioms NSE_NOH.pointwiseX1Invariant_iff_exists_lift
#check NSE_NOH.liftedVelocity_injective_components
#print axioms NSE_NOH.liftedVelocity_injective_components
#check NSE_NOH.modeProjection2_modeEmbedding2
#print axioms NSE_NOH.modeProjection2_modeEmbedding2
#check NSE_NOH.modeEmbedding2_modeProjection2
#print axioms NSE_NOH.modeEmbedding2_modeProjection2
#check NSE_NOH.x1zero_mode_iff_exists_planar_mode
#print axioms NSE_NOH.x1zero_mode_iff_exists_planar_mode
#check NSE_NOH.modeEmbedding2_injective
#print axioms NSE_NOH.modeEmbedding2_injective
#check NSE_NOH.GeometricLift.toNOHSolution
#print axioms NSE_NOH.GeometricLift.toNOHSolution
#check NSE_NOH.GeometryPorts.toAnalyticPorts
#print axioms NSE_NOH.GeometryPorts.toAnalyticPorts
#check NSE_NOH.from_geometry_ports
#print axioms NSE_NOH.from_geometry_ports
#check NSE_NOH.InvariantUniqueness

/- FIX8 exact rank-two Fourier and algebraic PDE jet edges. -/
#check NSE_NOH.X1ZeroModes
#check NSE_NOH.planarModesAddEquiv
#print axioms NSE_NOH.modeEmbedding2_add
#print axioms NSE_NOH.modeEmbedding2_neg
#print axioms NSE_NOH.planarModesAddEquiv
#print axioms NSE_NOH.x1zero_triad_closed
#print axioms NSE_NOH.x1zero_triad_target
#check NSE_NOH.NSEJet
#print axioms NSE_NOH.advectionJet_lift_scalar
#print axioms NSE_NOH.advectionJet_lift_planar_zero
#print axioms NSE_NOH.advectionJet_lift_planar_one
#print axioms NSE_NOH.divergenceJet_lift
#print axioms NSE_NOH.NSEJet_lift

/- FIX9: chain rule for actual lifted scalar functions (not just jets). -/
#check NSE_NOH.realProjection2CLM
#print axioms NSE_NOH.realProjection2CLM_apply
#print axioms NSE_NOH.fderiv_liftScalar
#print axioms NSE_NOH.coordinateDerivative_liftScalar_zero
#print axioms NSE_NOH.coordinateDerivative_liftScalar_one
#print axioms NSE_NOH.coordinateDerivative_liftScalar_two
#print axioms NSE_NOH.deriv_liftedVelocity_scalar
#print axioms NSE_NOH.deriv_liftedVelocity_planar_zero
#print axioms NSE_NOH.deriv_liftedVelocity_planar_one

/- FIX10: second spatial derivatives / actual Laplacian. -/
#check NSE_NOH.PlanarC2
#print axioms NSE_NOH.secondDerivative_liftScalar_zero
#print axioms NSE_NOH.secondDerivative_liftScalar_one
#print axioms NSE_NOH.secondDerivative_liftScalar_two
#print axioms NSE_NOH.spatialLaplacian_liftScalar

/- FIX10: full classical PDE from planar classical PDE + passive scalar. -/
#print axioms NSE_NOH.valueJet_liftedVelocity
#print axioms NSE_NOH.timeJet_liftedVelocity
#print axioms NSE_NOH.spatialJet_liftedVelocity
#print axioms NSE_NOH.pressureJet_liftedPressure
#print axioms NSE_NOH.lapJet_liftedVelocity
#check NSE_NOH.ClassicalNSE_lift_of_planar
#print axioms NSE_NOH.ClassicalNSE_lift_of_planar

/- FIX13 pointwise kinetic and dissipation densities (no L² existence). -/
#print axioms NSE_NOH.squareMassDensity_liftedVelocity
#print axioms NSE_NOH.scalarGradDensity_lift
#print axioms NSE_NOH.vectorGradDensity_liftedVelocity
#print axioms NSE_NOH.pointwiseEnergyDissipation_liftedVelocity

/- FIX14: Actual normalized-torus projection and integrated kinetic mass. -/
#check NSE_NOH.torusProjection2_measurePreserving
#print axioms NSE_NOH.torusProjection2_measurePreserving
#check NSE_NOH.integral_torusProjection2
#print axioms NSE_NOH.integral_torusProjection2
#check NSE_NOH.squareMassDensity_torusLiftedVector
#print axioms NSE_NOH.squareMassDensity_torusLiftedVector
#check NSE_NOH.integral_squareMassDensity_torusLiftedVector
#print axioms NSE_NOH.integral_squareMassDensity_torusLiftedVector

/- FIX16: arbitrary rough L² scalar/vector pullbacks and strong-trace transfer. -/
#check NSE_NOH.scalarL2Pullback
#check NSE_NOH.planarL2Pullback
#print axioms NSE_NOH.scalarL2Pullback_ae
#print axioms NSE_NOH.planarL2Pullback_ae
#print axioms NSE_NOH.scalarL2Pullback_norm
#print axioms NSE_NOH.planarL2Pullback_norm
#print axioms NSE_NOH.scalarL2Pullback_dist
#print axioms NSE_NOH.planarL2Pullback_dist
#print axioms NSE_NOH.scalarL2Pullback_injective
#print axioms NSE_NOH.planarL2Pullback_injective
#print axioms NSE_NOH.scalarL2Pullback_strongTrace
#print axioms NSE_NOH.planarL2Pullback_strongTrace
#print axioms NSE_NOH.scalarL2Pullback_mass

/- FIX17: closed L² planar pullback ranges and exact limit factorization. -/
#check NSE_NOH.ScalarL2Three
#check NSE_NOH.PlanarL2Three
#check NSE_NOH.scalarL2Pullback_closedRange
#print axioms NSE_NOH.scalarL2Pullback_closedRange
#check NSE_NOH.planarL2Pullback_closedRange
#print axioms NSE_NOH.planarL2Pullback_closedRange
#check NSE_NOH.scalarL2Pullback_closure_iff
#print axioms NSE_NOH.scalarL2Pullback_closure_iff
#check NSE_NOH.planarL2Pullback_closure_iff
#print axioms NSE_NOH.planarL2Pullback_closure_iff
#print axioms NSE_NOH.scalarL2Pullback_uniqueFactorization
#print axioms NSE_NOH.planarL2Pullback_uniqueFactorization
#print axioms NSE_NOH.scalarL2Pullback_approximationFactorization
#print axioms NSE_NOH.planarL2Pullback_approximationFactorization
#print axioms NSE_NOH.scalarL2Pullback_tendsto_iff
#print axioms NSE_NOH.planarL2Pullback_tendsto_iff
#check NSE_NOH.scalarL2Pullback_limitFactorization
#print axioms NSE_NOH.scalarL2Pullback_limitFactorization
#check NSE_NOH.planarL2Pullback_limitFactorization
#print axioms NSE_NOH.planarL2Pullback_limitFactorization

/- FIX20: actual complex L² Fourier support factorization. -/
#check NSE_NOH.complexL2Pullback
#print axioms NSE_NOH.mFourier_modeEmbedding2
#print axioms NSE_NOH.mFourier_zeroFirst
#print axioms NSE_NOH.finiteFourier3_zeroFirst_factorization
#print axioms NSE_NOH.torusProjection2_update_first
#print axioms NSE_NOH.finiteFourier3_zeroFirst_invariant
#print axioms NSE_NOH.complexL2Pullback_closedRange
#print axioms NSE_NOH.complexL2Pullback_fourierMode
#print axioms NSE_NOH.complexL2_zeroFirstSpectral_factorization

/- FIX21: actual torus Bochner weak-mode integrals and factorization. -/
#check NSE_NOH.firstFourierMultiplier
#check NSE_NOH.firstFourierModeTest
#print axioms NSE_NOH.firstFourierModeTest_eq_multiplier
#print axioms NSE_NOH.firstFourierMultiplier_ne_zero
#print axioms NSE_NOH.firstFourierModeTest_zero_iff_zeroFirst
#print axioms NSE_NOH.complexL2_firstFourierModeTest_factorization
#check NSE_NOH.ThreeComponentFirstFourierModeTestZero
#print axioms NSE_NOH.complexL2_threeComponentFirstFourierModeTest_factorization
