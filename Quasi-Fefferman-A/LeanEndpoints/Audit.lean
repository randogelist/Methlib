import QFA

set_option pp.universes false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.width 200

#eval IO.println "TYPE_BEGIN:QFA.Energy.envelope_zero"
#check @QFA.Energy.envelope_zero
#eval IO.println "TYPE_END:QFA.Energy.envelope_zero"
#print axioms QFA.Energy.envelope_zero

#eval IO.println "TYPE_BEGIN:QFA.Energy.envelope_absolutelyContinuousOnInterval"
#check @QFA.Energy.envelope_absolutelyContinuousOnInterval
#eval IO.println "TYPE_END:QFA.Energy.envelope_absolutelyContinuousOnInterval"
#print axioms QFA.Energy.envelope_absolutelyContinuousOnInterval

#eval IO.println "TYPE_BEGIN:QFA.Energy.envelope_hasDerivAt_ae"
#check @QFA.Energy.envelope_hasDerivAt_ae
#eval IO.println "TYPE_END:QFA.Energy.envelope_hasDerivAt_ae"
#print axioms QFA.Energy.envelope_hasDerivAt_ae

#eval IO.println "TYPE_BEGIN:QFA.Energy.envelope_product_intervalIntegrable"
#check @QFA.Energy.envelope_product_intervalIntegrable
#eval IO.println "TYPE_END:QFA.Energy.envelope_product_intervalIntegrable"
#print axioms QFA.Energy.envelope_product_intervalIntegrable

#eval IO.println "TYPE_BEGIN:QFA.Energy.envelope_product_integral"
#check @QFA.Energy.envelope_product_integral
#eval IO.println "TYPE_END:QFA.Energy.envelope_product_integral"
#print axioms QFA.Energy.envelope_product_integral

#eval IO.println "TYPE_BEGIN:QFA.Energy.product_budget_of_envelope_identity"
#check @QFA.Energy.product_budget_of_envelope_identity
#eval IO.println "TYPE_END:QFA.Energy.product_budget_of_envelope_identity"
#print axioms QFA.Energy.product_budget_of_envelope_identity

#eval IO.println "TYPE_BEGIN:QFA.Energy.product_budget"
#check @QFA.Energy.product_budget
#eval IO.println "TYPE_END:QFA.Energy.product_budget"
#print axioms QFA.Energy.product_budget

#eval IO.println "TYPE_BEGIN:QFA.Energy.product_budget_Ioo"
#check @QFA.Energy.product_budget_Ioo
#eval IO.println "TYPE_END:QFA.Energy.product_budget_Ioo"
#print axioms QFA.Energy.product_budget_Ioo

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.GoodTime.qfa_cutoff_nonneg"
#check @QFA.Endpoints.GoodTime.qfa_cutoff_nonneg
#eval IO.println "TYPE_END:QFA.Endpoints.GoodTime.qfa_cutoff_nonneg"
#print axioms QFA.Endpoints.GoodTime.qfa_cutoff_nonneg

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.GoodTime.qfa_budget_lt_threshold"
#check @QFA.Endpoints.GoodTime.qfa_budget_lt_threshold
#eval IO.println "TYPE_END:QFA.Endpoints.GoodTime.qfa_budget_lt_threshold"
#print axioms QFA.Endpoints.GoodTime.qfa_budget_lt_threshold

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.GoodTime.exists_good_time_of_integral_lt"
#check @QFA.Endpoints.GoodTime.exists_good_time_of_integral_lt
#eval IO.println "TYPE_END:QFA.Endpoints.GoodTime.exists_good_time_of_integral_lt"
#print axioms QFA.Endpoints.GoodTime.exists_good_time_of_integral_lt

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.GoodTime.exists_subcritical_product_good_time"
#check @QFA.Endpoints.GoodTime.exists_subcritical_product_good_time
#eval IO.println "TYPE_END:QFA.Endpoints.GoodTime.exists_subcritical_product_good_time"
#print axioms QFA.Endpoints.GoodTime.exists_subcritical_product_good_time

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.GoodTime.exists_subcritical_product_good_time_of_interval_budget"
#check @QFA.Endpoints.GoodTime.exists_subcritical_product_good_time_of_interval_budget
#eval IO.println "TYPE_END:QFA.Endpoints.GoodTime.exists_subcritical_product_good_time_of_interval_budget"
#print axioms QFA.Endpoints.GoodTime.exists_subcritical_product_good_time_of_interval_budget

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Composition.exists_subcritical_good_time_of_envelope"
#check @QFA.Endpoints.Composition.exists_subcritical_good_time_of_envelope
#eval IO.println "TYPE_END:QFA.Endpoints.Composition.exists_subcritical_good_time_of_envelope"
#print axioms QFA.Endpoints.Composition.exists_subcritical_good_time_of_envelope

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Agmon.agmon_fourth_power"
#check @QFA.Endpoints.Agmon.agmon_fourth_power
#eval IO.println "TYPE_END:QFA.Endpoints.Agmon.agmon_fourth_power"
#print axioms QFA.Endpoints.Agmon.agmon_fourth_power

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Agmon.nonlinear_fourth_power_of_agmon_fourth"
#check @QFA.Endpoints.Agmon.nonlinear_fourth_power_of_agmon_fourth
#eval IO.println "TYPE_END:QFA.Endpoints.Agmon.nonlinear_fourth_power_of_agmon_fourth"
#print axioms QFA.Endpoints.Agmon.nonlinear_fourth_power_of_agmon_fourth

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Agmon.ScalarProfile.nonlinear_fourth_power"
#check @QFA.Endpoints.Agmon.ScalarProfile.nonlinear_fourth_power
#eval IO.println "TYPE_END:QFA.Endpoints.Agmon.ScalarProfile.nonlinear_fourth_power"
#print axioms QFA.Endpoints.Agmon.ScalarProfile.nonlinear_fourth_power

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Agmon.nonlinear_le_of_product_le"
#check @QFA.Endpoints.Agmon.nonlinear_le_of_product_le
#eval IO.println "TYPE_END:QFA.Endpoints.Agmon.nonlinear_le_of_product_le"
#print axioms QFA.Endpoints.Agmon.nonlinear_le_of_product_le

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Agmon.nonlinearCoefficient_nonneg"
#check @QFA.Endpoints.Agmon.nonlinearCoefficient_nonneg
#eval IO.println "TYPE_END:QFA.Endpoints.Agmon.nonlinearCoefficient_nonneg"
#print axioms QFA.Endpoints.Agmon.nonlinearCoefficient_nonneg

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Agmon.nonlinearCoefficient_fourth"
#check @QFA.Endpoints.Agmon.nonlinearCoefficient_fourth
#eval IO.println "TYPE_END:QFA.Endpoints.Agmon.nonlinearCoefficient_fourth"
#print axioms QFA.Endpoints.Agmon.nonlinearCoefficient_fourth

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Agmon.ScalarProfile.nonlinear_le_coefficient"
#check @QFA.Endpoints.Agmon.ScalarProfile.nonlinear_le_coefficient
#eval IO.println "TYPE_END:QFA.Endpoints.Agmon.ScalarProfile.nonlinear_le_coefficient"
#print axioms QFA.Endpoints.Agmon.ScalarProfile.nonlinear_le_coefficient

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Agmon.ScalarProfile.nonlinear_eq_zero_of_laplacian_eq_zero"
#check @QFA.Endpoints.Agmon.ScalarProfile.nonlinear_eq_zero_of_laplacian_eq_zero
#eval IO.println "TYPE_END:QFA.Endpoints.Agmon.ScalarProfile.nonlinear_eq_zero_of_laplacian_eq_zero"
#print axioms QFA.Endpoints.Agmon.ScalarProfile.nonlinear_eq_zero_of_laplacian_eq_zero

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Agmon.nonlinearCoefficient_lt_viscosity"
#check @QFA.Endpoints.Agmon.nonlinearCoefficient_lt_viscosity
#eval IO.println "TYPE_END:QFA.Endpoints.Agmon.nonlinearCoefficient_lt_viscosity"
#print axioms QFA.Endpoints.Agmon.nonlinearCoefficient_lt_viscosity

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Agmon.ScalarProfile.enstrophy_absorption"
#check @QFA.Endpoints.Agmon.ScalarProfile.enstrophy_absorption
#eval IO.println "TYPE_END:QFA.Endpoints.Agmon.ScalarProfile.enstrophy_absorption"
#print axioms QFA.Endpoints.Agmon.ScalarProfile.enstrophy_absorption

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Agmon.ScalarProfile.viscosity_margin_pos"
#check @QFA.Endpoints.Agmon.ScalarProfile.viscosity_margin_pos
#eval IO.println "TYPE_END:QFA.Endpoints.Agmon.ScalarProfile.viscosity_margin_pos"
#print axioms QFA.Endpoints.Agmon.ScalarProfile.viscosity_margin_pos

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Comparison.CRITICAL_ADMISSIBLE_TIMES_TENDSTO_ZERO"
#check @QFA.Endpoints.Comparison.CRITICAL_ADMISSIBLE_TIMES_TENDSTO_ZERO
#eval IO.println "TYPE_END:QFA.Endpoints.Comparison.CRITICAL_ADMISSIBLE_TIMES_TENDSTO_ZERO"
#print axioms QFA.Endpoints.Comparison.CRITICAL_ADMISSIBLE_TIMES_TENDSTO_ZERO

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Comparison.critical_comparison_differential_gronwall"
#check @QFA.Endpoints.Comparison.critical_comparison_differential_gronwall
#eval IO.println "TYPE_END:QFA.Endpoints.Comparison.critical_comparison_differential_gronwall"
#print axioms QFA.Endpoints.Comparison.critical_comparison_differential_gronwall

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Comparison.CRITICAL_RELATIVE_ENERGY_GRONWALL"
#check @QFA.Endpoints.Comparison.CRITICAL_RELATIVE_ENERGY_GRONWALL
#eval IO.println "TYPE_END:QFA.Endpoints.Comparison.CRITICAL_RELATIVE_ENERGY_GRONWALL"
#print axioms QFA.Endpoints.Comparison.CRITICAL_RELATIVE_ENERGY_GRONWALL

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Comparison.CRITICAL_RELATIVE_ENERGY_ZERO_OF_ADMISSIBLE_TRACE"
#check @QFA.Endpoints.Comparison.CRITICAL_RELATIVE_ENERGY_ZERO_OF_ADMISSIBLE_TRACE
#eval IO.println "TYPE_END:QFA.Endpoints.Comparison.CRITICAL_RELATIVE_ENERGY_ZERO_OF_ADMISSIBLE_TRACE"
#print axioms QFA.Endpoints.Comparison.CRITICAL_RELATIVE_ENERGY_ZERO_OF_ADMISSIBLE_TRACE

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Comparison.CRITICAL_COMPARISON_EQ_OF_ADMISSIBLE_TRACE"
#check @QFA.Endpoints.Comparison.CRITICAL_COMPARISON_EQ_OF_ADMISSIBLE_TRACE
#eval IO.println "TYPE_END:QFA.Endpoints.Comparison.CRITICAL_COMPARISON_EQ_OF_ADMISSIBLE_TRACE"
#print axioms QFA.Endpoints.Comparison.CRITICAL_COMPARISON_EQ_OF_ADMISSIBLE_TRACE

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyVectorLI"
#check @QFA.Endpoints.Representation.complexifyVectorLI
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyVectorLI"
#print axioms QFA.Endpoints.Representation.complexifyVectorLI

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyVectorLI_apply"
#check @QFA.Endpoints.Representation.complexifyVectorLI_apply
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyVectorLI_apply"
#print axioms QFA.Endpoints.Representation.complexifyVectorLI_apply

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyVectorLI_zero"
#check @QFA.Endpoints.Representation.complexifyVectorLI_zero
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyVectorLI_zero"
#print axioms QFA.Endpoints.Representation.complexifyVectorLI_zero

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyVectorLI_norm"
#check @QFA.Endpoints.Representation.complexifyVectorLI_norm
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyVectorLI_norm"
#print axioms QFA.Endpoints.Representation.complexifyVectorLI_norm

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyVectorLI_norm_sq"
#check @QFA.Endpoints.Representation.complexifyVectorLI_norm_sq
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyVectorLI_norm_sq"
#print axioms QFA.Endpoints.Representation.complexifyVectorLI_norm_sq

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyVectorLI_isometry"
#check @QFA.Endpoints.Representation.complexifyVectorLI_isometry
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyVectorLI_isometry"
#print axioms QFA.Endpoints.Representation.complexifyVectorLI_isometry

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyL2_ae"
#check @QFA.Endpoints.Representation.complexifyL2_ae
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyL2_ae"
#print axioms QFA.Endpoints.Representation.complexifyL2_ae

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyL2_norm"
#check @QFA.Endpoints.Representation.complexifyL2_norm
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyL2_norm"
#print axioms QFA.Endpoints.Representation.complexifyL2_norm

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyL2_add"
#check @QFA.Endpoints.Representation.complexifyL2_add
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyL2_add"
#print axioms QFA.Endpoints.Representation.complexifyL2_add

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyL2_smul"
#check @QFA.Endpoints.Representation.complexifyL2_smul
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyL2_smul"
#print axioms QFA.Endpoints.Representation.complexifyL2_smul

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyL2LI"
#check @QFA.Endpoints.Representation.complexifyL2LI
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyL2LI"
#print axioms QFA.Endpoints.Representation.complexifyL2LI

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyL2_isometry"
#check @QFA.Endpoints.Representation.complexifyL2_isometry
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyL2_isometry"
#print axioms QFA.Endpoints.Representation.complexifyL2_isometry

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyL2_zero"
#check @QFA.Endpoints.Representation.complexifyL2_zero
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyL2_zero"
#print axioms QFA.Endpoints.Representation.complexifyL2_zero

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyL2_velocityEnergy"
#check @QFA.Endpoints.Representation.complexifyL2_velocityEnergy
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyL2_velocityEnergy"
#print axioms QFA.Endpoints.Representation.complexifyL2_velocityEnergy

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyL2_gradientEnergy"
#check @QFA.Endpoints.Representation.complexifyL2_gradientEnergy
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyL2_gradientEnergy"
#print axioms QFA.Endpoints.Representation.complexifyL2_gradientEnergy

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyL2_laplacianEnergy"
#check @QFA.Endpoints.Representation.complexifyL2_laplacianEnergy
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyL2_laplacianEnergy"
#print axioms QFA.Endpoints.Representation.complexifyL2_laplacianEnergy

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.integrable_compact_test_smul"
#check @QFA.Endpoints.Representation.integrable_compact_test_smul
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.integrable_compact_test_smul"
#print axioms QFA.Endpoints.Representation.integrable_compact_test_smul

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.integral_test_smul_complexifyL2"
#check @QFA.Endpoints.Representation.integral_test_smul_complexifyL2
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.integral_test_smul_complexifyL2"
#print axioms QFA.Endpoints.Representation.integral_test_smul_complexifyL2

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.weakTestIdentity_complexify"
#check @QFA.Endpoints.Representation.weakTestIdentity_complexify
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.weakTestIdentity_complexify"
#print axioms QFA.Endpoints.Representation.weakTestIdentity_complexify

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.complexifyL2_weakDirectionalDerivative"
#check @QFA.Endpoints.Representation.complexifyL2_weakDirectionalDerivative
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.complexifyL2_weakDirectionalDerivative"
#print axioms QFA.Endpoints.Representation.complexifyL2_weakDirectionalDerivative

#eval IO.println "TYPE_BEGIN:QFA.Representation.velocityEnergy_nonneg"
#check @QFA.Representation.velocityEnergy_nonneg
#eval IO.println "TYPE_END:QFA.Representation.velocityEnergy_nonneg"
#print axioms QFA.Representation.velocityEnergy_nonneg

#eval IO.println "TYPE_BEGIN:QFA.Representation.gradientEnergy_nonneg"
#check @QFA.Representation.gradientEnergy_nonneg
#eval IO.println "TYPE_END:QFA.Representation.gradientEnergy_nonneg"
#print axioms QFA.Representation.gradientEnergy_nonneg

#eval IO.println "TYPE_BEGIN:QFA.Representation.EnergyProfile.velocityEnergy_aestronglyMeasurable"
#check @QFA.Representation.EnergyProfile.velocityEnergy_aestronglyMeasurable
#eval IO.println "TYPE_END:QFA.Representation.EnergyProfile.velocityEnergy_aestronglyMeasurable"
#print axioms QFA.Representation.EnergyProfile.velocityEnergy_aestronglyMeasurable

#eval IO.println "TYPE_BEGIN:QFA.Representation.EnergyProfile.gradientEnergy_integrable"
#check @QFA.Representation.EnergyProfile.gradientEnergy_integrable
#eval IO.println "TYPE_END:QFA.Representation.EnergyProfile.gradientEnergy_integrable"
#print axioms QFA.Representation.EnergyProfile.gradientEnergy_integrable

#eval IO.println "TYPE_BEGIN:QFA.Representation.EnergyProfile.gradientEnergy_intervalIntegrable"
#check @QFA.Representation.EnergyProfile.gradientEnergy_intervalIntegrable
#eval IO.println "TYPE_END:QFA.Representation.EnergyProfile.gradientEnergy_intervalIntegrable"
#print axioms QFA.Representation.EnergyProfile.gradientEnergy_intervalIntegrable

#eval IO.println "TYPE_BEGIN:QFA.Representation.EnergyProfile.velocityEnergy_le_envelope"
#check @QFA.Representation.EnergyProfile.velocityEnergy_le_envelope
#eval IO.println "TYPE_END:QFA.Representation.EnergyProfile.velocityEnergy_le_envelope"
#print axioms QFA.Representation.EnergyProfile.velocityEnergy_le_envelope

#eval IO.println "TYPE_BEGIN:QFA.Representation.EnergyProfile.velocityEnergy_le_envelope_ae"
#check @QFA.Representation.EnergyProfile.velocityEnergy_le_envelope_ae
#eval IO.println "TYPE_END:QFA.Representation.EnergyProfile.velocityEnergy_le_envelope_ae"
#print axioms QFA.Representation.EnergyProfile.velocityEnergy_le_envelope_ae

#eval IO.println "TYPE_BEGIN:QFA.Representation.EnergyProfile.energy_product_budget_Ioo"
#check @QFA.Representation.EnergyProfile.energy_product_budget_Ioo
#eval IO.println "TYPE_END:QFA.Representation.EnergyProfile.energy_product_budget_Ioo"
#print axioms QFA.Representation.EnergyProfile.energy_product_budget_Ioo

#eval IO.println "TYPE_BEGIN:QFA.Representation.EnergyProfile.exists_subcritical_good_time"
#check @QFA.Representation.EnergyProfile.exists_subcritical_good_time
#eval IO.println "TYPE_END:QFA.Representation.EnergyProfile.exists_subcritical_good_time"
#print axioms QFA.Representation.EnergyProfile.exists_subcritical_good_time

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Restart.timeTranslate_tendsto_nhdsWithin_right"
#check @QFA.Endpoints.Restart.timeTranslate_tendsto_nhdsWithin_right
#eval IO.println "TYPE_END:QFA.Endpoints.Restart.timeTranslate_tendsto_nhdsWithin_right"
#print axioms QFA.Endpoints.Restart.timeTranslate_tendsto_nhdsWithin_right

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Restart.timeTranslate_measurePreserving_Ioc"
#check @QFA.Endpoints.Restart.timeTranslate_measurePreserving_Ioc
#eval IO.println "TYPE_END:QFA.Endpoints.Restart.timeTranslate_measurePreserving_Ioc"
#print axioms QFA.Endpoints.Restart.timeTranslate_measurePreserving_Ioc

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Restart.timeTranslate_memLp_Ioc"
#check @QFA.Endpoints.Restart.timeTranslate_memLp_Ioc
#eval IO.println "TYPE_END:QFA.Endpoints.Restart.timeTranslate_memLp_Ioc"
#print axioms QFA.Endpoints.Restart.timeTranslate_memLp_Ioc

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Restart.timeTranslate_ae_Ioc"
#check @QFA.Endpoints.Restart.timeTranslate_ae_Ioc
#eval IO.println "TYPE_END:QFA.Endpoints.Restart.timeTranslate_ae_Ioc"
#print axioms QFA.Endpoints.Restart.timeTranslate_ae_Ioc

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Restart.timeTranslate_intervalIntegral"
#check @QFA.Endpoints.Restart.timeTranslate_intervalIntegral
#eval IO.println "TYPE_END:QFA.Endpoints.Restart.timeTranslate_intervalIntegral"
#print axioms QFA.Endpoints.Restart.timeTranslate_intervalIntegral

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Restart.timeTranslate_intervalIntegrable"
#check @QFA.Endpoints.Restart.timeTranslate_intervalIntegrable
#eval IO.println "TYPE_END:QFA.Endpoints.Restart.timeTranslate_intervalIntegrable"
#print axioms QFA.Endpoints.Restart.timeTranslate_intervalIntegrable

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Restart.timeTranslate_dissipation_intervalIntegrable"
#check @QFA.Endpoints.Restart.timeTranslate_dissipation_intervalIntegrable
#eval IO.println "TYPE_END:QFA.Endpoints.Restart.timeTranslate_dissipation_intervalIntegrable"
#print axioms QFA.Endpoints.Restart.timeTranslate_dissipation_intervalIntegrable

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Restart.energy_le_of_energy_start"
#check @QFA.Endpoints.Restart.energy_le_of_energy_start
#eval IO.println "TYPE_END:QFA.Endpoints.Restart.energy_le_of_energy_start"
#print axioms QFA.Endpoints.Restart.energy_le_of_energy_start

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Restart.timeTranslate_energy_from_start"
#check @QFA.Endpoints.Restart.timeTranslate_energy_from_start
#eval IO.println "TYPE_END:QFA.Endpoints.Restart.timeTranslate_energy_from_start"
#print axioms QFA.Endpoints.Restart.timeTranslate_energy_from_start

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Restart.timeTranslate_energy_intervals"
#check @QFA.Endpoints.Restart.timeTranslate_energy_intervals
#eval IO.println "TYPE_END:QFA.Endpoints.Restart.timeTranslate_energy_intervals"
#print axioms QFA.Endpoints.Restart.timeTranslate_energy_intervals

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Restart.strong_tendsto_of_inner_and_norm_bound"
#check @QFA.Endpoints.Restart.strong_tendsto_of_inner_and_norm_bound
#eval IO.println "TYPE_END:QFA.Endpoints.Restart.strong_tendsto_of_inner_and_norm_bound"
#print axioms QFA.Endpoints.Restart.strong_tendsto_of_inner_and_norm_bound

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Restart.strong_right_trace_of_energy_start"
#check @QFA.Endpoints.Restart.strong_right_trace_of_energy_start
#eval IO.println "TYPE_END:QFA.Endpoints.Restart.strong_right_trace_of_energy_start"
#print axioms QFA.Endpoints.Restart.strong_right_trace_of_energy_start

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Restart.shifted_strong_trace_of_energy_start"
#check @QFA.Endpoints.Restart.shifted_strong_trace_of_energy_start
#eval IO.println "TYPE_END:QFA.Endpoints.Restart.shifted_strong_trace_of_energy_start"
#print axioms QFA.Endpoints.Restart.shifted_strong_trace_of_energy_start

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Composition.exists_subcritical_good_time_with_strong_trace"
#check @QFA.Endpoints.Composition.exists_subcritical_good_time_with_strong_trace
#eval IO.println "TYPE_END:QFA.Endpoints.Composition.exists_subcritical_good_time_with_strong_trace"
#print axioms QFA.Endpoints.Composition.exists_subcritical_good_time_with_strong_trace
