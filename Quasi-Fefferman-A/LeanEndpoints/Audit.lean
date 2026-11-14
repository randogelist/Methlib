import QFA

set_option pp.universes false
set_option pp.explicit true
set_option pp.fullNames true

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

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Representation.complexifyL2_sum"
#check @QFA.Assembly.Representation.complexifyL2_sum
#eval IO.println "TYPE_END:QFA.Assembly.Representation.complexifyL2_sum"
#print axioms QFA.Assembly.Representation.complexifyL2_sum

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Representation.complexify_compactDerivativeData"
#check @QFA.Assembly.Representation.complexify_compactDerivativeData
#eval IO.println "TYPE_END:QFA.Assembly.Representation.complexify_compactDerivativeData"
#print axioms QFA.Assembly.Representation.complexify_compactDerivativeData

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Representation.schwartzWitnesses_of_compactData"
#check @QFA.Assembly.Representation.schwartzWitnesses_of_compactData
#eval IO.println "TYPE_END:QFA.Assembly.Representation.schwartzWitnesses_of_compactData"
#print axioms QFA.Assembly.Representation.schwartzWitnesses_of_compactData

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Representation.spectralRealization_of_compactData"
#check @QFA.Assembly.Representation.spectralRealization_of_compactData
#eval IO.println "TYPE_END:QFA.Assembly.Representation.spectralRealization_of_compactData"
#print axioms QFA.Assembly.Representation.spectralRealization_of_compactData

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Restart.timeTranslate_aestronglyMeasurable_Ioc"
#check @QFA.Assembly.Restart.timeTranslate_aestronglyMeasurable_Ioc
#eval IO.println "TYPE_END:QFA.Assembly.Restart.timeTranslate_aestronglyMeasurable_Ioc"
#print axioms QFA.Assembly.Restart.timeTranslate_aestronglyMeasurable_Ioc

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Restart.timeTranslate_aestronglyMeasurable_Ioo"
#check @QFA.Assembly.Restart.timeTranslate_aestronglyMeasurable_Ioo
#eval IO.println "TYPE_END:QFA.Assembly.Restart.timeTranslate_aestronglyMeasurable_Ioo"
#print axioms QFA.Assembly.Restart.timeTranslate_aestronglyMeasurable_Ioo

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Restart.timeTranslate_memLp_Ioo"
#check @QFA.Assembly.Restart.timeTranslate_memLp_Ioo
#eval IO.println "TYPE_END:QFA.Assembly.Restart.timeTranslate_memLp_Ioo"
#print axioms QFA.Assembly.Restart.timeTranslate_memLp_Ioo

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Restart.timeTranslate_weakPairingContinuousOn"
#check @QFA.Assembly.Restart.timeTranslate_weakPairingContinuousOn
#eval IO.println "TYPE_END:QFA.Assembly.Restart.timeTranslate_weakPairingContinuousOn"
#print axioms QFA.Assembly.Restart.timeTranslate_weakPairingContinuousOn

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Restart.energyProfile_timeTranslate"
#check @QFA.Assembly.Restart.energyProfile_timeTranslate
#eval IO.println "TYPE_END:QFA.Assembly.Restart.energyProfile_timeTranslate"
#print axioms QFA.Assembly.Restart.energyProfile_timeTranslate

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Restart.restartData_of_energyStart"
#check @QFA.Assembly.Restart.restartData_of_energyStart
#eval IO.println "TYPE_END:QFA.Assembly.Restart.restartData_of_energyStart"
#print axioms QFA.Assembly.Restart.restartData_of_energyStart

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Restart.exists_restartData_before"
#check @QFA.Assembly.Restart.exists_restartData_before
#eval IO.println "TYPE_END:QFA.Assembly.Restart.exists_restartData_before"
#print axioms QFA.Assembly.Restart.exists_restartData_before

#eval IO.println "TYPE_BEGIN:QFA.Assembly.AnalyticInputs.scalarProfile_of_field_estimates"
#check @QFA.Assembly.AnalyticInputs.scalarProfile_of_field_estimates
#eval IO.println "TYPE_END:QFA.Assembly.AnalyticInputs.scalarProfile_of_field_estimates"
#print axioms QFA.Assembly.AnalyticInputs.scalarProfile_of_field_estimates

#eval IO.println "TYPE_BEGIN:QFA.Assembly.AnalyticInputs.scalarProfile_of_complexified_field_estimates"
#check @QFA.Assembly.AnalyticInputs.scalarProfile_of_complexified_field_estimates
#eval IO.println "TYPE_END:QFA.Assembly.AnalyticInputs.scalarProfile_of_complexified_field_estimates"
#print axioms QFA.Assembly.AnalyticInputs.scalarProfile_of_complexified_field_estimates

#eval IO.println "TYPE_BEGIN:QFA.Assembly.AnalyticInputs.exists_scalarProfile_of_analytic_endpoints"
#check @QFA.Assembly.AnalyticInputs.exists_scalarProfile_of_analytic_endpoints
#eval IO.println "TYPE_END:QFA.Assembly.AnalyticInputs.exists_scalarProfile_of_analytic_endpoints"
#print axioms QFA.Assembly.AnalyticInputs.exists_scalarProfile_of_analytic_endpoints

#eval IO.println "TYPE_BEGIN:QFA.Assembly.AnalyticInputs.nonlinear_estimates_of_analytic_endpoints"
#check @QFA.Assembly.AnalyticInputs.nonlinear_estimates_of_analytic_endpoints
#eval IO.println "TYPE_END:QFA.Assembly.AnalyticInputs.nonlinear_estimates_of_analytic_endpoints"
#print axioms QFA.Assembly.AnalyticInputs.nonlinear_estimates_of_analytic_endpoints

#eval IO.println "TYPE_BEGIN:QFA.Assembly.AnalyticInputs.exists_positive_margin_of_analytic_endpoints"
#check @QFA.Assembly.AnalyticInputs.exists_positive_margin_of_analytic_endpoints
#eval IO.println "TYPE_END:QFA.Assembly.AnalyticInputs.exists_positive_margin_of_analytic_endpoints"
#print axioms QFA.Assembly.AnalyticInputs.exists_positive_margin_of_analytic_endpoints

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Comparison.eq_on_Ioc_of_ae_relative_energy"
#check @QFA.Assembly.Comparison.eq_on_Ioc_of_ae_relative_energy
#eval IO.println "TYPE_END:QFA.Assembly.Comparison.eq_on_Ioc_of_ae_relative_energy"
#print axioms QFA.Assembly.Comparison.eq_on_Ioc_of_ae_relative_energy

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Comparison.eq_on_Icc_of_ae_relative_energy"
#check @QFA.Assembly.Comparison.eq_on_Icc_of_ae_relative_energy
#eval IO.println "TYPE_END:QFA.Assembly.Comparison.eq_on_Icc_of_ae_relative_energy"
#print axioms QFA.Assembly.Comparison.eq_on_Icc_of_ae_relative_energy

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Comparison.eq_on_nonnegative_of_ae_relative_energy"
#check @QFA.Assembly.Comparison.eq_on_nonnegative_of_ae_relative_energy
#eval IO.println "TYPE_END:QFA.Assembly.Comparison.eq_on_nonnegative_of_ae_relative_energy"
#print axioms QFA.Assembly.Comparison.eq_on_nonnegative_of_ae_relative_energy

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Comparison.restricted_class_eq_singleton_of_eq_on_nonnegative"
#check @QFA.Assembly.Comparison.restricted_class_eq_singleton_of_eq_on_nonnegative
#eval IO.println "TYPE_END:QFA.Assembly.Comparison.restricted_class_eq_singleton_of_eq_on_nonnegative"
#print axioms QFA.Assembly.Comparison.restricted_class_eq_singleton_of_eq_on_nonnegative

#eval IO.println "TYPE_BEGIN:QFA.Assembly.AnalyticChain.interpolation_of_nativeSpectralRealization"
#check @QFA.Assembly.AnalyticChain.interpolation_of_nativeSpectralRealization
#eval IO.println "TYPE_END:QFA.Assembly.AnalyticChain.interpolation_of_nativeSpectralRealization"
#print axioms QFA.Assembly.AnalyticChain.interpolation_of_nativeSpectralRealization

#eval IO.println "TYPE_BEGIN:QFA.Assembly.AnalyticChain.interpolationEndpoint_of_spectralEndpoint"
#check @QFA.Assembly.AnalyticChain.interpolationEndpoint_of_spectralEndpoint
#eval IO.println "TYPE_END:QFA.Assembly.AnalyticChain.interpolationEndpoint_of_spectralEndpoint"
#print axioms QFA.Assembly.AnalyticChain.interpolationEndpoint_of_spectralEndpoint

#eval IO.println "TYPE_BEGIN:QFA.Assembly.AnalyticChain.exists_profile_of_compactData"
#check @QFA.Assembly.AnalyticChain.exists_profile_of_compactData
#eval IO.println "TYPE_END:QFA.Assembly.AnalyticChain.exists_profile_of_compactData"
#print axioms QFA.Assembly.AnalyticChain.exists_profile_of_compactData

#eval IO.println "TYPE_BEGIN:QFA.Assembly.AnalyticChain.exists_absorption_of_compactData"
#check @QFA.Assembly.AnalyticChain.exists_absorption_of_compactData
#eval IO.println "TYPE_END:QFA.Assembly.AnalyticChain.exists_absorption_of_compactData"
#print axioms QFA.Assembly.AnalyticChain.exists_absorption_of_compactData

#eval IO.println "TYPE_BEGIN:QFA.Assembly.TailComparison.ComparisonData.eq_on_Icc"
#check @QFA.Assembly.TailComparison.ComparisonData.eq_on_Icc
#eval IO.println "TYPE_END:QFA.Assembly.TailComparison.ComparisonData.eq_on_Icc"
#print axioms QFA.Assembly.TailComparison.ComparisonData.eq_on_Icc

#eval IO.println "TYPE_BEGIN:QFA.Assembly.TailComparison.ComparableOnNonnegative.eq_on_nonnegative"
#check @QFA.Assembly.TailComparison.ComparableOnNonnegative.eq_on_nonnegative
#eval IO.println "TYPE_END:QFA.Assembly.TailComparison.ComparableOnNonnegative.eq_on_nonnegative"
#print axioms QFA.Assembly.TailComparison.ComparableOnNonnegative.eq_on_nonnegative

#eval IO.println "TYPE_BEGIN:QFA.Assembly.TailComparison.restricted_class_eq_singleton_of_comparable"
#check @QFA.Assembly.TailComparison.restricted_class_eq_singleton_of_comparable
#eval IO.println "TYPE_END:QFA.Assembly.TailComparison.restricted_class_eq_singleton_of_comparable"
#print axioms QFA.Assembly.TailComparison.restricted_class_eq_singleton_of_comparable

#eval IO.println "TYPE_BEGIN:QFA.Assembly.TailComparison.comparisonData_of_restartData"
#check @QFA.Assembly.TailComparison.comparisonData_of_restartData
#eval IO.println "TYPE_END:QFA.Assembly.TailComparison.comparisonData_of_restartData"
#print axioms QFA.Assembly.TailComparison.comparisonData_of_restartData

#eval IO.println "TYPE_BEGIN:QFA.Assembly.TailComparison.ComparableOnNonnegative.eq_on_tail"
#check @QFA.Assembly.TailComparison.ComparableOnNonnegative.eq_on_tail
#eval IO.println "TYPE_END:QFA.Assembly.TailComparison.ComparableOnNonnegative.eq_on_tail"
#print axioms QFA.Assembly.TailComparison.ComparableOnNonnegative.eq_on_tail

#eval IO.println "TYPE_BEGIN:QFA.Assembly.TailComparison.ComparableOnNonnegative.further_timeTranslate_eq"
#check @QFA.Assembly.TailComparison.ComparableOnNonnegative.further_timeTranslate_eq
#eval IO.println "TYPE_END:QFA.Assembly.TailComparison.ComparableOnNonnegative.further_timeTranslate_eq"
#print axioms QFA.Assembly.TailComparison.ComparableOnNonnegative.further_timeTranslate_eq

#eval IO.println "TYPE_BEGIN:QFA.Assembly.TailComparison.restricted_restart_class_eq_singleton"
#check @QFA.Assembly.TailComparison.restricted_restart_class_eq_singleton
#eval IO.println "TYPE_END:QFA.Assembly.TailComparison.restricted_restart_class_eq_singleton"
#print axioms QFA.Assembly.TailComparison.restricted_restart_class_eq_singleton

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Chain.exists_selected_reference_and_tail_singleton"
#check @QFA.Assembly.Chain.exists_selected_reference_and_tail_singleton
#eval IO.println "TYPE_END:QFA.Assembly.Chain.exists_selected_reference_and_tail_singleton"
#print axioms QFA.Assembly.Chain.exists_selected_reference_and_tail_singleton

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Chain.quantified_tail_assembly"
#check @QFA.Assembly.Chain.quantified_tail_assembly
#eval IO.println "TYPE_END:QFA.Assembly.Chain.quantified_tail_assembly"
#print axioms QFA.Assembly.Chain.quantified_tail_assembly

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Integrated.pointwiseAbsorption_of_analytic_inputs"
#check @QFA.Assembly.Integrated.pointwiseAbsorption_of_analytic_inputs
#eval IO.println "TYPE_END:QFA.Assembly.Integrated.pointwiseAbsorption_of_analytic_inputs"
#print axioms QFA.Assembly.Integrated.pointwiseAbsorption_of_analytic_inputs

#eval IO.println "TYPE_BEGIN:QFA.Assembly.Integrated.quantified_tail_assembly_of_analytic_inputs"
#check @QFA.Assembly.Integrated.quantified_tail_assembly_of_analytic_inputs
#eval IO.println "TYPE_END:QFA.Assembly.Integrated.quantified_tail_assembly_of_analytic_inputs"
#print axioms QFA.Assembly.Integrated.quantified_tail_assembly_of_analytic_inputs
