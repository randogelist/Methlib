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
