import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.PartitionOfUnity

/-!
# VAR_STABLE Mathlib endpoint collection

Import-and-check module only. No new theorem is asserted here.
-/

set_option autoImplicit false

namespace SingularClosure
namespace VAR_STABLE

#check gronwallBound
#check norm_le_gronwallBound_of_norm_deriv_right_le
#check dist_le_of_approx_trajectories_ODE_of_mem
#check dist_le_of_approx_trajectories_ODE
#check dist_le_of_trajectories_ODE_of_mem
#check ContractingWith.exists_fixedPoint
#check ContractingWith.exists_fixedPoint'
#check ContractingWith.edist_efixedPoint_le
#check ContractingWith.edist_efixedPoint_le'
#check IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt
#check IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
#check ODE_solution_unique_of_mem_Icc_right

end VAR_STABLE
end SingularClosure
