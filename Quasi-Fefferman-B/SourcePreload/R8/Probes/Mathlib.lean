import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.MulAction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Fourier.AddCircleMulti

/-
R8 SOURCE-ONLY API PROBE.
PINNED_LEAN = 4.33.0.
PINNED_MATHLIB = db584cd6d46c92f209a44c0f1c829460d327499d.
PINNED_FOUNDATION = 09dfe94a1ef150e21d09df3013fbe09002ef139c.
EXECUTION_STATUS = NOT_EXECUTED.
SOURCE_SNAPSHOTS_ARE_NOT_A_COMPLETE_DEPENDENCY_INSTALLATION.
-/

-- Mathlib/Data/Finset/Prod.lean:53; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.Finset.product_eq_sprod
-- Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:80; PINNED_SOURCE_TO_ADDITIVE_GENERATED
#check @_root_.Finset.sum_product
-- Mathlib/Algebra/BigOperators/Ring/Finset.lean:62; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.Finset.sum_mul_sum
-- Mathlib/Analysis/Calculus/Deriv/Basic.lean:602; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.HasDerivAt.congr_deriv
-- Mathlib/Analysis/Calculus/Deriv/Mul.lean:109; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.HasDerivAt.smul
-- Mathlib/Analysis/InnerProductSpace/Calculus.lean:109; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.HasDerivAt.inner
-- Mathlib/Analysis/Normed/Lp/PiLp.lean:97; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.PiLp.ext
-- Mathlib/Topology/Algebra/Monoid.lean:960; PINNED_SOURCE_TO_ADDITIVE_GENERATED
#check @_root_.continuousOn_finsetSum
-- Mathlib/Topology/Algebra/MulAction.lean:132; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.ContinuousOn.smul
-- Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:506; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.ContinuousOn.intervalIntegrable_of_Icc
-- Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:150; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.intervalIntegrable_iff_integrableOn_Ioo_of_le
-- Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1140; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
-- Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:474; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.MeasureTheory.tendstoInMeasure_of_tendsto_Lp
-- Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:277; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae
-- Mathlib/MeasureTheory/Measure/Restrict.lean:627; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.MeasureTheory.ae_restrict_iff'
-- Mathlib/MeasureTheory/Measure/Restrict.lean:655; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset
-- Mathlib/MeasureTheory/OuterMeasure/AE.lean:97; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.MeasureTheory.ae_all_iff
-- Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:57; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.MeasureTheory.tendsto_integral_of_dominated_convergence
-- Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean:485; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.MeasureTheory.memLp_congr_ae
-- Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:111; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.MeasureTheory.MemLp.coeFn_toLp
-- Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:167; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.MeasureTheory.Lp.toLp_coeFn
-- Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:201; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.MeasureTheory.Lp.coeFn_sub
-- Mathlib/Analysis/Real/Sqrt.lean:144; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.Real.sqrt_nonneg
-- Mathlib/Analysis/Real/Sqrt.lean:178; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.Real.sq_sqrt
-- Mathlib/Analysis/Real/Sqrt.lean:221; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.Real.sqrt_lt_sqrt
-- Mathlib/Topology/Algebra/InfiniteSum/Order.lean:149; PINNED_SOURCE_TO_ADDITIVE_GENERATED
#check @_root_.tsum_le_of_sum_le'
-- Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:237; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.MeasureTheory.integral_add
-- Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:288; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.MeasureTheory.integral_const_mul
-- Mathlib/Analysis/Fourier/AddCircleMulti.lean:169; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.UnitAddTorus.measurePreserving_equivPiIoc
-- Mathlib/Analysis/Real/Sqrt.lean:286; PINNED_SOURCE_DIRECT_DECLARATION
#check @_root_.Real.sqrt_pos
