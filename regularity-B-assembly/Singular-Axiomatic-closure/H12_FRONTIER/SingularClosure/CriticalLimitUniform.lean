import SingularClosure.CriticalLimitTail
import SingularClosure.SobolevFourierConstraints

/-! Strong uniform H0 convergence from the actual critical state bound.
Weighted-lp lower semicontinuity constructs the half-order limit. Finite-mode
uniform convergence and the quantitative half-order tail yield uniform H0
convergence, with no H1 bound imposed at zero time.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter Metric MeasureTheory
open scoped BigOperators Topology Interval

namespace SingularClosure

noncomputable section

theorem criticalSobolev_limit_mem_and_norm_le
    {α : Type*} {l : Filter α} [l.NeBot]
    (q : ℤ) (u : α → CriticalSobolev q) (c : FourierCoeff) (B : ℝ)
    (hbound : ∀ n, ‖u n‖ ≤ B)
    (hcoeff : ∀ k i, Tendsto (fun n => criticalCoeff q (u n) k i) l (𝓝 (c k i))) :
    ∃ v : CriticalSobolev q, criticalCoeff q v = c ∧ ‖v‖ ≤ B := by
  have hrepr : ∀ n, ‖criticalSobolevRepr q (u n)‖ ≤ B := by
    intro n
    simpa only [(criticalSobolevRepr q).norm_map] using hbound n
  have hbounded : Bornology.IsBounded (range (fun n => criticalSobolevRepr q (u n))) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B, ?_⟩
    rintro z ⟨n, rfl⟩
    exact hrepr n
  have hconv : Tendsto
      (fun n => (criticalSobolevRepr q (u n) : FourierIndex → ℂ)) l
      (𝓝 (criticalWeightedCoeff q c)) := by
    apply tendsto_pi_nhds.mpr
    intro ki
    exact (hcoeff ki.1 ki.2).const_mul ((criticalHalfWeight ki.1 : ℂ) ^ q)
  have hmem : Memℓp (criticalWeightedCoeff q c) 2 := lp.memℓp_of_tendsto hbounded hconv
  let v : CriticalSobolev q := ⟨c, hmem⟩
  refine ⟨v, rfl, ?_⟩
  change ‖(⟨criticalWeightedCoeff q c, hmem⟩ : FourierVectorSequence)‖ ≤ B
  exact lp.norm_le_of_tendsto (Filter.Eventually.of_forall hrepr) hconv

private theorem critical_tendstoUniformly_sum
    {ι X E : Type*} [NormedAddCommGroup E]
    (S : Finset ι) (F : ι → ℕ → X → E) (f : ι → X → E)
    (h : ∀ i ∈ S, TendstoUniformly (F i) (f i) atTop) :
    TendstoUniformly (fun n x => ∑ i ∈ S, F i n x) (fun x => ∑ i ∈ S, f i x) atTop := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E)) atTop (𝓝 0)).tendstoUniformly_const
  | @insert i S hi ih =>
    have hhead := h i (Finset.mem_insert_self _ _)
    have htail := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi, Pi.add_def] using hhead.add htail

/-- Uniform convergence of finitely many Fourier coefficients gives uniform
convergence of the literal Hilbert-space cutoff. -/
theorem torusSobolevCutoff_tendstoUniformly_of_coeff
    {X : Type*} (s K : ℕ) (U : ℕ → X → TorusSobolev s) (u : X → TorusSobolev s)
    (hcoeff : ∀ k i, TendstoUniformly (fun n x => (U n x).val k i)
      (fun x => (u x).val k i) atTop) :
    TendstoUniformly (fun n x => torusSobolevCutoff s K (U n x))
      (fun x => torusSobolevCutoff s K (u x)) atTop := by
  have hone (ki : FourierIndex) :
      TendstoUniformly (fun n x => torusSobolevRankOne s ki (U n x))
        (fun x => torusSobolevRankOne s ki (u x)) atTop := by
    let A : ℂ →L[ℂ] TorusSobolev s :=
      (((torusSobolevRepr s).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
        (lp.singleContinuousLinearMap ℂ (fun _ : FourierIndex => ℂ) 2 ki)).comp
        (((torusSobolevWeight ki.1 : ℂ) ^ s) • ContinuousLinearMap.id ℂ ℂ)
    have h := A.uniformContinuous.comp_tendstoUniformly (hcoeff ki.1 ki.2)
    change TendstoUniformly (fun n x => (torusSobolevRepr s).symm
        (lp.single 2 ki ((torusSobolevWeight ki.1 : ℂ) ^ s * (U n x).val ki.1 ki.2)))
      (fun x => (torusSobolevRepr s).symm
        (lp.single 2 ki ((torusSobolevWeight ki.1 : ℂ) ^ s * (u x).val ki.1 ki.2))) atTop
    exact h
  have hsum := critical_tendstoUniformly_sum (sobolevCutoffIndices K)
    (fun ki n x => torusSobolevRankOne s ki (U n x))
    (fun ki x => torusSobolevRankOne s ki (u x)) (fun ki _ => hone ki)
  simpa only [torusSobolevCutoff_eq_sum_rankOne, ContinuousLinearMap.sum_apply] using hsum

/-- Half-order boundedness upgrades uniform coefficient convergence to uniform H0 convergence. -/
theorem critical_half_uniform_H0_of_coeff_uniform
    {X : Type*} (U : ℕ → X → CriticalSobolev 1) (u : X → CriticalSobolev 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hU : ∀ n x, ‖U n x‖ ≤ A) (hu : ∀ x, ‖u x‖ ≤ A)
    (hcoeff : ∀ k i, TendstoUniformly
      (fun n x => criticalCoeff 1 (U n x) k i)
      (fun x => criticalCoeff 1 (u x) k i) atTop) :
    TendstoUniformly (fun n x => criticalToTorusH0 1 (by norm_num) (U n x))
      (fun x => criticalToTorusH0 1 (by norm_num) (u x)) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (9 * A ^ 2 / ε ^ 2)
  let N := K + 1
  have hN : 0 < N := Nat.succ_pos K
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlarge : 9 * A ^ 2 < (N : ℝ) * ε ^ 2 := by
    have hKN : (K : ℝ) < N := by dsimp [N]; norm_cast; omega
    have hh : 9 * A ^ 2 / ε ^ 2 < (N : ℝ) := hK.trans hKN
    exact (div_lt_iff₀ (sq_pos_of_pos hε)).mp hh
  have hsmall : (N : ℝ)⁻¹ * A ^ 2 < (ε / 3) ^ 2 := by
    rw [mul_comm, ← div_eq_mul_inv]
    apply (div_lt_iff₀ hNr).mpr
    nlinarith
  have htail (v : CriticalSobolev 1) (hv : ‖v‖ ≤ A) :
      ‖criticalToTorusH0 1 (by norm_num) v -
        torusSobolevCutoff 0 N (criticalToTorusH0 1 (by norm_num) v)‖ < ε / 3 := by
    have hsq := (criticalToTorusH0_tail_sq N hN v).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2)
        (inv_nonneg.mpr hNr.le))
    exact (sq_lt_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ε / 3)).mp
      (hsq.trans_lt hsmall)
  have hhead := torusSobolevCutoff_tendstoUniformly_of_coeff 0 N
    (fun n x => criticalToTorusH0 1 (by norm_num) (U n x))
    (fun x => criticalToTorusH0 1 (by norm_num) (u x))
    (fun k i => by simpa only [criticalToTorusH0_coeff] using hcoeff k i)
  filter_upwards [Metric.tendstoUniformly_iff.mp hhead (ε / 3) (by positivity)] with n hn
  intro x
  have hn' : dist
      (torusSobolevCutoff 0 N (criticalToTorusH0 1 (by norm_num) (u x)))
      (torusSobolevCutoff 0 N (criticalToTorusH0 1 (by norm_num) (U n x))) < ε / 3 := hn x
  have hu' := htail (u x) (hu x)
  have hU' := htail (U n x) (hU n x)
  have htriangle := dist_triangle
    (criticalToTorusH0 1 (by norm_num) (u x))
    (torusSobolevCutoff 0 N (criticalToTorusH0 1 (by norm_num) (u x)))
    (criticalToTorusH0 1 (by norm_num) (U n x))
  have htriangle' := dist_triangle
    (torusSobolevCutoff 0 N (criticalToTorusH0 1 (by norm_num) (u x)))
    (torusSobolevCutoff 0 N (criticalToTorusH0 1 (by norm_num) (U n x)))
    (criticalToTorusH0 1 (by norm_num) (U n x))
  rw [← dist_eq_norm] at hu' hU'
  rw [dist_comm (criticalToTorusH0 1 (by norm_num) (U n x))] at hU'
  linarith

/-- Construction of a genuine half-order-valued limit with uniform H0 convergence. -/
theorem CRITICAL_GALERKIN_H0_UNIFORM_SUBSEQUENCE
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (T A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hstate : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖(g n).criticalState 1 t‖ ≤ A)
    (hbudget : ∀ n, (∫ t in (0 : ℝ)..T, ‖(g n).criticalRhs (-1) t‖ ^ 2) ≤ B) :
    ∃ u : Icc (0 : ℝ) T → CriticalSobolev 1, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ (∀ t, ‖u t‖ ≤ A) ∧
      Continuous (fun t => criticalToTorusH0 1 (by norm_num) (u t)) ∧
      TendstoUniformly (fun n (t : Icc (0 : ℝ) T) =>
        (g (φ n)).sobolevState 0 t.val)
        (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop := by
  classical
  obtain ⟨c, φ, hφ, hconv⟩ :=
    CRITICAL_GALERKIN_FOURIER_COMPACTNESS ν a N g T A B hA hB hstate hbudget
  have hex (t : Icc (0 : ℝ) T) : ∃ v : CriticalSobolev 1,
      criticalCoeff 1 v = (fun k i => c (k, i) t) ∧ ‖v‖ ≤ A := by
    apply criticalSobolev_limit_mem_and_norm_le (l := (atTop : Filter ℕ)) 1
      (fun n => (g (φ n)).criticalState 1 t.val) (fun k i => c (k, i) t) A
    · intro n
      exact hstate (φ n) t.val t.property
    · intro k i
      have heq (n : ℕ) : criticalCoeff 1 ((g (φ n)).criticalState 1 t.val) =
          (g (φ n)).coeff t.val := (g (φ n)).criticalState_coeff 1 t.property.1
      simpa only [heq] using (hconv k i).tendsto_at t
  choose u hucoeff hubound using hex
  have hcoeff' (k : Frequency) (i : Fin 3) : TendstoUniformly
      (fun n (t : Icc (0 : ℝ) T) =>
        criticalCoeff 1 ((g (φ n)).criticalState 1 t.val) k i)
      (fun t => criticalCoeff 1 (u t) k i) atTop := by
    have heq : (fun n (t : Icc (0 : ℝ) T) =>
        criticalCoeff 1 ((g (φ n)).criticalState 1 t.val) k i) =
        (fun n (t : Icc (0 : ℝ) T) => (g (φ n)).coeff t.val k i) := by
      funext n t
      rw [(g (φ n)).criticalState_coeff 1 t.property.1]
    have heq' : (fun t => criticalCoeff 1 (u t) k i) = (fun t => c (k, i) t) := by
      funext t
      exact congrArg (fun z : FourierCoeff => z k i) (hucoeff t)
    rw [heq, heq']
    exact hconv k i
  have hcrit := critical_half_uniform_H0_of_coeff_uniform
    (fun n (t : Icc (0 : ℝ) T) => (g (φ n)).criticalState 1 t.val) u A hA
    (fun n t => hstate (φ n) t.val t.property) hubound hcoeff'
  have hident (n : ℕ) (t : Icc (0 : ℝ) T) :
      criticalToTorusH0 1 (by norm_num) ((g (φ n)).criticalState 1 t.val) =
      (g (φ n)).sobolevState 0 t.val := by
    apply Subtype.ext
    rw [criticalToTorusH0_coeff, (g (φ n)).criticalState_coeff 1 t.property.1,
      (g (φ n)).sobolevState_coeff 0 t.property.1]
  have hfinal : TendstoUniformly (fun n (t : Icc (0 : ℝ) T) =>
      (g (φ n)).sobolevState 0 t.val)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop := by
    simpa only [hident] using hcrit
  refine ⟨u, φ, hφ, hubound, ?_, hfinal⟩
  apply hfinal.continuous
  have hc : ∀ n : ℕ, Continuous (fun t : Icc (0 : ℝ) T =>
      (g (φ n)).sobolevState 0 t.val) := by
    intro n
    exact ((g (φ n)).sobolevState_continuousOn 0).comp_continuous
      continuous_subtype_val (fun t : Icc (0 : ℝ) T => t.property.1)
  exact (Filter.Eventually.of_forall hc).frequently

end

end SingularClosure
