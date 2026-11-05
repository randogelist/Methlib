import ConcreteABCDUnifiedClosure

noncomputable section

open Fefferman Fefferman.ConcreteReal Set MeasureTheory
open scoped BigOperators Topology

namespace CondFeffB

/-- A full period, centered so that the observation point lies in its interior. -/
def centeredCell : Set RSpace :=
  Icc (fun _ => -(1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ))

def sqDifference (u v : RVelocity) (t : ℝ) (x : RSpace) : ℝ :=
  ∑ i : Fin 3, (u x t i - v x t i)^2

def cellEnergy (u v : RVelocity) (t : ℝ) : ℝ :=
  ∫ x in centeredCell, sqDifference u v t x

def JointVelocityContinuous (u : RVelocity) : Prop :=
  ∀ i, ContinuousOn (fun z : RSpace × ℝ => u z.1 z.2 i) {z | 0 ≤ z.2}

theorem jointVelocityContinuous_of_globalSolution
    {ν : PositiveViscosity realAnalysis} {a : RInitial}
    {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s) :
    JointVelocityContinuous s.velocity := by
  have hsm : vectorSmooth realAnalysis s.velocity := hs.2.2.2.2.1.1
  intro i
  exact (show ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => s.velocity z.1 z.2 i)
    {z | 0 ≤ z.2} from hsm i).continuousOn

theorem slice_continuous_of_joint {u : RVelocity} (hu : JointVelocityContinuous u)
    {t : ℝ} (ht : 0 ≤ t) (i : Fin 3) : Continuous (fun x => u x t i) := by
  exact (hu i).comp_continuous (f := fun x : RSpace => (x,t))
    (continuous_id.prodMk continuous_const) (fun _ => ht)

theorem continuousOn_cellEnergy {u v : RVelocity}
    (hu : JointVelocityContinuous u) (hv : JointVelocityContinuous v) :
    ContinuousOn (cellEnergy u v) (Ici 0) := by
  let clamp (z : ℝ × RSpace) : RSpace × ℝ := (z.2, max z.1 0)
  have hcl : Continuous clamp := continuous_snd.prodMk (continuous_fst.max continuous_const)
  have hmap (z : ℝ × RSpace) : clamp z ∈ {p : RSpace × ℝ | 0 ≤ p.2} := by
    change (0 : ℝ) ≤ max z.1 0
    exact le_max_right z.1 0
  have hu' (i : Fin 3) : Continuous (fun z : ℝ × RSpace => u z.2 (max z.1 0) i) :=
    (hu i).comp_continuous (f := clamp) hcl hmap
  have hv' (i : Fin 3) : Continuous (fun z : ℝ × RSpace => v z.2 (max z.1 0) i) :=
    (hv i).comp_continuous (f := clamp) hcl hmap
  have hF : Continuous (Function.uncurry (fun (t : ℝ) (x : RSpace) =>
      sqDifference u v (max t 0) x)) := by
    change Continuous (fun z : ℝ × RSpace => ∑ i : Fin 3,
      (u z.2 (max z.1 0) i - v z.2 (max z.1 0) i)^2)
    exact continuous_finsetSum
      (f := fun (i : Fin 3) (z : ℝ × RSpace) =>
        (u z.2 (max z.1 0) i - v z.2 (max z.1 0) i)^2) Finset.univ
      (fun i _ => ((hu' i).sub (hv' i)).pow 2)
  have hcont : Continuous (fun t : ℝ => cellEnergy u v (max t 0)) :=
    continuous_parametric_integral_of_continuous hF
      (show IsCompact centeredCell from isCompact_Icc)
  apply hcont.continuousOn.congr
  intro t ht
  change cellEnergy u v t = cellEnergy u v (max t 0)
  rw [max_eq_left (show 0 ≤ t from ht)]

theorem cellEnergy_nonneg (u v : RVelocity) (t : ℝ) : 0 ≤ cellEnergy u v t :=
  integral_nonneg (fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem cellEnergy_zero_at_initial {u v : RVelocity}
    (h : ∀ x, u x 0 = v x 0) : cellEnergy u v 0 = 0 := by
  simp [cellEnergy, sqDifference, h]

theorem continuous_sqDifference {u v : RVelocity} {t : ℝ}
    (hu : ∀ i, Continuous (fun x => u x t i))
    (hv : ∀ i, Continuous (fun x => v x t i)) : Continuous (sqDifference u v t) := by
  change Continuous (fun x : RSpace => ∑ i : Fin 3, (u x t i - v x t i)^2)
  exact continuous_finsetSum
    (f := fun (i : Fin 3) (x : RSpace) => (u x t i - v x t i)^2) Finset.univ
    (fun i _ => ((hu i).sub (hv i)).pow 2)

theorem origin_eq_of_cellEnergy_zero {u v : RVelocity} {t : ℝ}
    (hu : ∀ i, Continuous (fun x => u x t i))
    (hv : ∀ i, Continuous (fun x => v x t i))
    (hE : cellEnergy u v t = 0) : u 0 t = v 0 t := by
  have hsq : Continuous (sqDifference u v t) :=
    continuous_sqDifference hu hv
  have hae : sqDifference u v t =ᵐ[volume.restrict centeredCell] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
      (hsq.continuousOn.integrableOn_compact
        (show IsCompact centeredCell from isCompact_Icc))).mp hE
  have hopen := Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset (interior_subset : interior centeredCell ⊆ centeredCell) hae)
    isOpen_interior hsq.continuousOn continuousOn_const
  have h0 : (0 : RSpace) ∈ interior centeredCell := by
    apply mem_interior_iff_mem_nhds.mpr
    exact pi_Icc_mem_nhds (fun _ => by norm_num) (fun _ => by norm_num)
  have hs : (∑ i : Fin 3, (u 0 t i - v 0 t i)^2) = 0 := hopen h0
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hs i
    (Finset.mem_univ i)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)

/-- The one-sided differential inequality is only needed at positive times.
    In particular this argument never differentiates ambient extensions at time zero. -/
theorem cellEnergy_zero_of_differential_ineq {u v : RVelocity} {T K : ℝ}
    (hcont : ContinuousOn (cellEnergy u v) (Icc 0 T))
    (hinitial : cellEnergy u v 0 = 0)
    (hlocal : ∀ t ∈ Ioo 0 T, ∃ d : ℝ,
      HasDerivAt (cellEnergy u v) d t ∧ d ≤ K * cellEnergy u v t) :
    ∀ t ∈ Icc 0 T, cellEnergy u v t = 0 := by
  let E := cellEnergy u v
  let g : ℝ → ℝ := fun t => Real.exp (-K * t) * E t
  have hsm (t : ℝ) (ht : t ∈ interior (Icc 0 T)) :
      ∃ q : ℝ, HasDerivAt g q t ∧ q ≤ 0 := by
    rcases hlocal t (by simpa only [interior_Icc] using ht) with ⟨d, hd, hle⟩
    have hweight : HasDerivAt (fun r : ℝ => Real.exp (-K * r))
        (Real.exp (-K * t) * (-K)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-K)).exp
    refine ⟨_, hweight.mul hd, ?_⟩
    have hdiff : Real.exp (-K * t) * (d - K * E t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr hle)
    convert hdiff using 1 <;> ring
  have hgc : ContinuousOn g (Icc 0 T) := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul hcont
  have hanti : AntitoneOn g (Icc 0 T) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _) hgc
      (fun t ht => ((hsm t ht).choose_spec.1.differentiableAt).differentiableWithinAt)
      (fun t ht => by rw [(hsm t ht).choose_spec.1.deriv]; exact (hsm t ht).choose_spec.2)
  intro t ht
  have hle := hanti (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, ht.1.trans ht.2⟩) ht ht.1
  have hmul : Real.exp (-K * t) * E t ≤ 0 := by
    simpa [g, E, hinitial] using hle
  exact le_antisymm (nonpos_of_mul_nonpos_right hmul (Real.exp_pos _))
    (cellEnergy_nonneg u v t)

theorem origin_eq_of_periodic_energy_ineq {u v : RVelocity} {T K : ℝ}
    (hu : JointVelocityContinuous u) (hv : JointVelocityContinuous v)
    (hini : ∀ x, u x 0 = v x 0)
    (hlocal : ∀ t ∈ Ioo 0 T, ∃ d : ℝ,
      HasDerivAt (cellEnergy u v) d t ∧ d ≤ K * cellEnergy u v t) :
    ∀ t ∈ Icc 0 T, u 0 t = v 0 t := by
  have hzero := cellEnergy_zero_of_differential_ineq
    ((continuousOn_cellEnergy hu hv).mono (fun _ ht => ht.1))
    (cellEnergy_zero_at_initial hini) hlocal
  intro t ht
  exact origin_eq_of_cellEnergy_zero (slice_continuous_of_joint hu ht.1)
    (slice_continuous_of_joint hv ht.1) (hzero t ht)

end CondFeffB
