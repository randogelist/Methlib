import SingularClosure.GalerkinAlgebra

/-!
# Local existence and forward uniqueness for the actual Fourier ODE

The local existence theorem below is instantiated with the concrete polynomial
`finiteGalerkinRhs`.  The uniqueness theorem concerns all nonnegative times,
which is the domain specified by `GalerkinSolution`; no equality is asserted
for the unconstrained values of a trajectory at negative times.

Global existence for arbitrary smooth initial data remains a separate part of
frozen endpoint 3.  In particular, local existence is not recorded as global
existence, and the real/solenoidal invariant-space construction is not assumed.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff BigOperators

namespace SingularClosure

noncomputable section

/-- The actual finite-dimensional polynomial ODE has a local solution from
every finite coefficient state and every reference time. -/
theorem finiteGalerkinRhs_local_exists (ν : ℝ) (N : ℕ)
    (z₀ : FiniteGalerkinState N) (t₀ : ℝ) :
    ∃ z : ℝ → FiniteGalerkinState N, z t₀ = z₀ ∧
      ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt z (finiteGalerkinRhs ν N (z t)) t := by
  have hC1 : ContDiff ℝ 1 (finiteGalerkinRhs ν N) :=
    (contDiff_finiteGalerkinRhs ν N).of_le (by norm_num)
  exact hC1.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

/-- On each bounded finite-state ball there is one local existence time valid
for every starting state and every starting time.  The radius need not be
small, and the time is independent of the starting point within this ball. -/
theorem finiteGalerkinRhs_uniform_local_time (ν : ℝ) (N : ℕ) (R : ℝ) :
    ∃ δ > (0 : ℝ),
      ∀ z₀ ∈ closedBall (0 : FiniteGalerkinState N) R, ∀ t₀ : ℝ,
        ∃ z : ℝ → FiniteGalerkinState N, z t₀ = z₀ ∧
          ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
            HasDerivAt z (finiteGalerkinRhs ν N (z t)) t := by
  classical
  have hC1 : ContDiff ℝ 1 (finiteGalerkinRhs ν N) :=
    (contDiff_finiteGalerkinRhs ν N).of_le (by norm_num)
  have hloc : ∀ y : FiniteGalerkinState N,
      ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
        ∀ x ∈ closedBall y r, ∃ z : ℝ → FiniteGalerkinState N,
          z 0 = x ∧ ∀ t ∈ Ioo (0 - ε) (0 + ε),
            HasDerivAt z (finiteGalerkinRhs ν N (z t)) t :=
    fun y => hC1.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  choose r hr ε hε hsol using hloc
  have hcover : closedBall (0 : FiniteGalerkinState N) R ⊆ ⋃ y, ball y (r y) := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_ball_self (hr x)⟩
  obtain ⟨I, hI⟩ := (isCompact_closedBall (0 : FiniteGalerkinState N) R).elim_finite_subcover
    (fun y => ball y (r y)) (fun _ => isOpen_ball) hcover
  rcases I.eq_empty_or_nonempty with hIemp | hIne
  · refine ⟨1, one_pos, fun z₀ hz₀ t₀ => ?_⟩
    rw [hIemp] at hI
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, subset_empty_iff] at hI
    exact absurd (hI ▸ hz₀) (Set.notMem_empty z₀)
  · refine ⟨I.inf' hIne ε, ?_, fun z₀ hz₀ t₀ => ?_⟩
    · rw [Finset.lt_inf'_iff]
      exact fun y _ => hε y
    · have hz₀' : z₀ ∈ ⋃ y ∈ I, ball y (r y) := hI hz₀
      rw [mem_iUnion₂] at hz₀'
      obtain ⟨y, hyI, hzy⟩ := hz₀'
      obtain ⟨z, hz0, hzs⟩ := hsol y z₀ (ball_subset_closedBall hzy)
      refine ⟨fun t => z (t - t₀), by simpa using hz0, fun t ht => ?_⟩
      have hδε : I.inf' hIne ε ≤ ε y := Finset.inf'_le _ hyI
      have htmem : t - t₀ ∈ Ioo (0 - ε y) (0 + ε y) := by
        constructor <;> linarith [ht.1, ht.2]
      have hd := hzs (t - t₀) htmem
      have hsub : HasDerivAt (fun t : ℝ => t - t₀) 1 t :=
        (hasDerivAt_id t).sub_const t₀
      simpa only [one_smul, Function.comp_def] using hd.scomp t hsub

/-- The finite-state restriction of a Galerkin trajectory is continuous on
its physical time domain. -/
theorem GalerkinSolution.finite_continuousOn {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) :
    ContinuousOn (fun t => restrictFiniteState N (g.coeff t)) (Ici 0) := by
  apply continuousOn_pi.2
  intro k
  apply continuousOn_pi.2
  intro i
  exact g.coefficient_continuous k.val i

/-- The componentwise derivative contract gives the derivative in the actual
finite-dimensional state space. -/
theorem GalerkinSolution.finite_hasDerivWithinAt
    {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => restrictFiniteState N (g.coeff s))
      (finiteGalerkinRhs ν N (restrictFiniteState N (g.coeff t))) (Ici 0) t := by
  apply hasDerivWithinAt_pi.2
  intro k
  apply hasDerivWithinAt_pi.2
  intro i
  exact g.finite_equation t ht k i

/-- Uniqueness on an arbitrary finite forward interval for the concrete ODE.
The bounding ball and its Lipschitz constant are derived from continuity and
smoothness; neither is an additional analytic assumption. -/
theorem finiteGalerkinRhs_unique_on_Icc (ν : ℝ) (N : ℕ)
    (f g : ℝ → FiniteGalerkinState N) (T : ℝ)
    (hf : ContinuousOn f (Ici 0)) (hg : ContinuousOn g (Ici 0))
    (hf' : ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt f (finiteGalerkinRhs ν N (f t)) (Ici 0) t)
    (hg' : ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt g (finiteGalerkinRhs ν N (g t)) (Ici 0) t)
    (h0 : f 0 = g 0) : EqOn f g (Icc 0 T) := by
  have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
  have hfc : ContinuousOn f (Icc 0 T) := hf.mono hsub
  have hgc : ContinuousOn g (Icc 0 T) := hg.mono hsub
  obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  let M : ℝ := max Mf Mg
  have hfM : ∀ t ∈ Icc (0 : ℝ) T,
      f t ∈ closedBall (0 : FiniteGalerkinState N) M := by
    intro t ht
    rw [mem_closedBall, dist_zero_right]
    exact (hMf t ht).trans (le_max_left Mf Mg)
  have hgM : ∀ t ∈ Icc (0 : ℝ) T,
      g t ∈ closedBall (0 : FiniteGalerkinState N) M := by
    intro t ht
    rw [mem_closedBall, dist_zero_right]
    exact (hMg t ht).trans (le_max_right Mf Mg)
  have hC1 : ContDiff ℝ 1 (finiteGalerkinRhs ν N) :=
    (contDiff_finiteGalerkinRhs ν N).of_le (by norm_num)
  obtain ⟨K, hK⟩ :=
    (hC1.contDiffOn (s := closedBall (0 : FiniteGalerkinState N) M)).exists_lipschitzOnWith
      one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  apply ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => finiteGalerkinRhs ν N)
    (s := fun _ => closedBall (0 : FiniteGalerkinState N) M) (K := K)
    (fun _ _ => hK) hfc
    (fun t ht => (hf' t ht.1).mono (fun _ hs => ht.1.trans hs))
    (fun t ht => hfM t ⟨ht.1, ht.2.le⟩) hgc
    (fun t ht => (hg' t ht.1).mono (fun _ hs => ht.1.trans hs))
    (fun t ht => hgM t ⟨ht.1, ht.2.le⟩) h0

/-- The coefficient family of a Galerkin trajectory is unique on all forward
times.  This result requires no smallness, viscosity sign, or square budget. -/
theorem GalerkinSolution.coeff_unique_forward {ν : ℝ} {a : Field} {N : ℕ}
    (g h : GalerkinSolution ν a N) : EqOn g.coeff h.coeff (Ici 0) := by
  intro t ht
  have hinit : restrictFiniteState N (g.coeff 0) =
      restrictFiniteState N (h.coeff 0) := by
    funext k i
    change g.coeff 0 k.val i = h.coeff 0 k.val i
    rw [g.initial, h.initial]
  have heq := finiteGalerkinRhs_unique_on_Icc ν N
    (fun s => restrictFiniteState N (g.coeff s))
    (fun s => restrictFiniteState N (h.coeff s)) t
    g.finite_continuousOn h.finite_continuousOn
    (fun _ hs => g.finite_hasDerivWithinAt hs)
    (fun _ hs => h.finite_hasDerivWithinAt hs) hinit
    ⟨ht, le_rfl⟩
  have hex := congrArg (extendFiniteState N) heq
  simpa only [g.extend_restrict_coeff t ht, h.extend_restrict_coeff t ht] using hex

/-- The actual synthesized physical Galerkin velocity is unique for t ≥ 0. -/
theorem GalerkinSolution.velocity_unique_forward {ν : ℝ} {a : Field} {N : ℕ}
    (g h : GalerkinSolution ν a N) : EqOn g.velocity h.velocity (Ici 0) := by
  intro t ht
  exact congrArg (finiteSynthesis N) (g.coeff_unique_forward h ht)

end

end SingularClosure
