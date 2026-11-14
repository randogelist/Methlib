import QFA.Assembly.TailComparison

/-!
# QFA: selection, reference comparison and the complete restricted-tail chain

Status: A_TIER_CANDIDATE. External cached native Windows Lean 4.33.0 and
exact theorem-level axiom audits are required. No local Lean/Lake execution.

The spatial carrier is the existing full-volume L2(R3;R3). `Admissible`,
`Reference`, `Domain` and `Good` are explicit parameters: no definition here
identifies them with physical Leray--Hopf or strong NSE solution classes.
The construction port returns a reference witness, never the target tail
equality, cutoff conclusion, or singleton. The comparison port supplies
primitive finite-horizon relative-energy data, never equality itself.

The exact cutoff and every selected restart premise are retained. A second,
strictly positive reference shift supplies actual membership at u(delta).
Only restrictions to nonnegative time are identified. No membership of a
different negative-time extension is inferred from restricted equality.

This is a proved implication between explicit interfaces after external
verification. The physical QFA root, pressure and smoothness remain separate
realization obligations. The pointwise H2 AnalyticChain is not applied to the
selected H1 time: its connection to local strong evolution and continuation
remains an explicit analytic task.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology

namespace QFA.Assembly.Chain

open QFA.Representation
open QFA.Endpoints.Restart
open QFA.Assembly.Restart
open QFA.Assembly.TailComparison

abbrev Trajectory := ℝ → RealSpatialL2
abbrev GradientTrajectory := ℝ → Fin 3 → RealSpatialL2

/-- Explicit comparison and positive-shift admission interfaces. Neither
field asserts the desired trajectory equality or a singleton conclusion. -/
structure ReferencePorts
    (Admissible : RealSpatialL2 → Set Trajectory)
    (Reference : RealSpatialL2 → Trajectory → Prop) : Prop where
  comparison : ∀ {b : RealSpatialL2} {w v : Trajectory},
    w ∈ Admissible b → Reference b v → ComparableOnNonnegative w v b
  positive_shift : ∀ {b : RealSpatialL2} {v : Trajectory},
    Reference b v → ∀ r : ℝ, 0 < r →
      Reference (v r) (timeTranslate r v) ∧
        timeTranslate r v ∈ Admissible (v r)

/-- The complete exact output of the selected-reference composition.
All reference/admission conclusions concern the supplied predicates.
The physical strong-solution interpretation is not built into this definition. -/
def SelectedTail
    (ν δ : ℝ)
    (Admissible : RealSpatialL2 → Set Trajectory)
    (Reference : RealSpatialL2 → Trajectory → Prop)
    (u : Trajectory) (G : GradientTrajectory) (Good : ℝ → Prop) : Prop :=
  ∃ (s : ℝ) (v : Trajectory),
    0 < s ∧ s < δ ∧ Good s ∧
    velocityEnergy (u s) * gradientEnergy (G s) < 4 * Real.pi ^ 2 * ν ^ 4 ∧
    EnergyStart ν u G s ∧ RestartData ν u G s ∧
    Reference (u s) v ∧
    (∀ t : ℝ, s ≤ t → u t = v (t - s)) ∧
    Reference (u δ) (timeTranslate (δ - s) v) ∧
    timeTranslate (δ - s) v ∈ Admissible (u δ) ∧
    (fun t : {t : ℝ // 0 ≤ t} => timeTranslate δ u t.1) =
      (fun t : {t : ℝ // 0 ≤ t} => timeTranslate (δ - s) v t.1) ∧
    (fun w : Trajectory => fun t : {t : ℝ // 0 ≤ t} => w t.1) '' Admissible (u δ) =
      {fun t : {t : ℝ // 0 ≤ t} => timeTranslate δ u t.1}

/-- Energy selection followed by two genuine comparison applications.
The first identifies the original trajectory after the selected restart.
The second compares every newly admitted trajectory at delta with the
positive shift of the reference. All physical construction ports are explicit. -/
theorem exists_selected_reference_and_tail_singleton
    {ν δ : ℝ} {a : RealSpatialL2}
    {u : Trajectory} {G : GradientTrajectory} {Good : ℝ → Prop}
    {Admissible : RealSpatialL2 → Set Trajectory}
    {Reference : RealSpatialL2 → Trajectory → Prop}
    (hProfile : EnergyProfile ν a u G) (hν : 0 < ν)
    (hcut : ‖a‖ ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ)
    (hweak : ∀ b : RealSpatialL2,
      ContinuousOn (fun t => inner ℝ (u t) b) (Ici (0 : ℝ)))
    (hgood : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) δ),
      Good s ∧ EnergyStart ν u G s)
    (hRestart : ∀ s : ℝ, 0 < s → Good s → EnergyStart ν u G s →
      timeTranslate s u ∈ Admissible (u s))
    (hReference : ∀ s : ℝ, 0 < s → Good s →
      velocityEnergy (u s) * gradientEnergy (G s) < 4 * Real.pi ^ 2 * ν ^ 4 →
      EnergyStart ν u G s → RestartData ν u G s →
        ∃ v : Trajectory, Reference (u s) v)
    (hPorts : ReferencePorts Admissible Reference) :
    SelectedTail ν δ Admissible Reference u G Good := by
  obtain ⟨s, hs0, hsδ, hgs, hsmall, hstart, hdata⟩ :=
    exists_restartData_before hProfile hν hcut hweak hgood
  obtain ⟨v, hv⟩ := hReference s hs0 hgs hsmall hstart hdata
  have hsource : ComparableOnNonnegative (timeTranslate s u) v (u s) :=
    hPorts.comparison (hRestart s hs0 hgs hstart) hv
  have hdatum : v (δ - s) = u δ := (hsource.eq_on_tail δ hsδ.le).symm
  have hshift := hPorts.positive_shift hv (δ - s) (sub_pos.mpr hsδ)
  have hshift_reference : Reference (u δ) (timeTranslate (δ - s) v) := by
    simpa only [hdatum] using hshift.1
  have hshift_admission : timeTranslate (δ - s) v ∈ Admissible (u δ) := by
    simpa only [hdatum] using hshift.2
  have hcomparisons : ∀ w ∈ Admissible (u δ),
      ComparableOnNonnegative w (timeTranslate (δ - s) v) (u δ) := by
    intro w hw
    exact hPorts.comparison hw hshift_reference
  exact ⟨s, v, hs0, hsδ, hgs, hsmall, hstart, hdata, hv,
    hsource.eq_on_tail, hshift_reference, hshift_admission,
    hsource.further_timeTranslate_eq hsδ.le,
    restricted_restart_class_eq_singleton hsδ hsource hshift_admission hcomparisons⟩

/-- Realization inputs for a datum-indexed trajectory class. The profile and
valid energy-start set are actual mathematical data; physical weak derivative,
divergence, momentum and LH interpretations remain to be constructed.
The initial value and the strong right trace remain separate fields. -/
structure ClassRealization
    (ν : ℝ) (Domain : Set RealSpatialL2)
    (Admissible : RealSpatialL2 → Set Trajectory)
    (Good : Trajectory → GradientTrajectory → ℝ → Prop) : Prop where
  nonempty : ∀ a ∈ Domain, (Admissible a).Nonempty
  initial_value : ∀ a ∈ Domain, ∀ u ∈ Admissible a, u 0 = a
  initial_trace : ∀ a ∈ Domain, ∀ u ∈ Admissible a,
    Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a)
  profile : ∀ a ∈ Domain, ∀ u ∈ Admissible a,
    ∃ G : GradientTrajectory,
      EnergyProfile ν a u G ∧
      (∀ b : RealSpatialL2,
        ContinuousOn (fun t => inner ℝ (u t) b) (Ici (0 : ℝ))) ∧
      ∀ R : ℝ, 0 < R →
        ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) R),
          Good u G s ∧ EnergyStart ν u G s
  restart_admission : ∀ a ∈ Domain, ∀ u ∈ Admissible a,
    ∀ (G : GradientTrajectory) (s : ℝ),
      0 < s → Good u G s → EnergyStart ν u G s →
        timeTranslate s u ∈ Admissible (u s)

/-- Explicit unresolved subcritical reference construction. Its conclusion
contains no cutoff, comparison equality, tail-singleton, or QFA root assertion.
It must later be inhabited by actual strong-solution and continuation theory. -/
def SubcriticalReferenceConstruction
    (ν : ℝ) (Domain : Set RealSpatialL2)
    (Admissible : RealSpatialL2 → Set Trajectory)
    (Reference : RealSpatialL2 → Trajectory → Prop)
    (Good : Trajectory → GradientTrajectory → ℝ → Prop) : Prop :=
  ∀ a ∈ Domain, ∀ u ∈ Admissible a, ∀ (G : GradientTrajectory) (s : ℝ),
    0 < s → Good u G s →
    velocityEnergy (u s) * gradientEnergy (G s) < 4 * Real.pi ^ 2 * ν ^ 4 →
    EnergyStart ν u G s → RestartData ν u G s →
      ∃ v : Trajectory, Reference (u s) v

/-- Quantified exact class/reference composition. Nonemptiness and initial
trace are provided by ClassRealization; the cutoff, selected restart, tail
comparison and restricted singleton are assembled by the preceding theorem.

No uniqueness from the original datum is required or concluded. No smooth
representative or pressure is asserted for the uninterpreted Reference. -/
theorem quantified_tail_assembly
    {ν : ℝ} {Domain : Set RealSpatialL2}
    {Admissible : RealSpatialL2 → Set Trajectory}
    {Reference : RealSpatialL2 → Trajectory → Prop}
    {Good : Trajectory → GradientTrajectory → ℝ → Prop}
    (hν : 0 < ν)
    (hClass : ClassRealization ν Domain Admissible Good)
    (hReference : SubcriticalReferenceConstruction ν Domain Admissible Reference Good)
    (hPorts : ReferencePorts Admissible Reference) :
    ∀ a ∈ Domain,
      (Admissible a).Nonempty ∧
      ∀ u ∈ Admissible a,
        u 0 = a ∧ Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a) ∧
        ∀ δ : ℝ, ‖a‖ ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ →
          ∃ G : GradientTrajectory,
            EnergyProfile ν a u G ∧
              SelectedTail ν δ Admissible Reference u G (Good u G) := by
  intro a ha
  refine ⟨hClass.nonempty a ha, ?_⟩
  intro u hu
  refine ⟨hClass.initial_value a ha u hu, hClass.initial_trace a ha u hu, ?_⟩
  intro δ hcut
  obtain ⟨G, hProfile, hweak, hgood⟩ := hClass.profile a ha u hu
  have hcut_nonnegative : 0 ≤ ‖a‖ ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) := by positivity
  have hδ : 0 < δ := hcut_nonnegative.trans_lt hcut
  refine ⟨G, hProfile, ?_⟩
  exact exists_selected_reference_and_tail_singleton hProfile hν hcut hweak
    (hgood δ hδ)
    (fun s hs hgs hstart => hClass.restart_admission a ha u hu G s hs hgs hstart)
    (fun s hs hgs hsmall hstart hdata =>
      hReference a ha u hu G s hs hgs hsmall hstart hdata)
    hPorts

end QFA.Assembly.Chain
