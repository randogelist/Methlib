import QFA.Assembly.Integrated

/-!
# QUASI_FEFFERMAN_A: conditional formal closure of the frozen physical root

Prepared status: A_TIER_CANDIDATE.
Required promotion evidence: matching external native Windows Lean 4.33.0
compiler pass and exact theorem-level axiom audit.

The existing chain supplies nonemptiness, strong initial trace, strict-cutoff
selection, a global reference, comparison, positive-shift admission, and the
singleton of nonnegative-time restrictions. This module adds only the exact
root interface and the semantic smooth-tail transport edge.

`SmoothNSETail ν u δ` is an explicit semantic parameter. Its intended physical
interpretation is the frozen statement that there exists a pressure such that
`u,p` possess smooth representatives on `[δ,∞) × ℝ³` and solve the unforced
incompressible Navier--Stokes equations with viscosity `ν`. No inhabitant or
analytic realization of that semantic predicate is introduced here.

Consequently the final theorem establishes CONDITIONAL_FORMAL_CLOSURE:
the exact implication from the named analytic, realization, comparison,
admission, continuation, and semantic premises to the frozen QFA root.
It does not establish unconditional closure.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace QFA.PhysicalRoot

open QFA.Representation
open QFA.Endpoints.Restart
open QFA.Assembly.Chain
open QFA.Assembly.Integrated

abbrev NonnegativeTime := {t : ℝ // 0 ≤ t}
abbrev NonnegativeTrajectory := NonnegativeTime → RealSpatialL2

/-- Restriction of an internally real-time-extended trajectory to physical
nonnegative time. -/
def restrictNonnegative (u : Trajectory) : NonnegativeTrajectory :=
  fun t => u t.1

/-- Physical tail beginning at `δ`, represented on nonnegative elapsed time. -/
def tailRestriction (δ : ℝ) (u : Trajectory) : NonnegativeTrajectory :=
  fun t => timeTranslate δ u t.1

/-- The physical nonnegative-time trajectory class induced by the internal
real-time extension class. -/
def restrictedAdmissible
    (Admissible : RealSpatialL2 → Set Trajectory)
    (b : RealSpatialL2) : Set NonnegativeTrajectory :=
  restrictNonnegative '' Admissible b

/-- Exact frozen QFA conclusion relative to supplied physical semantics.

`SmoothNSETail ν u δ` is to be instantiated by the exact smooth
velocity-pressure NSE-tail predicate. `restrictedAdmissible` removes only the
auxiliary negative-time extensions used by the internal comparison assembly.
-/
def QFARoot
    (ν : ℝ)
    (Domain : Set RealSpatialL2)
    (Admissible : RealSpatialL2 → Set Trajectory)
    (SmoothNSETail : ℝ → Trajectory → ℝ → Prop) : Prop :=
  ∀ a ∈ Domain,
    (Admissible a).Nonempty ∧
    ∀ u ∈ Admissible a,
      Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a) ∧
      ∀ δ : ℝ, ‖a‖ ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ →
        SmoothNSETail ν u δ ∧
        restrictedAdmissible Admissible (u δ) =
          {tailRestriction δ u}

/-- Named semantic edge from the supplied global reference to physical
positive-time regularity, together with transport across the proved tail
identity. Neither field states the QFA cutoff or root conclusion. -/
structure SmoothReferencePorts
    (ν : ℝ)
    (Reference : RealSpatialL2 → Trajectory → Prop)
    (SmoothNSETail : ℝ → Trajectory → ℝ → Prop) : Prop where
  positive_time :
    ∀ {b : RealSpatialL2} {v : Trajectory},
      Reference b v → ∀ r : ℝ, 0 < r → SmoothNSETail ν v r
  transport :
    ∀ {u v : Trajectory} {s r : ℝ},
      (∀ t : ℝ, s ≤ t → u t = v (t - s)) →
      SmoothNSETail ν v r →
      SmoothNSETail ν u (s + r)

/-- LE109. The selected-tail object already contains the exact singleton
statement for the physical nonnegative-time class. -/
theorem selectedTail_restricted_singleton
    {ν δ : ℝ}
    {Admissible : RealSpatialL2 → Set Trajectory}
    {Reference : RealSpatialL2 → Trajectory → Prop}
    {u : Trajectory} {G : GradientTrajectory} {Good : ℝ → Prop}
    (h : SelectedTail ν δ Admissible Reference u G Good) :
    restrictedAdmissible Admissible (u δ) =
      {tailRestriction δ u} := by
  obtain ⟨s, v, hs0, hsδ, hgood, hsmall, hstart, hrestart,
    href, htail, hrefδ, hadmitδ, hrestricted, hsingleton⟩ := h
  simpa only [restrictedAdmissible, restrictNonnegative, tailRestriction]
    using hsingleton

/-- LE110. Positive-time smoothness of the global reference transfers to the
original selected trajectory at every later cutoff. -/
theorem selectedTail_smooth
    {ν δ : ℝ}
    {Admissible : RealSpatialL2 → Set Trajectory}
    {Reference : RealSpatialL2 → Trajectory → Prop}
    {SmoothNSETail : ℝ → Trajectory → ℝ → Prop}
    {u : Trajectory} {G : GradientTrajectory} {Good : ℝ → Prop}
    (h : SelectedTail ν δ Admissible Reference u G Good)
    (hSmooth : SmoothReferencePorts ν Reference SmoothNSETail) :
    SmoothNSETail ν u δ := by
  obtain ⟨s, v, hs0, hsδ, hgood, hsmall, hstart, hrestart,
    href, htail, hrefδ, hadmitδ, hrestricted, hsingleton⟩ := h
  have hv : SmoothNSETail ν v (δ - s) :=
    hSmooth.positive_time href (δ - s) (sub_pos.mpr hsδ)
  have hu : SmoothNSETail ν u (s + (δ - s)) :=
    hSmooth.transport htail hv
  have hsum : s + (δ - s) = δ := by ring
  simpa only [hsum] using hu

/-- LE111. Exact post-cutoff physical conclusion extracted from a selected
tail and the named smooth-reference semantics. -/
theorem selectedTail_root_conclusion
    {ν δ : ℝ}
    {Admissible : RealSpatialL2 → Set Trajectory}
    {Reference : RealSpatialL2 → Trajectory → Prop}
    {SmoothNSETail : ℝ → Trajectory → ℝ → Prop}
    {u : Trajectory} {G : GradientTrajectory} {Good : ℝ → Prop}
    (h : SelectedTail ν δ Admissible Reference u G Good)
    (hSmooth : SmoothReferencePorts ν Reference SmoothNSETail) :
    SmoothNSETail ν u δ ∧
      restrictedAdmissible Admissible (u δ) =
        {tailRestriction δ u} :=
  ⟨selectedTail_smooth h hSmooth, selectedTail_restricted_singleton h⟩

/-- LE112. Conditional formal closure of the exact frozen QFA root.

Unresolved premises are named and visible:
* `ClassRealization`: physical Leray--Hopf existence, representatives,
  energy profile, good restart times, and translated admission;
* `ReferencePorts`: relative-energy comparison and positive-shift admission;
* `CompactToSchwartzEndpoint`, `WholeSpaceSpectralEndpoint`,
  `WholeSpaceAgmonEndpoint`: analytic realization;
* `ReferenceConstructionFromAbsorption`: local strong evolution, physical
  identities, temporal invariant, and global continuation;
* `SmoothReferencePorts`: pressure/smooth-NSE semantics and tail transport.

No uniqueness from the original datum is assumed or concluded.
-/
theorem QUASI_FEFFERMAN_A
    {ν : ℝ}
    {Domain : Set RealSpatialL2}
    {Admissible : RealSpatialL2 → Set Trajectory}
    {Reference : RealSpatialL2 → Trajectory → Prop}
    {Good : Trajectory → GradientTrajectory → ℝ → Prop}
    {SmoothNSETail : ℝ → Trajectory → ℝ → Prop}
    (hν : 0 < ν)
    (hClass : ClassRealization ν Domain Admissible Good)
    (hPorts : ReferencePorts Admissible Reference)
    (hExtension : QFA.Assembly.Representation.CompactToSchwartzEndpoint)
    (hSpectral : QFA.Endpoints.Agmon.WholeSpaceSpectralEndpoint)
    (hAgmon : QFA.Endpoints.Agmon.WholeSpaceAgmonEndpoint)
    (hReferenceBackend :
      ReferenceConstructionFromAbsorption ν Domain Admissible Reference Good)
    (hSmooth : SmoothReferencePorts ν Reference SmoothNSETail) :
    QFARoot ν Domain Admissible SmoothNSETail := by
  intro a ha
  obtain ⟨hNonempty, hAll⟩ :=
    quantified_tail_assembly_of_analytic_inputs
      hν hClass hPorts hExtension hSpectral hAgmon hReferenceBackend a ha
  refine ⟨hNonempty, ?_⟩
  intro u hu
  obtain ⟨hInitial, hTrace, hTails⟩ := hAll u hu
  refine ⟨hTrace, ?_⟩
  intro δ hcut
  obtain ⟨G, hProfile, hSelected⟩ := hTails δ hcut
  exact selectedTail_root_conclusion hSelected hSmooth

end QFA.PhysicalRoot
