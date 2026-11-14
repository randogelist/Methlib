import QFACorrectedRoot.Analytic

/-!
# Corrected conditional formal closure of QUASI_FEFFERMAN_A

The exact frozen root conclusion is unchanged. The obsolete radial-bump
compact-to-Schwartz premise is absent. Compact-Schwartz density and the
continuous-linear extension to tempered distributions are imported as proved
A-tier results.

Unresolved premises remain explicit: physical class realization, spectral and
Agmon endpoints, construction/continuation of the strong reference from the
corrected absorption statement, relative-energy comparison/admission, and the
smooth pressure/NSE semantic edge.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace QFA.CorrectedPhysicalRoot

open QFA.Representation
open QFA.Endpoints.Restart
open QFA.Assembly.Chain

abbrev NonnegativeTime := {t : ℝ // 0 ≤ t}
abbrev NonnegativeTrajectory := NonnegativeTime → RealSpatialL2

/-- Restriction to physical nonnegative time. -/
def restrictNonnegative (u : Trajectory) : NonnegativeTrajectory :=
  fun t => u t.1

/-- Physical tail beginning at `δ`. -/
def tailRestriction (δ : ℝ) (u : Trajectory) : NonnegativeTrajectory :=
  fun t => timeTranslate δ u t.1

/-- Physical nonnegative-time class induced by the internal real-time class. -/
def restrictedAdmissible
    (Admissible : RealSpatialL2 → Set Trajectory)
    (b : RealSpatialL2) : Set NonnegativeTrajectory :=
  restrictNonnegative '' Admissible b

/-- Exact frozen QFA conclusion relative to the supplied smooth-NSE semantics. -/
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

/-- Smooth reference semantics and transport across the proved tail identity. -/
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

/-- The selected-tail object contains the exact physical restricted singleton. -/
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

/-- Positive-time smoothness of the global reference transfers to the selected
trajectory at every later cutoff. -/
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

/-- Exact post-cutoff physical conclusion. -/
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

/-- Corrected conditional formal closure of the exact frozen QFA root.

The old `CompactToSchwartzEndpoint` is absent. The exact remaining premises
are visible in the theorem type. No uniqueness from the original datum is
assumed or concluded.
-/
theorem QUASI_FEFFERMAN_A_CORRECTED
    {ν : ℝ}
    {Domain : Set RealSpatialL2}
    {Admissible : RealSpatialL2 → Set Trajectory}
    {Reference : RealSpatialL2 → Trajectory → Prop}
    {Good : Trajectory → GradientTrajectory → ℝ → Prop}
    {SmoothNSETail : ℝ → Trajectory → ℝ → Prop}
    (hν : 0 < ν)
    (hClass : ClassRealization ν Domain Admissible Good)
    (hPorts : ReferencePorts Admissible Reference)
    (hSpectral : QFA.Endpoints.Agmon.WholeSpaceSpectralEndpoint)
    (hAgmon : QFA.Endpoints.Agmon.WholeSpaceAgmonEndpoint)
    (hReferenceBackend :
      CorrectedReferenceConstructionFromAbsorption
        ν Domain Admissible Reference Good)
    (hSmooth : SmoothReferencePorts ν Reference SmoothNSETail) :
    QFARoot ν Domain Admissible SmoothNSETail := by
  intro a ha
  obtain ⟨hNonempty, hAll⟩ :=
    quantified_tail_assembly_of_corrected_analytic_inputs
      hν hClass hPorts hSpectral hAgmon hReferenceBackend a ha
  refine ⟨hNonempty, ?_⟩
  intro u hu
  obtain ⟨hInitial, hTrace, hTails⟩ := hAll u hu
  refine ⟨hTrace, ?_⟩
  intro δ hcut
  obtain ⟨G, hProfile, hSelected⟩ := hTails δ hcut
  exact selectedTail_root_conclusion hSelected hSmooth

end QFA.CorrectedPhysicalRoot
