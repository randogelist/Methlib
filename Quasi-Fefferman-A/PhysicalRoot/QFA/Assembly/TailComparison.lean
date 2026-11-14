import QFA.Assembly.Comparison
import QFA.Assembly.Restart

/-!
# QFA: finite comparison data to restricted tail singleton

Status: A_TIER_CANDIDATE. Matching external compilation and exact
declaration-level axiom auditing remain pending for this new module.
Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d; Lean 4.33.0.
No local Lean or Lake execution.

The scalar comparison inputs remain explicit. The coefficient and good-start
predicate may depend on the trajectory pair and the finite observation horizon.
No admissible-time sequence or numerical coefficient budget is supplied by
the caller: the existing comparison assembly constructs those ingredients.

The final result identifies only nonnegative-time restrictions of an arbitrary
datum-indexed class. It requires actual membership of the shifted reference
and comparison data for every member at the new initial time. Equality on
nonnegative time does not imply membership of a different total-real extension.

The concrete RestartData constructor consumes its already derived strong
trace. It supplies neither physical cross-testing nor coefficient/product
integrability. No physical NSE, LH existence, smoothness, pressure, or frozen
QUASI_FEFFERMAN_A conclusion is declared by this module.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Interval Topology

namespace QFA.Assembly.TailComparison

open QFA.Endpoints.Restart

variable {V : Type*} [NormedAddCommGroup V]

/-- Exact finite-horizon premises of comparison. Strong right traces and
the two values at zero are separate fields. No field is an equality-of-
trajectories conclusion or an inhabitant of a physical solution class. -/
structure ComparisonData
    (u v : ℝ → V) (a₀ : V) (T : ℝ)
    (g : ℝ → ℝ) (Good : ℝ → Prop) : Prop where
  coefficient_continuous : ContinuousOn g (Ioc (0 : ℝ) T)
  coefficient_nonnegative : ∀ t ∈ Ioc (0 : ℝ) T, 0 ≤ g t
  coefficient_integrable : IntervalIntegrable g volume (0 : ℝ) T
  relative_energy_integrable :
    IntervalIntegrable (fun r => g r * ‖u r - v r‖ ^ 2) volume (0 : ℝ) T
  good_ae : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) T), Good r
  left_trace : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a₀)
  right_trace : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 a₀)
  left_initial : u 0 = a₀
  right_initial : v 0 = a₀
  relative_energy : ∀ r ∈ Ioo (0 : ℝ) T, Good r →
    ∀ t ∈ Icc r T,
      ‖u t - v t‖ ^ 2 ≤ ‖u r - v r‖ ^ 2 +
        ∫ q in r..t, g q * ‖u q - v q‖ ^ 2

/-- Finite comparison data for every positive horizon. The witnesses `g`
and `Good` may vary with that horizon. This definition assumes the actual
comparison premises; it contains no trajectory-equality field. -/
def ComparableOnNonnegative (u v : ℝ → V) (a₀ : V) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ g : ℝ → ℝ, ∃ Good : ℝ → Prop,
    ComparisonData u v a₀ T g Good

/-- The existing closed-horizon endpoint consumes every field of the exact
finite comparison data, including its all-upper-endpoint relative energy. -/
theorem ComparisonData.eq_on_Icc
    {u v : ℝ → V} {a₀ : V} {T : ℝ} {g : ℝ → ℝ} {Good : ℝ → Prop}
    (h : ComparisonData u v a₀ T g Good) (hT : 0 < T) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = v t := by
  exact QFA.Assembly.Comparison.eq_on_Icc_of_ae_relative_energy
    hT h.coefficient_continuous h.coefficient_nonnegative
    h.coefficient_integrable h.relative_energy_integrable h.good_ae
    h.left_trace h.right_trace h.left_initial h.right_initial h.relative_energy

/-- Finite-horizon comparison gives equality at every nonnegative time.
No global coefficient or integrability over the infinite interval is required. -/
theorem ComparableOnNonnegative.eq_on_nonnegative
    {u v : ℝ → V} {a₀ : V}
    (h : ComparableOnNonnegative u v a₀) :
    ∀ t : ℝ, 0 ≤ t → u t = v t := by
  intro t ht
  have hT : 0 < t + 1 := by linarith
  obtain ⟨g, Good, hdata⟩ := h (t + 1) hT
  exact hdata.eq_on_Icc hT t ⟨ht, by linarith⟩

/-- Every class member is compared with the supplied member `v` by actual
finite comparison data. Reference membership supplies the reverse singleton
inclusion and nonemptiness. Equality of total-real extensions is not claimed. -/
theorem restricted_class_eq_singleton_of_comparable
    {C : Set (ℝ → V)} {v : ℝ → V} {a₀ : V}
    (hv : v ∈ C)
    (hcomparisons : ∀ w ∈ C, ComparableOnNonnegative w v a₀) :
    (fun w : ℝ → V => fun t : {t : ℝ // 0 ≤ t} => w t.1) '' C =
      {fun t : {t : ℝ // 0 ≤ t} => v t.1} := by
  apply QFA.Assembly.Comparison.restricted_class_eq_singleton_of_eq_on_nonnegative hv
  intro w hw
  exact (hcomparisons w hw).eq_on_nonnegative

/-- The concrete restart assembly supplies the left strong trace and the
translated initial value. Reference trace/value, finite integrability,
good starts and the actual relative-energy inequality remain inputs. -/
theorem comparisonData_of_restartData
    {ν s T : ℝ}
    {u v : ℝ → QFA.Representation.RealSpatialL2}
    {G : ℝ → Fin 3 → QFA.Representation.RealSpatialL2}
    {g : ℝ → ℝ} {Good : ℝ → Prop}
    (hrestart : QFA.Assembly.Restart.RestartData ν u G s)
    (hg : ContinuousOn g (Ioc (0 : ℝ) T))
    (hg_nonnegative : ∀ t ∈ Ioc (0 : ℝ) T, 0 ≤ g t)
    (hg_integrable : IntervalIntegrable g volume (0 : ℝ) T)
    (hprod : IntervalIntegrable
      (fun r => g r * ‖timeTranslate s u r - v r‖ ^ 2) volume (0 : ℝ) T)
    (hgood : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) T), Good r)
    (hv_trace : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 (u s)))
    (hv_initial : v 0 = u s)
    (hrelative : ∀ r ∈ Ioo (0 : ℝ) T, Good r →
      ∀ t ∈ Icc r T,
        ‖timeTranslate s u t - v t‖ ^ 2 ≤ ‖timeTranslate s u r - v r‖ ^ 2 +
          ∫ q in r..t, g q * ‖timeTranslate s u q - v q‖ ^ 2) :
    ComparisonData (timeTranslate s u) v (u s) T g Good := by
  refine
    { coefficient_continuous := hg
      coefficient_nonnegative := hg_nonnegative
      coefficient_integrable := hg_integrable
      relative_energy_integrable := hprod
      good_ae := hgood
      left_trace := hrestart.strong_trace
      right_trace := hv_trace
      left_initial := ?_
      right_initial := hv_initial
      relative_energy := hrelative }
  change u ((0 : ℝ) + s) = u s
  rw [zero_add]

/-- Comparison at the selected restart clock identifies the original
trajectory on its entire closed tail. The conclusion is pointwise in the
normed carrier, including the selected starting time. -/
theorem ComparableOnNonnegative.eq_on_tail
    {u v : ℝ → V} {a₀ : V} {s : ℝ}
    (h : ComparableOnNonnegative (timeTranslate s u) v a₀) :
    ∀ t : ℝ, s ≤ t → u t = v (t - s) := by
  intro t ht
  have heq := h.eq_on_nonnegative (t - s) (sub_nonneg.mpr ht)
  change u ((t - s) + s) = v (t - s) at heq
  rw [sub_add_cancel] at heq
  exact heq

/-- A later shift of the original trajectory agrees with the corresponding
shift of the reference after restriction to nonnegative time. -/
theorem ComparableOnNonnegative.further_timeTranslate_eq
    {u v : ℝ → V} {a₀ : V} {s δ : ℝ}
    (h : ComparableOnNonnegative (timeTranslate s u) v a₀)
    (hsδ : s ≤ δ) :
    (fun t : {t : ℝ // 0 ≤ t} => timeTranslate δ u t.1) =
      (fun t : {t : ℝ // 0 ≤ t} => timeTranslate (δ - s) v t.1) := by
  funext t
  change u (t.1 + δ) = v (t.1 + (δ - s))
  have htime : s ≤ t.1 + δ := by linarith [t.2]
  have heq := h.eq_on_tail (t.1 + δ) htime
  rw [show t.1 + δ - s = t.1 + (δ - s) by ring] at heq
  exact heq

/-- Selected-clock comparison followed by fresh comparison at `δ > s`.
The shifted reference is explicitly a member of the datum-indexed class;
its finite comparison data with every class member are supplied separately.
Only the final restricted singleton representative is rewritten using the
first comparison. No class extensionality in negative time is assumed. -/
theorem restricted_restart_class_eq_singleton
    {Admissible : V → Set (ℝ → V)} {u v : ℝ → V} {s δ : ℝ}
    (hsδ : s < δ)
    (hsource : ComparableOnNonnegative (timeTranslate s u) v (u s))
    (hreference : timeTranslate (δ - s) v ∈ Admissible (u δ))
    (hcomparisons : ∀ w ∈ Admissible (u δ),
      ComparableOnNonnegative w (timeTranslate (δ - s) v) (u δ)) :
    (fun w : ℝ → V => fun t : {t : ℝ // 0 ≤ t} => w t.1) '' Admissible (u δ) =
      {fun t : {t : ℝ // 0 ≤ t} => timeTranslate δ u t.1} := by
  have hsingleton := restricted_class_eq_singleton_of_comparable hreference hcomparisons
  have htail := hsource.further_timeTranslate_eq hsδ.le
  rw [← htail] at hsingleton
  exact hsingleton

end QFA.Assembly.TailComparison
