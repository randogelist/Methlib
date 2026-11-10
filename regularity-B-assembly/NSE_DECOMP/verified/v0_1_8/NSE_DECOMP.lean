import Mathlib

/-!
NSE_DECOMP -- v0_1_8 Lean 4.34.0-rc1 candidate, 2026-11-10.

This file provides a concrete periodic L² Fourier/PDE signature and a deterministic
root assembly from named, UNPROVED analytic endpoints, with candidate proved
positive-time extensionality, reconstruction uniqueness and energy-equality transfer,
plus zero-mode transport identities, strong trace uniqueness, Fourier Leray
solenoidality and H¹-to-H^(1/2) spectral bridges. Version 0.1.7 adds
finite-frequency H^(1/2) energy controls and an algebraic strong-ODE
pressure-corrector interface. Version 0.1.8 proves a candidate finite-window
rough-trace blow-up chain assuming only coefficient-level trace continuity.
The endpoints are STRUCTURE
ARGUMENTS, not axioms or theorems. The unconditional PDE theorem has NOT been proved.

NO_LOCAL_LEAN: this file was not compiled in the creating environment.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology

noncomputable section

namespace NSEDecomp

abbrev Time := ℝ
abbrev Torus (d : ℕ) := UnitAddTorus (Fin d)
abbrev Mode (d : ℕ) := Fin d → ℤ
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev VF (d : ℕ) := Lp (Vec d) 2 (volume : Measure (Torus d))
abbrev Scalar2 := Lp ℝ 2 (volume : Measure (Torus 2))

/-! ### Concrete spatial Fourier and weak-PDE signatures -/

noncomputable def fieldCoeff {d : ℕ} (f : VF d) (k : Mode d) (j : Fin d) : ℂ :=
  ∫ x : Torus d, UnitAddTorus.mFourier (-k) x * (f x j : ℂ)

noncomputable def scalarCoeff (f : Scalar2) (k : Mode 2) : ℂ :=
  ∫ x : Torus 2, UnitAddTorus.mFourier (-k) x * (f x : ℂ)

noncomputable def modeSq {d : ℕ} (k : Mode d) : ℝ :=
  ∑ j : Fin d, (k j : ℝ) ^ 2

noncomputable def freqSq {d : ℕ} (k : Mode d) : ℝ :=
  (2 * Real.pi) ^ 2 * modeSq k

/-! Solenoidality is defined by its exact Fourier divergence symbol. -/
def DivFree {d : ℕ} (f : VF d) : Prop :=
  ∀ k : Mode d, (∑ j : Fin d, (k j : ℂ) * fieldCoeff f k j) = 0

/-! The datum is precisely a planar divergence-free L² velocity and an L²
passive component. No smallness or H^(1/2) hypothesis occurs. -/
structure X2D3CL2 where
  planar : VF 2
  planar_divFree : DivFree planar
  passive : Scalar2

noncomputable def horizontalProjection (x : Torus 3) : Torus 2 :=
  fun i => x i.castSucc

noncomputable def rawLift (v : VF 2) (w : Scalar2) (x : Torus 3) : Vec 3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if h : i.val < 2 then
      v (horizontalProjection x) (⟨i.val, h⟩ : Fin 2)
    else
      w (horizontalProjection x))

/-! The physical L² lift and its almost-everywhere identification are a named
analytic edge, not a postulated coercion. -/
structure LiftBridge where
  lift : X2D3CL2 → VF 3
  represents : ∀ a : X2D3CL2,
    (fun x : Torus 3 => lift a x) =ᵐ[(volume : Measure (Torus 3))]
      rawLift a.planar a.passive
  divFree : ∀ a : X2D3CL2, DivFree (lift a)

noncomputable def quadCoeff {d : ℕ}
    (f : VF d) (k : Mode d) (a j : Fin d) : ℂ :=
  ∫ x : Torus d,
    UnitAddTorus.mFourier (-k) x * (((f x a * f x j : ℝ) : ℂ))

noncomputable def rawTransportCoeff {d : ℕ}
    (f : VF d) (k : Mode d) (j : Fin d) : ℂ :=
  ∑ a : Fin d,
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (k a : ℂ)) *
      quadCoeff f k a j

/-! At k=0 the transport coefficient is already zero. For k ≠ 0 the
explicit Fourier Leray multiplier removes the gradient (pressure) component. -/
noncomputable def projectedTransportCoeff {d : ℕ}
    (f : VF d) (k : Mode d) (j : Fin d) : ℂ :=
  if modeSq k = 0 then rawTransportCoeff f k j
  else
    rawTransportCoeff f k j -
      ((k j : ℂ) / ((modeSq k : ℝ) : ℂ)) *
        (∑ a : Fin d, (k a : ℂ) * rawTransportCoeff f k a)

noncomputable def weakNSIntegrand {d : ℕ}
    (ν : ℝ) (u : Time → VF d) (ψ : Time → ℝ)
    (k : Mode d) (j : Fin d) (t : Time) : ℂ :=
  -((deriv ψ t : ℝ) : ℂ) * fieldCoeff (u t) k j +
    (ψ t : ℂ) *
      ((((ν * freqSq k : ℝ) : ℂ) * fieldCoeff (u t) k j) +
        projectedTransportCoeff (u t) k j)

/-! A concrete Fourier-test weak NSE contract. Its equivalence to the full
physical space-time weak formulation is a separate, OPEN semantic edge. -/
def FourierWeakNS {d : ℕ} (ν : ℝ) (u : Time → VF d) : Prop :=
  ∀ (T : ℝ), 0 < T →
  ∀ (ψ : Time → ℝ), HasCompactSupport ψ →
    tsupport ψ ⊆ Set.Ioo 0 T → ContDiff ℝ 1 ψ →
  ∀ (k : Mode d) (j : Fin d),
    IntervalIntegrable (weakNSIntegrand ν u ψ k j) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, weakNSIntegrand ν u ψ k j t) = 0

noncomputable def dissipation {d : ℕ} (f : VF d) : ℝ≥0∞ :=
  ∑' k : Mode d,
    ENNReal.ofReal
      (freqSq k * (∑ j : Fin d, ‖fieldCoeff f k j‖ ^ 2))

noncomputable def scalarDissipation (w : Scalar2) : ℝ≥0∞ :=
  ∑' k : Mode 2, ENNReal.ofReal (freqSq k * ‖scalarCoeff w k‖ ^ 2)

/-! Extended-nonnegative integrals avoid an off-summable real-tsum junk value
in the energy inequality. -/
def EnergyBound {d : ℕ}
    (ν : ℝ) (a : VF d) (u : Time → VF d) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    ENNReal.ofReal (‖u t‖ ^ 2) +
      ENNReal.ofReal (2 * ν) *
        (∫⁻ s in Set.Icc 0 t, dissipation (u s)) ≤
    ENNReal.ofReal (‖a‖ ^ 2)

def EnergyEquality {d : ℕ}
    (ν : ℝ) (a : VF d) (u : Time → VF d) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    ENNReal.ofReal (‖u t‖ ^ 2) +
      ENNReal.ofReal (2 * ν) *
        (∫⁻ s in Set.Icc 0 t, dissipation (u s)) =
    ENNReal.ofReal (‖a‖ ^ 2)

def PassiveEnergyEquality
    (ν : ℝ) (w₀ : Scalar2) (w : Time → Scalar2) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    ENNReal.ofReal (‖w t‖ ^ 2) +
      ENNReal.ofReal (2 * ν) *
        (∫⁻ s in Set.Icc 0 t, scalarDissipation (w s)) =
    ENNReal.ofReal (‖w₀‖ ^ 2)

/-! The full time-zero contract includes strong L² trace and continuity,
not merely weak convergence of Fourier coefficients. -/
structure GlobalLerayHopf {d : ℕ}
    (ν : ℝ) (a : VF d) (u : Time → VF d) : Prop where
  weakNSE : FourierWeakNS ν u
  divFree : ∀ t : Time, 0 ≤ t → DivFree (u t)
  trace : Tendsto u (nhdsWithin 0 (Set.Ici 0)) (nhds a)
  continuous : ContinuousOn u (Set.Ici 0)
  energy : EnergyBound ν a u
  measurable : ∀ T : Time, 0 < T →
    AEStronglyMeasurable u (volume.restrict (Set.Icc 0 T))

/-! ### Positive-time Fourier-Sobolev and space-time regularity -/

noncomputable def hmTerm {d : ℕ} (m : ℕ) (f : VF d) (k : Mode d) : ℝ :=
  (1 + freqSq k) ^ m * (∑ j : Fin d, ‖fieldCoeff f k j‖ ^ 2)

noncomputable def hmDistanceTerm {d : ℕ}
    (m : ℕ) (f g : VF d) (k : Mode d) : ℝ :=
  (1 + freqSq k) ^ m *
    (∑ j : Fin d, ‖fieldCoeff f k j - fieldCoeff g k j‖ ^ 2)

/-! Fourier characterization: H^m membership for t>0 plus H^m continuity
on the positive half-line. -/
def PositiveHInf {d : ℕ} (u : Time → VF d) : Prop :=
  ∀ m : ℕ,
    (∀ t : Time, 0 < t → Summable (hmTerm m (u t))) ∧
    (∀ t : Time, 0 < t →
      Tendsto
        (fun s : Time => ∑' k : Mode d, hmDistanceTerm m (u s) (u t) k)
        (nhdsWithin t (Set.Ioi 0)) (nhds 0))

/-! Iterated ordinary time derivatives of one complex Fourier mode. -/
noncomputable def timeDeriv : ℕ → (Time → ℂ) → Time → ℂ
  | 0, f, t => f t
  | r + 1, f, t => deriv (timeDeriv r f) t

noncomputable def timeHmTerm {d : ℕ}
    (r m : ℕ) (u : Time → VF d) (t : Time) (k : Mode d) : ℝ :=
  (1 + freqSq k) ^ m *
    (∑ j : Fin d,
      ‖timeDeriv r (fun s => fieldCoeff (u s) k j) t‖ ^ 2)

/-! All time derivatives of all modes have locally uniform Sobolev bounds.
Combined with Fourier reconstruction, this yields a C∞ space-time representative;
that reconstruction is a named, OPEN semantic endpoint. -/
def PositiveTimeCInfFourier {d : ℕ} (u : Time → VF d) : Prop :=
  PositiveHInf u ∧
  (∀ (k : Mode d) (j : Fin d),
    ContDiffOn ℝ ⊤ (fun t => fieldCoeff (u t) k j) (Set.Ioi 0)) ∧
  (∀ (r m : ℕ) (τ T : Time), 0 < τ → τ ≤ T →
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ t : Time, t ∈ Set.Icc τ T →
        Summable (timeHmTerm r m u t) ∧
        (∑' k : Mode d, timeHmTerm r m u t k) ≤ M)

/-! The strict rough-trace corollary uses the actual inhomogeneous
periodic Fourier H^(1/2) norm, not an H12Datum input carrier. -/
noncomputable def hhalfTerm {d : ℕ} (f : VF d) (k : Mode d) : ℝ :=
  Real.sqrt (1 + freqSq k) *
    (∑ j : Fin d, ‖fieldCoeff f k j‖ ^ 2)

def MemHhalf {d : ℕ} (f : VF d) : Prop :=
  Summable (hhalfTerm f)

noncomputable def hhalfNorm {d : ℕ} (f : VF d) : ℝ :=
  Real.sqrt (∑' k : Mode d, hhalfTerm f k)

/-! Fourier support in k₃=0 defines the 2D3C invariant subspace. -/
def TwoD3CInvariant (u : Time → VF 3) : Prop :=
  ∀ (t : Time), 0 ≤ t →
  ∀ (k : Mode 3), k 2 ≠ 0 →
  ∀ j : Fin 3, fieldCoeff (u t) k j = 0

/-! A pressure coefficient family satisfying the unprojected Fourier NSE
at every strictly positive time. The separate Fourier-to-physical semantic
bridge is still OPEN. -/
def ClassicalPressureFourier (ν : ℝ) (u : Time → VF 3) : Prop :=
  ∃ p : Time → Mode 3 → ℂ,
    (∀ t : Time, 0 < t → p t 0 = 0) ∧
    (∀ t : Time, 0 < t → ∀ k : Mode 3,
      p t (-k) = star (p t k)) ∧
    (∀ m : ℕ, ∀ t : Time, 0 < t →
      Summable (fun k : Mode 3 =>
        (1 + freqSq k) ^ m * ‖p t k‖ ^ 2)) ∧
    (∀ k : Mode 3, ContDiffOn ℝ ⊤
      (fun t : Time => p t k) (Set.Ioi 0)) ∧
    (∀ (t : Time), 0 < t → ∀ (k : Mode 3) (j : Fin 3),
      HasDerivAt (fun s : Time => fieldCoeff (u s) k j)
        (-(((ν * freqSq k : ℝ) : ℂ) * fieldCoeff (u t) k j) -
          rawTransportCoeff (u t) k j -
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (k j : ℂ)) * p t k)
        t)

/-! ### Discharged structural implications (no new PDE assumptions) -/

/-- Exact energy equality automatically implies the zero-start energy inequality.
This removes any need for a separately admitted energy-inequality conversion. -/
theorem energyBound_of_energyEquality {d : ℕ}
    {ν : ℝ} {a : VF d} {u : Time → VF d}
    (hE : EnergyEquality ν a u) : EnergyBound ν a u := by
  intro t ht
  exact le_of_eq (hE t ht)

/-- Zero-initial-frequency support is preserved by equality of trajectories
on the physical nonnegative half-line. -/
theorem twoD3CInvariant_congr
    {u v : Time → VF 3}
    (h : ∀ t : Time, 0 ≤ t → u t = v t)
    (hu : TwoD3CInvariant u) : TwoD3CInvariant v := by
  intro t ht k hk j
  rw [← h t ht]
  exact hu t ht k hk j

/-- Two curves with identical positive-time values have identical positive-time
Fourier H^m summability and continuity for every m. -/
theorem positiveHInf_congr {d : ℕ}
    {u v : Time → VF d}
    (h : ∀ t : Time, 0 < t → u t = v t)
    (hu : PositiveHInf u) : PositiveHInf v := by
  intro m
  rcases hu m with ⟨hsummable, hcontinuous⟩
  constructor
  · intro t ht
    rw [← h t ht]
    exact hsummable t ht
  · intro t ht
    have heq :
        (fun s : Time => ∑' k : Mode d,
          hmDistanceTerm m (u s) (u t) k)
        =ᶠ[nhdsWithin t (Set.Ioi 0)]
        (fun s : Time => ∑' k : Mode d,
          hmDistanceTerm m (v s) (v t) k) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [h s hs, h t ht]
    exact (hcontinuous t ht).congr' heq

/-- A function and its replacement by an equal function on the open positive
half-line have identical iterated time derivatives at every positive time. -/
theorem timeDeriv_eqOn_positive
    {f g : Time → ℂ}
    (h : Set.EqOn f g (Set.Ioi 0))
    (r : ℕ) :
    Set.EqOn (timeDeriv r f) (timeDeriv r g) (Set.Ioi 0) := by
  induction r with
  | zero =>
      simpa only [timeDeriv] using h
  | succ r ih =>
      intro t ht
      change deriv (timeDeriv r f) t = deriv (timeDeriv r g) t
      have heventually :
          timeDeriv r f =ᶠ[nhds t] timeDeriv r g := by
        filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
        exact ih hs
      exact heventually.deriv_eq

/-- DISCHARGED ENDPOINT: positive-time Fourier regularity is extensional
under equality on (0,infinity).  The derivative tower is preserved using
local equality of germs, not by rewriting only the value at t. -/
theorem positiveTimeCInfFourier_congr {d : ℕ}
    {u v : Time → VF d}
    (h : ∀ t : Time, 0 < t → u t = v t)
    (hu : PositiveTimeCInfFourier u) :
    PositiveTimeCInfFourier v := by
  rcases hu with ⟨hH, hC, hB⟩
  refine ⟨positiveHInf_congr h hH, ?_, ?_⟩
  · intro k j
    apply (hC k j).congr
    intro t ht
    exact congrArg (fun z : VF d => fieldCoeff z k j) ((h t ht).symm)
  · intro r m τ T hτ hτT
    obtain ⟨M, hM0, hBound⟩ := hB r m τ T hτ hτT
    refine ⟨M, hM0, ?_⟩
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hτ ht.1
    have hderiv (k : Mode d) (j : Fin d) :
        timeDeriv r (fun s => fieldCoeff (u s) k j) t =
        timeDeriv r (fun s => fieldCoeff (v s) k j) t := by
      have hcoeff :
          Set.EqOn
            (fun s => fieldCoeff (u s) k j)
            (fun s => fieldCoeff (v s) k j)
            (Set.Ioi 0) := by
        intro s hs
        exact congrArg (fun z : VF d => fieldCoeff z k j) (h s hs)
      exact (timeDeriv_eqOn_positive hcoeff r) htpos
    have hterm (k : Mode d) :
        timeHmTerm r m u t k = timeHmTerm r m v t k := by
      unfold timeHmTerm
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [hderiv k j]
    have hsame :
        timeHmTerm r m u t = timeHmTerm r m v t := by
      funext k
      exact hterm k
    exact Eq.mp
      (congrArg
        (fun F : Mode d → ℝ => Summable F ∧ (∑' k : Mode d, F k) ≤ M)
        hsame)
      (hBound t ht)

/-! ### Strong energy transport along identical nonnegative-time curves -/

/-- Energy equality is extensional under pointwise equality on the entire
nonnegative-time interval. Crucially, dissipation is integrated only on
`Icc 0 t`; no equality at negative times is required. -/
theorem energyEquality_congr {d : ℕ}
    {ν : ℝ} {a : VF d} {u v : Time → VF d}
    (h : ∀ t : Time, 0 ≤ t → u t = v t)
    (hE : EnergyEquality ν a u) : EnergyEquality ν a v := by
  intro t ht
  have hInt :
      (∫⁻ s in Set.Icc 0 t, dissipation (v s)) =
      (∫⁻ s in Set.Icc 0 t, dissipation (u s)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact congrArg (fun z : VF d => dissipation z) (h s hs.1).symm
  rw [← h t ht, hInt]
  exact hE t ht

/-! ### Passive scalar weak equation on T² -/

noncomputable def passiveTransportCoeff
    (v : VF 2) (w : Scalar2) (k : Mode 2) : ℂ :=
  ∑ j : Fin 2,
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (k j : ℂ)) *
      (∫ x : Torus 2,
        UnitAddTorus.mFourier (-k) x *
          ((v x j : ℂ) * (w x : ℂ)))

noncomputable def passiveWeakIntegrand
    (ν : ℝ) (v : Time → VF 2) (w : Time → Scalar2)
    (ψ : Time → ℝ) (k : Mode 2) (t : Time) : ℂ :=
  -((deriv ψ t : ℝ) : ℂ) * scalarCoeff (w t) k +
    (ψ t : ℂ) *
      ((((ν * freqSq k : ℝ) : ℂ) * scalarCoeff (w t) k) +
        passiveTransportCoeff (v t) (w t) k)

def PassiveWeakEquation
    (ν : ℝ) (v : Time → VF 2) (w : Time → Scalar2) : Prop :=
  ∀ (T : Time), 0 < T →
  ∀ (ψ : Time → ℝ), HasCompactSupport ψ →
    tsupport ψ ⊆ Set.Ioo 0 T → ContDiff ℝ 1 ψ →
  ∀ k : Mode 2,
    IntervalIntegrable (passiveWeakIntegrand ν v w ψ k) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, passiveWeakIntegrand ν v w ψ k t) = 0

/-! The scalar positive-time regularity carries an explicit H^m tower; its
physical C∞ reconstruction belongs to the later semantic bridge. -/
noncomputable def scalarHmTerm (m : ℕ) (w : Scalar2) (k : Mode 2) : ℝ :=
  (1 + freqSq k) ^ m * ‖scalarCoeff w k‖ ^ 2

def PassivePositiveHInf (w : Time → Scalar2) : Prop :=
  ∀ m : ℕ, ∀ t : Time, 0 < t → Summable (scalarHmTerm m (w t))

/-! ### Unconditional Fourier zero-mode and trace lemmas (candidate) -/

/-- Every quadratic transport coefficient has zero spatial mean, because its
Fourier derivative symbol contains a factor `k`. No divergence-free assumption
is needed for this cancellation. -/
theorem rawTransportCoeff_zero_mode {d : ℕ}
    (f : VF d) (j : Fin d) :
    rawTransportCoeff f (0 : Mode d) j = 0 := by
  simp [rawTransportCoeff]

/-- The unit-torus frequency weight vanishes at zero mode. -/
theorem freqSq_zero_mode {d : ℕ} :
    freqSq (0 : Mode d) = 0 := by
  simp [freqSq, modeSq]

/-- Projected NSE transport has zero mode exactly zero, not merely in the
solenoidal quotient. -/
theorem projectedTransportCoeff_zero_mode {d : ℕ}
    (f : VF d) (j : Fin d) :
    projectedTransportCoeff f (0 : Mode d) j = 0 := by
  simp [projectedTransportCoeff, freqSq_zero_mode,
    rawTransportCoeff_zero_mode, modeSq]

/-- The passive scalar's divergence-form transport also has zero Fourier mode. -/
theorem passiveTransportCoeff_zero_mode
    (v : VF 2) (w : Scalar2) :
    passiveTransportCoeff v w (0 : Mode 2) = 0 := by
  simp [passiveTransportCoeff]

/-- At zero frequency, the NSE weak integrand consists only of the temporal
mean-derivative term. This is the algebraic input to conservation of mean. -/
theorem weakNSIntegrand_zero_mode {d : ℕ}
    (ν : ℝ) (u : Time → VF d) (ψ : Time → ℝ)
    (j : Fin d) (t : Time) :
    weakNSIntegrand ν u ψ (0 : Mode d) j t =
      -((deriv ψ t : ℝ) : ℂ) * fieldCoeff (u t) 0 j := by
  simp [weakNSIntegrand, freqSq_zero_mode,
    projectedTransportCoeff_zero_mode]

/-- At zero frequency, passive transport and diffusion vanish. -/
theorem passiveWeakIntegrand_zero_mode
    (ν : ℝ) (v : Time → VF 2) (w : Time → Scalar2)
    (ψ : Time → ℝ) (t : Time) :
    passiveWeakIntegrand ν v w ψ (0 : Mode 2) t =
      -((deriv ψ t : ℝ) : ℂ) * scalarCoeff (w t) 0 := by
  simp [passiveWeakIntegrand, freqSq_zero_mode,
    passiveTransportCoeff_zero_mode]

/-- The zero-mode NSE weak identity has no viscous or nonlinear term. -/
theorem nse_zero_mode_weak_identity {d : ℕ}
    {ν : ℝ} {u : Time → VF d}
    (hNS : FourierWeakNS ν u)
    (T : Time) (hT : 0 < T)
    (ψ : Time → ℝ)
    (hψ : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ Set.Ioo 0 T)
    (hC : ContDiff ℝ 1 ψ)
    (j : Fin d) :
    (∫ t in (0 : ℝ)..T,
      -((deriv ψ t : ℝ) : ℂ) * fieldCoeff (u t) 0 j) = 0 := by
  have h := (hNS T hT ψ hψ hsupp hC (0 : Mode d) j).2
  simpa only [weakNSIntegrand_zero_mode] using h

/-- The passive scalar's spatial mean has zero distributional time derivative. -/
theorem passive_zero_mode_weak_identity
    {ν : ℝ} {v : Time → VF 2} {w : Time → Scalar2}
    (hW : PassiveWeakEquation ν v w)
    (T : Time) (hT : 0 < T)
    (ψ : Time → ℝ)
    (hψ : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ Set.Ioo 0 T)
    (hC : ContDiff ℝ 1 ψ) :
    (∫ t in (0 : ℝ)..T,
      -((deriv ψ t : ℝ) : ℂ) * scalarCoeff (w t) 0) = 0 := by
  have h := (hW T hT ψ hψ hsupp hC (0 : Mode 2)).2
  simpa only [passiveWeakIntegrand_zero_mode] using h

/-- Strong L² initial traces are unique, including for rough data. -/
theorem globalLerayHopf_trace_unique {d : ℕ}
    {ν : ℝ} {a b : VF d} {u : Time → VF d}
    (ha : GlobalLerayHopf ν a u)
    (hb : GlobalLerayHopf ν b u) :
    a = b := by
  exact tendsto_nhds_unique ha.trace hb.trace

/-! ### Spectral regularity and pressure-projection coherence (candidate) -/

/-- Quadratic Fourier frequency is nonnegative. -/
theorem modeSq_nonneg {d : ℕ} (k : Mode d) : 0 ≤ modeSq k := by
  unfold modeSq
  exact Finset.sum_nonneg (fun j _ => sq_nonneg (k j : ℝ))

/-- The exact normalized viscous Fourier frequency is nonnegative. -/
theorem freqSq_nonneg {d : ℕ} (k : Mode d) : 0 ≤ freqSq k := by
  unfold freqSq
  exact mul_nonneg (sq_nonneg _) (modeSq_nonneg k)

/-- The squared Fourier frequency is zero exactly at the zero mode. -/
theorem modeSq_eq_zero_iff {d : ℕ} (k : Mode d) :
    modeSq k = 0 ↔ k = 0 := by
  constructor
  · intro hz
    funext j
    have hsum :
        ∀ i ∈ (Finset.univ : Finset (Fin d)), (k i : ℝ) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (k i : ℝ))).mp (by simpa [modeSq] using hz)
    have hsq : (k j : ℝ) ^ 2 = 0 := hsum j (Finset.mem_univ j)
    have hr : (k j : ℝ) = 0 := by nlinarith
    exact_mod_cast hr
  · rintro rfl
    simp [modeSq]

/-- Fourier projection has no spurious frequency-zero branch. -/
theorem projectedTransportCoeff_zero_of_modeSq_zero {d : ℕ}
    (f : VF d) (k : Mode d) (j : Fin d)
    (hk : modeSq k = 0) :
    projectedTransportCoeff f k j = 0 := by
  have hz : k = 0 := (modeSq_eq_zero_iff k).mp hk
  subst k
  exact projectedTransportCoeff_zero_mode f j

/-- Mode-square as a complex Fourier frequency denominator. -/
theorem modeSq_complex_sum {d : ℕ} (k : Mode d) :
    (modeSq k : ℂ) = ∑ j : Fin d, (k j : ℂ) ^ 2 := by
  simp [modeSq]

/-- The pressure-eliminating Fourier transport multiplier is transverse to k.
This is an algebraic fact about the actual projected nonlinear symbol, not an
assumption that the PDE has already been solved. -/
theorem projectedTransport_solenoidal {d : ℕ}
    (f : VF d) (k : Mode d) :
    (∑ j : Fin d, (k j : ℂ) * projectedTransportCoeff f k j) = 0 := by
  by_cases hz : modeSq k = 0
  · have hk : k = 0 := (modeSq_eq_zero_iff k).mp hz
    subst k
    simp [projectedTransportCoeff_zero_mode]
  · let R : ℂ :=
      ∑ a : Fin d, (k a : ℂ) * rawTransportCoeff f k a
    have hdenom : (modeSq k : ℂ) ≠ 0 := by
      exact_mod_cast hz
    have hsq : (∑ j : Fin d, (k j : ℂ) ^ 2) = (modeSq k : ℂ) :=
      (modeSq_complex_sum k).symm
    -- A finite sum of common-denominator terms factors in the
    -- commutative field of complex numbers; avoid AC-normalizing an opaque sum.
    have hscaled :
        (∑ j : Fin d,
          (((k j : ℂ) ^ 2 / (modeSq k : ℂ)) * R)) =
          ((∑ j : Fin d, (k j : ℂ) ^ 2) / (modeSq k : ℂ)) * R := by
      simp only [div_eq_mul_inv, mul_assoc, Finset.sum_mul]
    have hstep :
        (∑ j : Fin d, (k j : ℂ) * projectedTransportCoeff f k j) =
          R - ((∑ j : Fin d, (k j : ℂ) ^ 2) / (modeSq k : ℂ)) * R := by
      calc
        (∑ j : Fin d, (k j : ℂ) * projectedTransportCoeff f k j)
          = ∑ j : Fin d,
              ((k j : ℂ) * rawTransportCoeff f k j -
                (((k j : ℂ) ^ 2 / (modeSq k : ℂ)) * R)) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    simp only [projectedTransportCoeff, if_neg hz]
                    dsimp [R]
                    ring
        _ = R - ((∑ j : Fin d, (k j : ℂ) ^ 2) / (modeSq k : ℂ)) * R := by
              rw [Finset.sum_sub_distrib, hscaled]
    rw [hstep, hsq]
    simp [hdenom]

/-! ### Pressure-symbol recovery and projected viscous-force coherence (candidate) -/

/-! `pressureCorrector` is the dimensionless longitudinal correction of the
quadratic NSE Fourier transport. A physical pressure coefficient additionally
requires the nonzero `2*pi*I` Fourier-gradient normalization and analytic
regularity; neither is asserted by this definition. -/
noncomputable def pressureCorrector {d : ℕ}
    (f : VF d) (k : Mode d) : ℂ :=
  if modeSq k = 0 then 0
  else (∑ j : Fin d, (k j : ℂ) * rawTransportCoeff f k j) / (modeSq k : ℂ)

/-- The canonical longitudinal correction vanishes on a zero-frequency branch. -/
theorem pressureCorrector_zero_of_modeSq_zero {d : ℕ}
    (f : VF d) (k : Mode d) (hk : modeSq k = 0) :
    pressureCorrector f k = 0 := by
  simp [pressureCorrector, hk]

/-- In particular the physical zero Fourier mode has no pressure correction. -/
theorem pressureCorrector_zero_mode {d : ℕ} (f : VF d) :
    pressureCorrector f (0 : Mode d) = 0 := by
  apply pressureCorrector_zero_of_modeSq_zero
  simp [modeSq]

/-- The nonlinear Leray projection has an exact longitudinal defect. -/
theorem projectedTransportCoeff_eq_raw_sub_corrector {d : ℕ}
    (f : VF d) (k : Mode d) (j : Fin d) :
    projectedTransportCoeff f k j =
      rawTransportCoeff f k j - (k j : ℂ) * pressureCorrector f k := by
  unfold projectedTransportCoeff pressureCorrector
  by_cases hz : modeSq k = 0
  · simp [hz]
  · simp only [if_neg hz, div_eq_mul_inv]
    ring

/-- Unprojected transport is projected transport plus a Fourier gradient. -/
theorem rawTransportCoeff_eq_projected_plus_corrector {d : ℕ}
    (f : VF d) (k : Mode d) (j : Fin d) :
    rawTransportCoeff f k j =
      projectedTransportCoeff f k j + (k j : ℂ) * pressureCorrector f k := by
  rw [projectedTransportCoeff_eq_raw_sub_corrector]
  ring

/-- Divergence of the explicit longitudinal correction has Fourier symbol |k|². -/
theorem pressureCorrector_gradient_divergence {d : ℕ}
    (f : VF d) (k : Mode d) :
    (∑ j : Fin d, (k j : ℂ) * ((k j : ℂ) * pressureCorrector f k)) =
      (modeSq k : ℂ) * pressureCorrector f k := by
  calc
    (∑ j : Fin d, (k j : ℂ) * ((k j : ℂ) * pressureCorrector f k)) =
        (∑ j : Fin d, (k j : ℂ) ^ 2) * pressureCorrector f k := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (modeSq k : ℂ) * pressureCorrector f k := by
          rw [← modeSq_complex_sum k]

/-- At every mode, |k|² times the correction equals raw transport divergence.
This uses previously proved solenoidality, including the frequency-zero case. -/
theorem pressureCorrector_divergence_identity {d : ℕ}
    (f : VF d) (k : Mode d) :
    (modeSq k : ℂ) * pressureCorrector f k =
      (∑ j : Fin d, (k j : ℂ) * rawTransportCoeff f k j) := by
  calc
    (modeSq k : ℂ) * pressureCorrector f k =
        ∑ j : Fin d, (k j : ℂ) * ((k j : ℂ) * pressureCorrector f k) :=
          (pressureCorrector_gradient_divergence f k).symm
    _ = ∑ j : Fin d, (k j : ℂ) *
          (rawTransportCoeff f k j - projectedTransportCoeff f k j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [show rawTransportCoeff f k j - projectedTransportCoeff f k j =
              (k j : ℂ) * pressureCorrector f k by
              rw [projectedTransportCoeff_eq_raw_sub_corrector]
              ring]
    _ = (∑ j : Fin d, (k j : ℂ) * rawTransportCoeff f k j) -
        (∑ j : Fin d, (k j : ℂ) * projectedTransportCoeff f k j) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ j : Fin d, (k j : ℂ) * rawTransportCoeff f k j := by
          rw [projectedTransport_solenoidal f k]
          ring

/-- Divergence-free Fourier modes remain transverse under scalar viscosity. -/
theorem viscousMode_solenoidal {d : ℕ}
    (ν : ℝ) (f : VF d) (hf : DivFree f) (k : Mode d) :
    (∑ j : Fin d, (k j : ℂ) *
      (((ν * freqSq k : ℝ) : ℂ) * fieldCoeff f k j)) = 0 := by
  calc
    (∑ j : Fin d, (k j : ℂ) *
      (((ν * freqSq k : ℝ) : ℂ) * fieldCoeff f k j)) =
        ((ν * freqSq k : ℝ) : ℂ) *
          (∑ j : Fin d, (k j : ℂ) * fieldCoeff f k j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = 0 := by rw [hf k]; ring

/-! This is the Fourier-projected viscous-plus-nonlinear force. -/
noncomputable def projectedNSForce {d : ℕ}
    (ν : ℝ) (f : VF d) (k : Mode d) (j : Fin d) : ℂ :=
  (((ν * freqSq k : ℝ) : ℂ) * fieldCoeff f k j) +
    projectedTransportCoeff f k j

/-- The complete projected NSE force is transverse whenever the datum is. -/
theorem projectedNSForce_solenoidal {d : ℕ}
    (ν : ℝ) (f : VF d) (hf : DivFree f) (k : Mode d) :
    (∑ j : Fin d, (k j : ℂ) * projectedNSForce ν f k j) = 0 := by
  calc
    (∑ j : Fin d, (k j : ℂ) * projectedNSForce ν f k j) =
      (∑ j : Fin d, (k j : ℂ) *
        (((ν * freqSq k : ℝ) : ℂ) * fieldCoeff f k j)) +
      (∑ j : Fin d, (k j : ℂ) * projectedTransportCoeff f k j) := by
        simp only [projectedNSForce]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = 0 := by
      rw [viscousMode_solenoidal ν f hf k, projectedTransport_solenoidal f k]
      ring

/-- Total projected force vanishes at spatial frequency zero. -/
theorem projectedNSForce_zero_mode {d : ℕ}
    (ν : ℝ) (f : VF d) (j : Fin d) :
    projectedNSForce ν f (0 : Mode d) j = 0 := by
  simp [projectedNSForce, freqSq_zero_mode,
    projectedTransportCoeff_zero_mode]

/-! ### Projected Fourier ODE to longitudinal pressure identity (candidate) -/

/-!
This strong positive-time Fourier ODE is NOT inferred from the weak equation
without additional analysis. Its definition exposes the exact required
regularity as a separate, testable interface, not an implicit axiom.
-/
def ProjectedFourierODE {d : ℕ}
    (ν : ℝ) (u : Time → VF d) : Prop :=
  ∀ t : Time, 0 < t → ∀ (k : Mode d) (j : Fin d),
    HasDerivAt (fun s : Time => fieldCoeff (u s) k j)
      (-projectedNSForce ν (u t) k j) t

/-- The projected strong ODE is precisely the unprojected ODE plus the
longitudinal Fourier corrector. Physical pressure additionally requires
normalization by 2*pi*I, reality, smoothness and summability. -/
theorem projectedODE_unprojected_corrector {d : ℕ}
    (ν : ℝ) (u : Time → VF d)
    (h : ProjectedFourierODE ν u)
    (t : Time) (ht : 0 < t) (k : Mode d) (j : Fin d) :
    HasDerivAt (fun s : Time => fieldCoeff (u s) k j)
      (-(((ν * freqSq k : ℝ) : ℂ) * fieldCoeff (u t) k j) -
        rawTransportCoeff (u t) k j +
        (k j : ℂ) * pressureCorrector (u t) k) t := by
  have hforce :
      -projectedNSForce ν (u t) k j =
        -(((ν * freqSq k : ℝ) : ℂ) * fieldCoeff (u t) k j) -
          rawTransportCoeff (u t) k j +
          (k j : ℂ) * pressureCorrector (u t) k := by
    simp only [projectedNSForce, projectedTransportCoeff_eq_raw_sub_corrector]
    ring
  rw [← hforce]
  exact h t ht k j

/-- The spatial mean has zero time derivative in the projected strong ODE.
Mean conservation at all times follows by a separate connectedness argument. -/
theorem projectedODE_zero_mode_hasDerivAt {d : ℕ}
    (ν : ℝ) (u : Time → VF d)
    (h : ProjectedFourierODE ν u)
    (t : Time) (ht : 0 < t) (j : Fin d) :
    HasDerivAt (fun s : Time => fieldCoeff (u s) (0 : Mode d) j) 0 t := by
  simpa only [projectedNSForce_zero_mode, neg_zero] using
    (h t ht (0 : Mode d) j)

/-- The critical H^(1/2) spectral density is nonnegative. -/
theorem hhalfTerm_nonneg {d : ℕ} (f : VF d) (k : Mode d) :
    0 ≤ hhalfTerm f k := by
  unfold hhalfTerm
  apply mul_nonneg (Real.sqrt_nonneg _)
  exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

/-- All positive integer Sobolev spectral densities are nonnegative. -/
theorem hmTerm_nonneg {d : ℕ} (m : ℕ) (f : VF d) (k : Mode d) :
    0 ≤ hmTerm m f k := by
  unfold hmTerm
  apply mul_nonneg
  · exact pow_nonneg (by linarith [freqSq_nonneg k]) m
  · exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

/-- The inhomogeneous H^(1/2) Fourier weight is controlled by H^1. -/
theorem hhalfTerm_le_hmTerm_one {d : ℕ} (f : VF d) (k : Mode d) :
    hhalfTerm f k ≤ hmTerm 1 f k := by
  have hfreq : 0 ≤ freqSq k := freqSq_nonneg k
  have hw : (1 : ℝ) ≤ 1 + freqSq k := by linarith
  have hroot0 : 0 ≤ Real.sqrt (1 + freqSq k) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (1 + freqSq k)) ^ 2 = 1 + freqSq k :=
    Real.sq_sqrt (by linarith)
  have hroot1 : (1 : ℝ) ≤ Real.sqrt (1 + freqSq k) := by
    nlinarith
  have hrootle : Real.sqrt (1 + freqSq k) ≤ 1 + freqSq k := by
    nlinarith
  have hsum : 0 ≤ (∑ j : Fin d, ‖fieldCoeff f k j‖ ^ 2) :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  simpa only [hhalfTerm, hmTerm, pow_one] using
    mul_le_mul_of_nonneg_right hrootle hsum

/-- A genuine Sobolev bridge: finite Fourier H¹ energy forces H^(1/2)
summability, with no smallness hypothesis. -/
theorem memHhalf_of_hmOne_summable {d : ℕ} (f : VF d)
    (hf : Summable (hmTerm 1 f)) : MemHhalf f := by
  exact Summable.of_nonneg_of_le
    (hhalfTerm_nonneg f)
    (hhalfTerm_le_hmTerm_one f)
    hf

/-- Consequently every strictly positive time slice in a positive H∞
tower belongs to the exact periodic H^(1/2) space. -/
theorem positiveHInf_memHhalf {d : ℕ} (u : Time → VF d)
    (h : PositiveHInf u) (t : Time) (ht : 0 < t) :
    MemHhalf (u t) := by
  exact memHhalf_of_hmOne_summable (u t) ((h 1).1 t ht)

/-- Every positive-time C∞ Fourier state has a legitimate finite H^(1/2)
spectral sum on each strictly positive slice. -/
theorem positiveTimeCInfFourier_memHhalf {d : ℕ} (u : Time → VF d)
    (h : PositiveTimeCInfFourier u) (t : Time) (ht : 0 < t) :
    MemHhalf (u t) :=
  positiveHInf_memHhalf u h.1 t ht

/-! ### Finite-frequency estimates toward strict H^(1/2) rough traces -/

/-- Every finite Fourier window has mass bounded by the full H^(1/2)
spectral sum. This is not a boundedness statement for a rough datum. -/
theorem finiteHhalfMass_le_total {d : ℕ}
    (f : VF d) (hf : MemHhalf f) (S : Finset (Mode d)) :
    (∑ k ∈ S, hhalfTerm f k) ≤
      (∑' k : Mode d, hhalfTerm f k) := by
  exact Summable.sum_le_tsum S
    (fun k _ => hhalfTerm_nonneg f k) hf

/-- The norm square equals the spectral sum when it is summable. -/
theorem hhalfNorm_sq_eq_total {d : ℕ}
    (f : VF d) (hf : MemHhalf f) :
    hhalfNorm f ^ 2 = (∑' k : Mode d, hhalfTerm f k) := by
  have hnonneg : (0 : ℝ) ≤ (∑' k : Mode d, hhalfTerm f k) :=
    tsum_nonneg (fun k => hhalfTerm_nonneg f k)
  exact Real.sq_sqrt hnonneg

/-- Uniform H^(1/2) control bounds every finite Fourier-energy window.
This is the finite-dimensional estimate used in a later Fatou/trace proof. -/
theorem finiteHhalfMass_le_norm_sq {d : ℕ}
    (f : VF d) (hf : MemHhalf f) (S : Finset (Mode d)) :
    (∑ k ∈ S, hhalfTerm f k) ≤ hhalfNorm f ^ 2 := by
  rw [hhalfNorm_sq_eq_total f hf]
  exact finiteHhalfMass_le_total f hf S

/-- A single Fourier mode is controlled by the H^(1/2) norm square. -/
theorem hhalfMode_le_norm_sq {d : ℕ}
    (f : VF d) (hf : MemHhalf f) (k : Mode d) :
    hhalfTerm f k ≤ hhalfNorm f ^ 2 := by
  have h := finiteHhalfMass_le_norm_sq f hf ({k} : Finset (Mode d))
  simpa only [Finset.sum_singleton] using h

/-! ### Independent analytic endpoint signatures -/

structure PlanarFlow (ν : ℝ) (a : X2D3CL2) where
  v : Time → VF 2
  equation : FourierWeakNS ν v
  solenoidal : ∀ t, 0 ≤ t → DivFree (v t)
  trace : Tendsto v (nhdsWithin 0 (Set.Ici 0)) (nhds a.planar)
  continuous : ContinuousOn v (Set.Ici 0)
  energyEquality : EnergyEquality ν a.planar v
  positiveSmooth : PositiveTimeCInfFourier v

structure PassiveFlow (ν : ℝ) (a : X2D3CL2) (V : PlanarFlow ν a) where
  w : Time → Scalar2
  equation : PassiveWeakEquation ν V.v w
  trace : Tendsto w (nhdsWithin 0 (Set.Ici 0)) (nhds a.passive)
  continuous : ContinuousOn w (Set.Ici 0)
  energyEquality : PassiveEnergyEquality ν a.passive w
  positiveSmooth : PassivePositiveHInf w

/-! Concrete identification of the reconstructed 3D L² trajectory with the
2D velocity and passive component (no assumed uniqueness). -/
def IsReconstruction (v : Time → VF 2) (w : Time → Scalar2)
    (u : Time → VF 3) : Prop :=
  ∀ t : Time, 0 ≤ t →
    (fun x : Torus 3 => u t x) =ᵐ[(volume : Measure (Torus 3))]
      rawLift (v t) (w t)

/-- The physical reconstruction is unique on the nonnegative time axis,
for fixed planar and passive trajectories. This is purely L² extensionality;
it does not assume Navier--Stokes uniqueness. -/
theorem isReconstruction_unique
    {v : Time → VF 2} {w : Time → Scalar2}
    {u₁ u₂ : Time → VF 3}
    (h₁ : IsReconstruction v w u₁)
    (h₂ : IsReconstruction v w u₂) :
    ∀ t : Time, 0 ≤ t → u₁ t = u₂ t := by
  intro t ht
  apply Lp.ext
  filter_upwards [h₁ t ht, h₂ t ht] with x hleft hright
  exact hleft.trans hright.symm

/-! The unresolved obligations are independent logical inputs. In particular,
'anisotropicUnique' does NOT assume the final NSE_DECOMP conclusion; its input
contains a constructed reference solution with explicit 2D3C and smoothness. -/
structure AnalyticEndpoints where
  bridge : LiftBridge

  planarGlobal :
    ∀ (ν : ℝ), 0 < ν → ∀ a : X2D3CL2, Nonempty (PlanarFlow ν a)

  passiveGlobal :
    ∀ (ν : ℝ), 0 < ν → ∀ (a : X2D3CL2) (V : PlanarFlow ν a),
      Nonempty (PassiveFlow ν a V)

  reconstruct :
    ∀ (ν : ℝ), 0 < ν → ∀ (a : X2D3CL2)
      (V : PlanarFlow ν a) (W : PassiveFlow ν a V),
      ∃ u : Time → VF 3,
        GlobalLerayHopf ν (bridge.lift a) u ∧
        IsReconstruction V.v W.w u

  reconstructionInvariant :
    ∀ (ν : ℝ) (a : X2D3CL2)
      (V : PlanarFlow ν a) (W : PassiveFlow ν a V)
      (u : Time → VF 3),
      IsReconstruction V.v W.w u → TwoD3CInvariant u

  reconstructionSmooth :
    ∀ (ν : ℝ) (a : X2D3CL2)
      (V : PlanarFlow ν a) (W : PassiveFlow ν a V)
      (u : Time → VF 3),
      IsReconstruction V.v W.w u → PositiveTimeCInfFourier u

  reconstructionEnergy :
    ∀ (ν : ℝ) (a : X2D3CL2)
      (V : PlanarFlow ν a) (W : PassiveFlow ν a V)
      (u : Time → VF 3),
      IsReconstruction V.v W.w u → EnergyEquality ν (bridge.lift a) u

  pressureRecovery :
    ∀ (ν : ℝ), 0 < ν → ∀ (a : X2D3CL2)
      (u : Time → VF 3),
      GlobalLerayHopf ν (bridge.lift a) u →
      PositiveTimeCInfFourier u →
      ClassicalPressureFourier ν u

  anisotropicUnique :
    ∀ (ν : ℝ), 0 < ν → ∀ (a : X2D3CL2)
      (u : Time → VF 3),
      GlobalLerayHopf ν (bridge.lift a) u →
      TwoD3CInvariant u →
      PositiveTimeCInfFourier u →
      EnergyEquality ν (bridge.lift a) u →
      ∀ y : Time → VF 3,
        GlobalLerayHopf ν (bridge.lift a) y →
        ∀ t : Time, 0 ≤ t → y t = u t

/-! The boundary norm blow-up needs the Hilbert compactness/trace bridge.
It is mathematically B-tier derived, but no Lean proof body is included yet. -/
structure BoundaryTraceEndpoint (E : AnalyticEndpoints) where
  roughTraceBlowup :
    ∀ (ν : ℝ), 0 < ν → ∀ (a : X2D3CL2)
      (u : Time → VF 3),
      GlobalLerayHopf ν (E.bridge.lift a) u →
      PositiveTimeCInfFourier u →
      ¬ MemHhalf (E.bridge.lift a) →
      Tendsto (fun t : Time => hhalfNorm (u t))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop

/-! ### Boundary blow-up from Fourier coefficient trace continuity -/

/-- Non-summability of a nonnegative Fourier energy density implies finite
spectral windows with arbitrarily large mass. The critical datum is only L². -/
theorem finiteHhalfWindow_unbounded_of_notMemHhalf {d : ℕ}
    (a : VF d) (ha : ¬ MemHhalf a) (B : ℝ) :
    ∃ S : Finset (Mode d), B < ∑ k ∈ S, hhalfTerm a k := by
  classical
  by_contra h
  have hle : ∀ S : Finset (Mode d),
      (∑ k ∈ S, hhalfTerm a k) ≤ B := by
    intro S
    exact le_of_not_gt (by
      intro hgt
      exact h ⟨S, hgt⟩)
  exact ha (summable_of_sum_le (fun k => hhalfTerm_nonneg a k) hle)

/-- Convergence of each complex Fourier coefficient transfers to convergence
of its squared magnitude and the finite component sum. -/
theorem hhalfTerm_tendsto_of_coeffTrace {d : ℕ}
    (a : VF d) (u : Time → VF d)
    (hcoeff : ∀ (k : Mode d) (j : Fin d),
      Tendsto (fun t : Time => fieldCoeff (u t) k j)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (fieldCoeff a k j)))
    (k : Mode d) :
    Tendsto (fun t : Time => hhalfTerm (u t) k)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (hhalfTerm a k)) := by
  have hj (j : Fin d) :
      Tendsto (fun t : Time => ‖fieldCoeff (u t) k j‖ ^ 2)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (‖fieldCoeff a k j‖ ^ 2)) :=
    ((continuous_norm.pow 2).tendsto _).comp (hcoeff k j)
  have hsum :
      Tendsto (fun t : Time => ∑ j : Fin d, ‖fieldCoeff (u t) k j‖ ^ 2)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∑ j : Fin d, ‖fieldCoeff a k j‖ ^ 2)) :=
    tendsto_finsetSum Finset.univ (by
      intro j _
      exact hj j)
  have hweighted :
      Tendsto (fun t : Time => Real.sqrt (1 + freqSq k) *
        (∑ j : Fin d, ‖fieldCoeff (u t) k j‖ ^ 2))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Real.sqrt (1 + freqSq k) *
          (∑ j : Fin d, ‖fieldCoeff a k j‖ ^ 2))) :=
    tendsto_const_nhds.mul hsum
  simpa only [hhalfTerm] using hweighted

/-- Finite-window trace continuity follows from individual coefficient
continuity. No infinite-series limit is exchanged here. -/
theorem finiteHhalfWindowTrace_of_coeffTrace {d : ℕ}
    (a : VF d) (u : Time → VF d)
    (hcoeff : ∀ (k : Mode d) (j : Fin d),
      Tendsto (fun t : Time => fieldCoeff (u t) k j)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (fieldCoeff a k j)))
    (S : Finset (Mode d)) :
    Tendsto (fun t : Time => ∑ k ∈ S, hhalfTerm (u t) k)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ k ∈ S, hhalfTerm a k)) := by
  exact tendsto_finsetSum S (by
    intro k _
    exact hhalfTerm_tendsto_of_coeffTrace a u hcoeff k)

/-- All finite windows of the rough datum are unbounded; coefficient trace
continuity transfers an arbitrarily high finite window to small positive
times. The window is below the full H^(1/2) norm of the positive-time flow. -/
theorem roughTraceBlowup_of_finiteWindowTrace {d : ℕ}
    (a : VF d) (u : Time → VF d)
    (hWindow : ∀ S : Finset (Mode d),
      Tendsto (fun t : Time => ∑ k ∈ S, hhalfTerm (u t) k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∑ k ∈ S, hhalfTerm a k)))
    (hPos : ∀ t : Time, 0 < t → MemHhalf (u t))
    (ha : ¬ MemHhalf a) :
    Tendsto (fun t : Time => hhalfNorm (u t))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  classical
  apply Filter.tendsto_atTop.2
  intro C
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right C 0
  obtain ⟨S, hS⟩ :=
    finiteHhalfWindow_unbounded_of_notMemHhalf a ha (M ^ 2 + 1)
  have hEv : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      M ^ 2 + 1 < ∑ k ∈ S, hhalfTerm (u t) k :=
    (hWindow S).eventually (isOpen_Ioi.mem_nhds hS)
  filter_upwards [hEv, self_mem_nhdsWithin] with t hMass htpos
  have hPart :
      (∑ k ∈ S, hhalfTerm (u t) k) ≤ hhalfNorm (u t) ^ 2 :=
    finiteHhalfMass_le_norm_sq (u t) (hPos t htpos) S
  have hNorm : 0 ≤ hhalfNorm (u t) := Real.sqrt_nonneg _
  have hSq : M ^ 2 < hhalfNorm (u t) ^ 2 := by linarith
  have hOrder : M ≤ hhalfNorm (u t) := by nlinarith
  exact (le_max_left C 0).trans hOrder

/-- A single genuine remaining Fourier-semantic endpoint: strong L²
initial trace implies convergence of each fixed Fourier coefficient.
This is NOT discharged here, and is not equivalent to the full blow-up claim. -/
structure FourierTraceEndpoint (E : AnalyticEndpoints) where
  coefficientTrace :
    ∀ (ν : ℝ), 0 < ν → ∀ (a : X2D3CL2)
      (u : Time → VF 3),
      GlobalLerayHopf ν (E.bridge.lift a) u →
      ∀ (k : Mode 3) (j : Fin 3),
        Tendsto (fun t : Time => fieldCoeff (u t) k j)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (fieldCoeff (E.bridge.lift a) k j))

/-- The original rough-trace endpoint is *derived* from coefficient
trace continuity and positive-time regularity, retaining its exact type. -/
theorem boundaryTraceEndpoint_of_FourierTrace
    (E : AnalyticEndpoints) (F : FourierTraceEndpoint E) :
    BoundaryTraceEndpoint E := by
  refine ⟨?_⟩
  intro ν hν a u hLH hSmooth ha
  apply roughTraceBlowup_of_finiteWindowTrace (E.bridge.lift a) u
  · intro S
    exact finiteHhalfWindowTrace_of_coeffTrace (E.bridge.lift a) u
      (F.coefficientTrace ν hν a u hLH) S
  · intro t ht
    exact positiveTimeCInfFourier_memHhalf u hSmooth t ht
  · exact ha

/-! ### Deterministic theorem chain; no endpoint is discharged here -/

/-!
Conditional root: exact L² datum, one global Leray–Hopf curve, all-order
positive-time Fourier-Sobolev regularity, energy equality and uniqueness among
ALL three-dimensional Leray–Hopf competitors. The argument `E` is an OPEN
analytic proof obligation, not a harmless type-class or a hidden theorem.
-/
theorem NSE_DECOMP
    (E : AnalyticEndpoints)
    (ν : ℝ) (hν : 0 < ν) (a : X2D3CL2) :
    ∃ u : Time → VF 3,
      GlobalLerayHopf ν (E.bridge.lift a) u ∧
      TwoD3CInvariant u ∧
      PositiveTimeCInfFourier u ∧
      ClassicalPressureFourier ν u ∧
      EnergyEquality ν (E.bridge.lift a) u ∧
      ∀ y : Time → VF 3,
        GlobalLerayHopf ν (E.bridge.lift a) y →
        ∀ t : Time, 0 ≤ t → y t = u t := by
  let V : PlanarFlow ν a := Classical.choice (E.planarGlobal ν hν a)
  let W : PassiveFlow ν a V := Classical.choice (E.passiveGlobal ν hν a V)
  obtain ⟨u, hLH, hRec⟩ := E.reconstruct ν hν a V W
  have hInv : TwoD3CInvariant u :=
    E.reconstructionInvariant ν a V W u hRec
  have hSmooth : PositiveTimeCInfFourier u :=
    E.reconstructionSmooth ν a V W u hRec
  have hPressure : ClassicalPressureFourier ν u :=
    E.pressureRecovery ν hν a u hLH hSmooth
  have hEnergy : EnergyEquality ν (E.bridge.lift a) u :=
    E.reconstructionEnergy ν a V W u hRec
  refine ⟨u, hLH, hInv, hSmooth, hPressure, hEnergy, ?_⟩
  exact E.anisotropicUnique ν hν a u hLH hInv hSmooth hEnergy

/-! A useful unconditional logical consequence of the same OPEN endpoint package:
any Leray–Hopf competitor has the same positive-time regularity and 2D3C symmetry. -/
theorem NSE_DECOMP_every_LH_regular
    (E : AnalyticEndpoints)
    (ν : ℝ) (hν : 0 < ν) (a : X2D3CL2)
    (y : Time → VF 3)
    (hy : GlobalLerayHopf ν (E.bridge.lift a) y) :
    PositiveTimeCInfFourier y ∧ TwoD3CInvariant y := by
  obtain ⟨u, _, hInv, hSmooth, _, _, hUnique⟩ := NSE_DECOMP E ν hν a
  have heq : ∀ t : Time, 0 ≤ t → y t = u t := hUnique y hy
  have hpos : ∀ t : Time, 0 < t → u t = y t := by
    intro t ht
    exact (heq t ht.le).symm
  constructor
  · exact positiveTimeCInfFourier_congr hpos hSmooth
  · intro t ht k hk j
    rw [heq t ht]
    exact hInv t ht k hk j

/-! Stronger conditional conclusion: the same admitted analytic endpoints
force every Leray--Hopf competitor to be the unique reconstructed flow, even
if the competitor was not initially assumed to be 2D3C. -/
theorem NSE_DECOMP_every_LH_agrees_with_reconstruction
    (E : AnalyticEndpoints)
    (ν : ℝ) (hν : 0 < ν) (a : X2D3CL2)
    (y : Time → VF 3)
    (hy : GlobalLerayHopf ν (E.bridge.lift a) y) :
    ∃ (V : PlanarFlow ν a) (W : PassiveFlow ν a V),
      IsReconstruction V.v W.w y := by
  let V : PlanarFlow ν a := Classical.choice (E.planarGlobal ν hν a)
  let W : PassiveFlow ν a V := Classical.choice (E.passiveGlobal ν hν a V)
  obtain ⟨u, hLH, hRec⟩ := E.reconstruct ν hν a V W
  have hInv : TwoD3CInvariant u := E.reconstructionInvariant ν a V W u hRec
  have hSmooth : PositiveTimeCInfFourier u :=
    E.reconstructionSmooth ν a V W u hRec
  have hEnergy : EnergyEquality ν (E.bridge.lift a) u :=
    E.reconstructionEnergy ν a V W u hRec
  have heq : ∀ t : Time, 0 ≤ t → y t = u t :=
    E.anisotropicUnique ν hν a u hLH hInv hSmooth hEnergy y hy
  refine ⟨V, W, ?_⟩
  intro t ht
  rw [heq t ht]
  exact hRec t ht

/-! All following results preserve the EXACT original analytic premise
`E : AnalyticEndpoints`. None discharges the open PDE/smoothing endpoints. -/

/-- Any pair of global Leray--Hopf curves from one 2D3C datum agrees,
without imposing the 2D3C restriction on either competitor. -/
theorem NSE_DECOMP_all_LH_unique_pair
    (E : AnalyticEndpoints)
    (ν : ℝ) (hν : 0 < ν) (a : X2D3CL2)
    (y z : Time → VF 3)
    (hy : GlobalLerayHopf ν (E.bridge.lift a) y)
    (hz : GlobalLerayHopf ν (E.bridge.lift a) z) :
    ∀ t : Time, 0 ≤ t → y t = z t := by
  obtain ⟨u, _, _, _, _, _, hUnique⟩ := NSE_DECOMP E ν hν a
  intro t ht
  exact (hUnique y hy t ht).trans (hUnique z hz t ht).symm

/-- The reconstructed energy equality transfers to EVERY Leray--Hopf
competitor, not only to the selected smooth reconstructed trajectory. -/
theorem NSE_DECOMP_all_LH_energyEquality
    (E : AnalyticEndpoints)
    (ν : ℝ) (hν : 0 < ν) (a : X2D3CL2)
    (y : Time → VF 3)
    (hy : GlobalLerayHopf ν (E.bridge.lift a) y) :
    EnergyEquality ν (E.bridge.lift a) y := by
  obtain ⟨u, _, _, _, _, hEnergy, hUnique⟩ := NSE_DECOMP E ν hν a
  have heq : ∀ t : Time, 0 ≤ t → u t = y t := by
    intro t ht
    exact (hUnique y hy t ht).symm
  exact energyEquality_congr heq hEnergy

/-- The admitted pressure-recovery endpoint applies to every competing
Leray--Hopf flow once the proved regularity transport is used. -/
theorem NSE_DECOMP_all_LH_pressureFourier
    (E : AnalyticEndpoints)
    (ν : ℝ) (hν : 0 < ν) (a : X2D3CL2)
    (y : Time → VF 3)
    (hy : GlobalLerayHopf ν (E.bridge.lift a) y) :
    ClassicalPressureFourier ν y := by
  have hReg := (NSE_DECOMP_every_LH_regular E ν hν a y hy).1
  exact E.pressureRecovery ν hν a y hy hReg

/-- The separately admitted boundary compactness endpoint propagates to
EVERY Leray--Hopf competitor in the same exact datum class. -/
theorem NSE_DECOMP_all_LH_strict_HHALF
    (E : AnalyticEndpoints) (B : BoundaryTraceEndpoint E)
    (ν : ℝ) (hν : 0 < ν) (a : X2D3CL2)
    (ha : ¬ MemHhalf (E.bridge.lift a))
    (y : Time → VF 3)
    (hy : GlobalLerayHopf ν (E.bridge.lift a) y) :
    Tendsto (fun t : Time => hhalfNorm (y t))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  have hReg := (NSE_DECOMP_every_LH_regular E ν hν a y hy).1
  exact B.roughTraceBlowup ν hν a y hy hReg ha

/-! Strict L² \ H^(1/2) corollary. Its new input B is the UNPROVED
boundary-compactness endpoint; it is not supplied by the root compilation. -/
theorem NSE_DECOMP_STRICT_HHALF
    (E : AnalyticEndpoints) (B : BoundaryTraceEndpoint E)
    (ν : ℝ) (hν : 0 < ν) (a : X2D3CL2)
    (ha : ¬ MemHhalf (E.bridge.lift a)) :
    ∃ u : Time → VF 3,
      GlobalLerayHopf ν (E.bridge.lift a) u ∧
      PositiveTimeCInfFourier u ∧
      Tendsto (fun t : Time => hhalfNorm (u t))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  obtain ⟨u, hLH, _, hSmooth, _, _, _⟩ := NSE_DECOMP E ν hν a
  exact ⟨u, hLH, hSmooth, B.roughTraceBlowup ν hν a u hLH hSmooth ha⟩


/-! ### Exact strict-rough-trace theorem under the reduced coefficient trace endpoint -/

/-- The strict-rough-trace theorem requires only the Fourier coefficient trace
endpoint in place of an explicitly assumed H^(1/2) blow-up certificate. -/
theorem NSE_DECOMP_STRICT_HHALF_of_FourierTrace
    (E : AnalyticEndpoints) (F : FourierTraceEndpoint E)
    (ν : ℝ) (hν : 0 < ν) (a : X2D3CL2)
    (ha : ¬ MemHhalf (E.bridge.lift a)) :
    ∃ u : Time → VF 3,
      GlobalLerayHopf ν (E.bridge.lift a) u ∧
      PositiveTimeCInfFourier u ∧
      Tendsto (fun t : Time => hhalfNorm (u t))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  exact NSE_DECOMP_STRICT_HHALF E
    (boundaryTraceEndpoint_of_FourierTrace E F) ν hν a ha

/-- Every Leray--Hopf competitor also inherits the boundary blow-up under
coefficient-level trace continuity and the original analytic endpoints. -/
theorem NSE_DECOMP_all_LH_strict_HHALF_of_FourierTrace
    (E : AnalyticEndpoints) (F : FourierTraceEndpoint E)
    (ν : ℝ) (hν : 0 < ν) (a : X2D3CL2)
    (ha : ¬ MemHhalf (E.bridge.lift a))
    (y : Time → VF 3)
    (hy : GlobalLerayHopf ν (E.bridge.lift a) y) :
    Tendsto (fun t : Time => hhalfNorm (y t))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  exact NSE_DECOMP_all_LH_strict_HHALF E
    (boundaryTraceEndpoint_of_FourierTrace E F) ν hν a ha y hy

#print axioms finiteHhalfWindow_unbounded_of_notMemHhalf
#print axioms hhalfTerm_tendsto_of_coeffTrace
#print axioms finiteHhalfWindowTrace_of_coeffTrace
#print axioms roughTraceBlowup_of_finiteWindowTrace
#print axioms boundaryTraceEndpoint_of_FourierTrace
#print axioms NSE_DECOMP_STRICT_HHALF_of_FourierTrace
#print axioms NSE_DECOMP_all_LH_strict_HHALF_of_FourierTrace

#print axioms projectedODE_unprojected_corrector
#print axioms projectedODE_zero_mode_hasDerivAt
#print axioms finiteHhalfMass_le_total
#print axioms hhalfNorm_sq_eq_total
#print axioms finiteHhalfMass_le_norm_sq
#print axioms hhalfMode_le_norm_sq

#print axioms pressureCorrector_zero_of_modeSq_zero
#print axioms pressureCorrector_zero_mode
#print axioms projectedTransportCoeff_eq_raw_sub_corrector
#print axioms rawTransportCoeff_eq_projected_plus_corrector
#print axioms pressureCorrector_gradient_divergence
#print axioms pressureCorrector_divergence_identity
#print axioms viscousMode_solenoidal
#print axioms projectedNSForce_solenoidal
#print axioms projectedNSForce_zero_mode

#print axioms modeSq_nonneg
#print axioms freqSq_nonneg
#print axioms modeSq_eq_zero_iff
#print axioms projectedTransportCoeff_zero_of_modeSq_zero
#print axioms modeSq_complex_sum
#print axioms projectedTransport_solenoidal
#print axioms hhalfTerm_nonneg
#print axioms hmTerm_nonneg
#print axioms hhalfTerm_le_hmTerm_one
#print axioms memHhalf_of_hmOne_summable
#print axioms positiveHInf_memHhalf
#print axioms positiveTimeCInfFourier_memHhalf

#print axioms rawTransportCoeff_zero_mode
#print axioms freqSq_zero_mode
#print axioms projectedTransportCoeff_zero_mode
#print axioms passiveTransportCoeff_zero_mode
#print axioms weakNSIntegrand_zero_mode
#print axioms passiveWeakIntegrand_zero_mode
#print axioms nse_zero_mode_weak_identity
#print axioms passive_zero_mode_weak_identity
#print axioms globalLerayHopf_trace_unique

#print axioms energyBound_of_energyEquality
#print axioms energyEquality_congr
#print axioms twoD3CInvariant_congr
#print axioms positiveHInf_congr
#print axioms timeDeriv_eqOn_positive
#print axioms positiveTimeCInfFourier_congr
#print axioms isReconstruction_unique
#print axioms NSE_DECOMP_every_LH_agrees_with_reconstruction
#print axioms NSE_DECOMP_all_LH_unique_pair
#print axioms NSE_DECOMP_all_LH_energyEquality
#print axioms NSE_DECOMP_all_LH_pressureFourier
#print axioms NSE_DECOMP_all_LH_strict_HHALF
#print axioms NSE_DECOMP
#print axioms NSE_DECOMP_every_LH_regular
#print axioms NSE_DECOMP_STRICT_HHALF

end NSEDecomp
