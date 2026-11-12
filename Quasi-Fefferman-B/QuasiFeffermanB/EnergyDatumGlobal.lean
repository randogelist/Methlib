import QuasiFeffermanB.EnergyDatumApproximation
import QuasiFeffermanB.EnergyModalEquation

/-! A global actual Fourier evolution for each physical finite-energy datum.
The conclusion includes the nonlinear integral equation and the original
physical datum's Fourier trace. This is an intermediate existence theorem;
the physical Leray--Hopf record is assembled separately. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval ENNReal
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem ENERGY_DATUM_GLOBAL_MODAL_LIMIT
    (ν : ℝ) (hν : 0 < ν) (a : EnergyDatum) :
    ∃ U : ℝ → TorusSobolev 0, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ t, 0 ≤ t → ‖U t‖ ≤ ‖a.val‖) ∧
      (∀ k i, ContinuousOn (fun t => (U t).val k i) (Ici 0)) ∧
      (U 0).val = datumFourierCoeff (a.val : Field) ∧
      (∀ t, 0 ≤ t → SpectralReality (U t).val ∧
        SpectralSolenoidal (U t).val ∧ SpectralMeanZero (U t).val) ∧
      (∀ t, 0 ≤ t → ∀ k i, (U t).val k i = (U 0).val k i +
        ∫ r in (0 : ℝ)..t, fullFourierRhs ν (U r) k i) ∧
      (∀ T k i, TendstoUniformlyOn
        (fun n t => (energyDatumGalerkinFamily ν hν.le a (φ n)).coeff t k i)
        (fun t => (U t).val k i) atTop (Icc (0 : ℝ) T)) ∧
      (∀ T : ℝ, 0 ≤ T → ∃ v : EnergyTimeH0L2 T,
        Tendsto (fun n => (energyDatumGalerkinFamily ν hν.le a (φ n)).energyTimeH0L2 T)
          atTop (𝓝 v) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), v t = U t)) := by
  let A : ℕ → Field := fun n =>
    finiteSynthesis (n + 1) (datumFourierCoeff (a.val : Field))
  let g := energyDatumGalerkinFamily ν hν.le a
  obtain ⟨U, φ, hφ, hnorm, hcont, hcoeff, htime⟩ :=
    ENERGY_GALERKIN_GLOBAL_LIMIT ν hν A (fun n => n + 1) g
      ‖a.val‖ (norm_nonneg _) (energyDatumGalerkinFamily_energy_initial ν hν.le a)
  have hp (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
      Tendsto (fun n => (g (φ n)).coeff t k i) atTop (𝓝 ((U t).val k i)) :=
    (hcoeff (t + 1) k i).tendsto_at ⟨ht, by linarith⟩
  have hinit : (U 0).val = datumFourierCoeff (a.val : Field) := by
    funext k i
    have hlim := hp 0 le_rfl k i
    have heq : (fun n => (g (φ n)).coeff 0 k i) =ᶠ[atTop]
        (fun _ => datumFourierCoeff (a.val : Field) k i) := by
      by_cases hk : k = 0
      · subst k
        apply Filter.Eventually.of_forall
        intro n
        rw [energyDatumGalerkinFamily_initial]
        simp only [cutoffCoeff, if_neg (cutoffModes_zero_not_mem _), Pi.zero_apply,
          a.property.fourier_constraints.2.2 i]
      · filter_upwards [eventually_mem_cutoffModes_strictMono φ hφ k hk] with n hn
        rw [energyDatumGalerkinFamily_initial]
        simp only [cutoffCoeff, if_pos hn]
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' heq.symm)
  have hspectral (t : ℝ) (ht : 0 ≤ t) :=
    energy_modal_limit_constraints ν (fun n => A (φ n)) (fun n => φ n + 1)
      (fun n => g (φ n)) U hp t ht
  refine ⟨U, φ, hφ, hnorm, hcont, hinit, hspectral, ?_, hcoeff, htime⟩
  intro t ht k i
  obtain ⟨v, hv, hcompat⟩ := htime t ht
  apply ENERGY_GALERKIN_MODAL_INTEGRAL ν hν.le
    (fun n => A (φ n)) (fun n => φ n + 1) (fun n => g (φ n))
    ‖a.val‖ t (norm_nonneg _) ht
    (fun n => energyDatumGalerkinFamily_energy_initial ν hν.le a (φ n))
    (fun k hk => eventually_mem_cutoffModes_strictMono φ hφ k hk)
    U v (fun s hs k i => hp s hs.1 k i) hv hcompat t ⟨ht, le_rfl⟩ k i

end
end QuasiFeffermanB
