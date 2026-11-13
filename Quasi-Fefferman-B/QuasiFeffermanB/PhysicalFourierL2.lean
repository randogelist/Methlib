import QuasiFeffermanB.SpatialAdmission

/-! The physical cube and the normalized torus have the same actual L2
Fourier coordinates, including arbitrary rough L2 representatives. -/

set_option autoImplicit false
set_option Elab.async true
noncomputable section
open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff ENNReal Topology

namespace QuasiFeffermanB

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem torusDatumRepresentative_measurePreserving :
    MeasurePreserving torusDatumRepresentative volume (volume.restrict unitCube) := by
  let S : Set (Fin 3 → ℝ) :=
    {x | ∀ i, x i ∈ Ioc ((0 : Fin 3 → ℝ) i) (((0 : Fin 3 → ℝ) i) + 1)}
  have hS : MeasurableSet S := MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  have hSprod : S = Set.univ.pi (fun _ : Fin 3 => Ioc (0 : ℝ) 1) := by
    ext x
    simp only [S, Pi.zero_apply, zero_add, Set.mem_setOf_eq,
      Set.mem_pi, Set.mem_univ, forall_true_left]
  have hSmeasure : (volume : Measure (Fin 3 → ℝ)).restrict S = unitProductMeasure 3 := by
    change ((Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict S) = _
    rw [hSprod, Measure.restrict_pi_pi]
    have hinterval : (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1) = unitIntervalMeasure :=
      Measure.restrict_congr_set Ioc_ae_eq_Icc
    simp only [hinterval]
    rfl
  have hsub : MeasurePreserving (Subtype.val : S → (Fin 3 → ℝ))
      (Measure.comap Subtype.val volume) (unitProductMeasure 3) := by
    rw [← hSmeasure]
    exact ⟨measurable_subtype_coe, map_comap_subtype_coe hS volume⟩
  have htoLp : MeasurePreserving (@WithLp.toLp 2 (Fin 3 → ℝ))
      (unitProductMeasure 3) (volume.restrict unitCube) := by
    have h := (PiLp.volume_preserving_toLp (Fin 3)).restrict_preimage
      isCompact_unitCube.measurableSet
    change MeasurePreserving (@WithLp.toLp 2 (Fin 3 → ℝ))
      ((Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict
        ((@WithLp.toLp 2 (Fin 3 → ℝ)) ⁻¹' unitCube)) (volume.restrict unitCube) at h
    have hpre : (@WithLp.toLp 2 (Fin 3 → ℝ)) ⁻¹' unitCube =
        Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1) := by
      ext x
      constructor
      · intro hx i _
        exact hx i
      · intro hx i
        exact hx i (Set.mem_univ i)
    rw [hpre, Measure.restrict_pi_pi] at h
    exact h
  have heq : MeasurePreserving (UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ))
      volume (Measure.comap (Subtype.val : S → (Fin 3 → ℝ)) volume) := by
    exact UnitAddTorus.measurePreserving_equivPiIoc (0 : Fin 3 → ℝ)
  change MeasurePreserving
    (fun θ : UnitAddTorus (Fin 3) =>
      WithLp.toLp 2 ((UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ) θ).val))
    volume (volume.restrict unitCube)
  exact htoLp.comp (hsub.comp heq)

theorem rough_torusDatumComponent_memLp (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (i : Fin 3) :
    MemLp (torusDatumComponent v i) 2 (volume : Measure (UnitAddTorus (Fin 3))) := by
  exact (physical_complex_coordinate_memLp v hv i).comp_measurePreserving
    torusDatumRepresentative_measurePreserving

def physicalTorusComponentL2 (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (i : Fin 3) : TorusScalarL2 :=
  (rough_torusDatumComponent_memLp v hv i).toLp (torusDatumComponent v i)

theorem physicalTorusComponentL2_coeff (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (i : Fin 3) (k : Frequency) :
    UnitAddTorus.mFourierBasis.repr (physicalTorusComponentL2 v hv i) k =
      datumFourierCoeff v k i := by
  rw [UnitAddTorus.mFourierBasis_repr]
  calc
    _ = UnitAddTorus.mFourierCoeff (torusDatumComponent v i) k := by
      apply integral_congr_ae
      filter_upwards [(rough_torusDatumComponent_memLp v hv i).coeFn_toLp] with θ hθ
      simp only [physicalTorusComponentL2] at hθ ⊢
      rw [hθ]
    _ = _ := torusDatumComponent_fourierCoeff v i k

theorem physicalTorusComponentL2_norm_sq (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (i : Fin 3) :
    ‖physicalTorusComponentL2 v hv i‖ ^ 2 =
      ∫ x in unitCube, ‖(v x i : ℂ)‖ ^ 2 := by
  rw [physicalTorusComponentL2, Lp.norm_toLp]
  have he : eLpNorm (torusDatumComponent v i) 2 volume =
      eLpNorm (fun x => (v x i : ℂ)) 2 (volume.restrict unitCube) :=
    eLpNorm_comp_measurePreserving
      (physical_complex_coordinate_memLp v hv i).aestronglyMeasurable
      torusDatumRepresentative_measurePreserving
  rw [he]
  exact critical_eLpNorm_two_toReal_sq _ (physical_complex_coordinate_memLp v hv i)

theorem physicalTorusComponentL2_sum_norm_sq (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) :
    (∑ i : Fin 3, ‖physicalTorusComponentL2 v hv i‖ ^ 2) = physicalEnergy v := by
  simp_rw [physicalTorusComponentL2_norm_sq]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    (physical_complex_coordinate_memLp v hv i).norm.integrable_sq)]
  rw [physicalEnergy_eq_integral_norm_sq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (∑ i : Fin 3, ‖(v x i : ℂ)‖ ^ 2) = ‖v x‖ ^ 2
    calc
      (∑ i : Fin 3, ‖(v x i : ℂ)‖ ^ 2) =
          ∑ i : Fin 3, ‖v x i‖ ^ 2 := by simp only [Complex.norm_real]
      _ = ‖v x‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (v x)).symm

theorem physicalL2_coefficientEnergy_le (N : ℕ) (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) :
    coefficientEnergy N (datumFourierCoeff v) ≤ physicalEnergy v := by
  have hi (i : Fin 3) :
      (∑ k ∈ cutoffModes N, Complex.normSq (datumFourierCoeff v k i)) ≤
        ‖physicalTorusComponentL2 v hv i‖ ^ 2 := by
    have h := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num)
      (UnitAddTorus.mFourierBasis.repr (physicalTorusComponentL2 v hv i)) (cutoffModes N)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, physicalTorusComponentL2_coeff,
      Complex.normSq_eq_norm_sq, UnitAddTorus.mFourierBasis.repr.norm_map] using h
  calc
    coefficientEnergy N (datumFourierCoeff v) =
        ∑ i : Fin 3, ∑ k ∈ cutoffModes N, Complex.normSq (datumFourierCoeff v k i) :=
      Finset.sum_comm
    _ ≤ ∑ i : Fin 3, ‖physicalTorusComponentL2 v hv i‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := physicalTorusComponentL2_sum_norm_sq v hv

theorem physicalL2_fourier_mem (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) :
    Memℓp (fun ki : FourierIndex => datumFourierCoeff v ki.1 ki.2) 2 := by
  classical
  apply memℓp_gen' (C := physicalEnergy v)
  intro S
  have hsub : S ⊆ (S.image Prod.fst).product (Finset.univ : Finset (Fin 3)) := by
    intro ki hki
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨ki, hki, rfl⟩, Finset.mem_univ _⟩
  have hi (i : Fin 3) :
      (∑ k ∈ S.image Prod.fst, ‖datumFourierCoeff v k i‖ ^ 2) ≤
        ‖physicalTorusComponentL2 v hv i‖ ^ 2 := by
    have h := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num)
      (UnitAddTorus.mFourierBasis.repr (physicalTorusComponentL2 v hv i)) (S.image Prod.fst)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, physicalTorusComponentL2_coeff,
      UnitAddTorus.mFourierBasis.repr.norm_map] using h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  calc
    (∑ ki ∈ S, ‖datumFourierCoeff v ki.1 ki.2‖ ^ 2) ≤
        ∑ ki ∈ (S.image Prod.fst).product (Finset.univ : Finset (Fin 3)),
          ‖datumFourierCoeff v ki.1 ki.2‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = ∑ k ∈ S.image Prod.fst, ∑ i : Fin 3, ‖datumFourierCoeff v k i‖ ^ 2 :=
      Finset.sum_product _ _ _
    _ = ∑ i : Fin 3, ∑ k ∈ S.image Prod.fst, ‖datumFourierCoeff v k i‖ ^ 2 :=
      Finset.sum_comm
    _ ≤ ∑ i : Fin 3, ‖physicalTorusComponentL2 v hv i‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = physicalEnergy v := physicalTorusComponentL2_sum_norm_sq v hv

def physicalFourierSequence (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) : FourierVectorSequence :=
  ⟨fun ki => datumFourierCoeff v ki.1 ki.2, physicalL2_fourier_mem v hv⟩

theorem physicalFourierSequence_component (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (i : Fin 3) :
    fourierVectorComponent (physicalFourierSequence v hv) i =
      UnitAddTorus.mFourierBasis.repr (physicalTorusComponentL2 v hv i) := by
  apply lp.ext
  funext k
  change datumFourierCoeff v k i = _
  exact (physicalTorusComponentL2_coeff v hv i k).symm

theorem physicalFourierSequence_norm_sq (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) :
    ‖physicalFourierSequence v hv‖ ^ 2 = physicalEnergy v := by
  rw [← fourierVectorComponent_sum_norm_sq]
  simp_rw [physicalFourierSequence_component, UnitAddTorus.mFourierBasis.repr.norm_map]
  exact physicalTorusComponentL2_sum_norm_sq v hv

theorem physical_datumFourierCoeff_sub (v w : Field)
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hw : MemLp w 2 (volume.restrict unitCube)) :
    datumFourierCoeff (v - w) = datumFourierCoeff v - datumFourierCoeff w := by
  funext k i
  have heq : datumFourierIntegrand (v - w) k i =
      datumFourierIntegrand v k i - datumFourierIntegrand w k i := by
    funext x
    simp [datumFourierIntegrand, Complex.ofReal_sub, mul_sub]
  change (∫ x in unitCube, datumFourierIntegrand (v - w) k i x) = _
  rw [heq, integral_sub' (physical_datumFourierIntegrand_integrable v hv k i)
    (physical_datumFourierIntegrand_integrable w hw k i)]
  rfl

theorem physicalL2_fourier_injective (a b : PhysicalCubeL2)
    (heq : datumFourierCoeff (a : Field) = datumFourierCoeff (b : Field)) : a = b := by
  let d : Field := (a : Field) - (b : Field)
  have hd : MemLp d 2 (volume.restrict unitCube) := (Lp.memLp a).sub (Lp.memLp b)
  have hc : datumFourierCoeff d = 0 := by
    rw [physical_datumFourierCoeff_sub _ _ (Lp.memLp a) (Lp.memLp b), heq, sub_self]
  have hs : physicalFourierSequence d hd = 0 := by
    apply lp.ext
    funext ki
    change datumFourierCoeff d ki.1 ki.2 = 0
    rw [hc]
    rfl
  have hnorm : ‖a - b‖ ^ 2 = 0 := by
    calc
      ‖a - b‖ ^ 2 = physicalEnergy d := by
        rw [physicalEnergy_eq_toLp_norm_sq d hd]
        have hlp : hd.toLp d = a - b := by
          rw [(Lp.memLp a).toLp_sub (Lp.memLp b), Lp.toLp_coeFn, Lp.toLp_coeFn]
        rw [hlp]
      _ = ‖physicalFourierSequence d hd‖ ^ 2 := (physicalFourierSequence_norm_sq d hd).symm
      _ = 0 := by rw [hs]; simp
  exact sub_eq_zero.mp (norm_eq_zero.mp ((sq_eq_zero_iff).mp hnorm))

theorem physicalH1HalfDatum_physicalL2
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) (hz : SpectralMeanZero (datumFourierCoeff v)) :
    criticalInitialPhysicalL2 (physicalH1HalfDatum hv hz) = hv.velocity_L2.toLp v := by
  apply physicalL2_fourier_injective
  have hr : SpectralReality (criticalCoeff 1 (physicalH1HalfDatum hv hz)) := by
    rw [physicalH1HalfDatum_coeff]
    exact datumFourierCoeff_reality v
  have hm : SpectralMeanZero (criticalCoeff 1 (physicalH1HalfDatum hv hz)) := by
    rw [physicalH1HalfDatum_coeff]
    exact hz
  rw [criticalInitialPhysicalL2_fourierCoeff _ hr hm, physicalH1HalfDatum_coeff,
    criticalCube_datumFourierCoeff_congr_ae hv.velocity_L2.coeFn_toLp]

def physicalL2SobolevDatum (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) : CriticalSobolev 0 :=
  criticalSobolevOfCoeff 0 (datumFourierCoeff v) (by
    have hw : criticalWeightedCoeff (0 : ℤ) (datumFourierCoeff v) =
        (fun ki : FourierIndex => datumFourierCoeff v ki.1 ki.2) := by
      funext ki
      change (criticalHalfWeight ki.1 : ℂ) ^ (0 : ℤ) *
        datumFourierCoeff v ki.1 ki.2 = datumFourierCoeff v ki.1 ki.2
      rw [zpow_zero, one_mul]
    rw [hw]
    exact physicalL2_fourier_mem v hv)

@[simp] theorem physicalL2SobolevDatum_coeff (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) :
    criticalCoeff 0 (physicalL2SobolevDatum v hv) = datumFourierCoeff v :=
  criticalSobolevOfCoeff_coeff 0 _ _

theorem physicalL2SobolevDatum_norm (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) :
    ‖physicalL2SobolevDatum v hv‖ = ‖hv.toLp v‖ := by
  have hr : criticalSobolevRepr 0 (physicalL2SobolevDatum v hv) =
      physicalFourierSequence v hv := by
    apply lp.ext
    funext ki
    simp only [criticalSobolevRepr_apply, criticalWeightedCoeff, zpow_zero,
      one_mul, physicalL2SobolevDatum_coeff]
    rfl
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖physicalL2SobolevDatum v hv‖ ^ 2 =
        ‖criticalSobolevRepr 0 (physicalL2SobolevDatum v hv)‖ ^ 2 := by
      rw [(criticalSobolevRepr 0).norm_map]
    _ = physicalEnergy v := by rw [hr, physicalFourierSequence_norm_sq]
    _ = ‖hv.toLp v‖ ^ 2 := physicalEnergy_eq_toLp_norm_sq v hv

theorem physicalL2SobolevDatum_sub (v w : Field)
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hw : MemLp w 2 (volume.restrict unitCube)) :
    physicalL2SobolevDatum (v - w) (hv.sub hw) =
      physicalL2SobolevDatum v hv - physicalL2SobolevDatum w hw := by
  apply criticalCoeff_injective 0
  change criticalCoeff 0 (physicalL2SobolevDatum (v - w) (hv.sub hw)) =
    criticalCoeff 0 (physicalL2SobolevDatum v hv) -
      criticalCoeff 0 (physicalL2SobolevDatum w hw)
  simp only [physicalL2SobolevDatum_coeff, physical_datumFourierCoeff_sub v w hv hw]

theorem physicalL2SobolevDatum_finite (N : ℕ) (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) :
    physicalL2SobolevDatum (finiteSynthesis N (datumFourierCoeff v))
      (critical_continuous_memLp_cube _ (finiteSynthesis_contDiff N _).continuous 2) =
        criticalFiniteSobolev 0 N (datumFourierCoeff v) := by
  apply criticalCoeff_injective 0
  rw [physicalL2SobolevDatum_coeff, criticalFiniteSobolev_coeff]
  exact criticalGalerkin_datumFourierCoeff_finiteSynthesis N _ (datumFourierCoeff_reality v)

/-- Exact finite Fourier cutoff convergence for arbitrary mean-zero physical L2 data. -/
theorem physicalL2_cutoff_tendsto (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hz : SpectralMeanZero (datumFourierCoeff v)) :
    Tendsto (fun N => physicalFieldL2 (finiteSynthesis N (datumFourierCoeff v))
      (finiteSynthesis_contDiff N _).continuous) atTop (𝓝 (hv.toLp v)) := by
  let a : CriticalSobolev 0 := physicalL2SobolevDatum v hv
  have hzero : SpectralMeanZero (criticalCoeff 0 a) := by
    rw [physicalL2SobolevDatum_coeff]
    exact hz
  have hcritical : Tendsto
      (fun N => criticalFiniteSobolev 0 N (datumFourierCoeff v)) atTop (𝓝 a) := by
    simpa only [a, physicalL2SobolevDatum_coeff] using criticalFiniteSobolev_tendsto 0 a hzero
  have hdist (N : ℕ) :
      dist (physicalFieldL2 (finiteSynthesis N (datumFourierCoeff v))
        (finiteSynthesis_contDiff N _).continuous) (hv.toLp v) =
          ‖criticalFiniteSobolev 0 N (datumFourierCoeff v) - a‖ := by
    let w : Field := finiteSynthesis N (datumFourierCoeff v)
    have hw : MemLp w 2 (volume.restrict unitCube) :=
      critical_continuous_memLp_cube _ (finiteSynthesis_contDiff N _).continuous 2
    change dist (hw.toLp w) (hv.toLp v) = _
    rw [dist_eq_norm, ← hw.toLp_sub hv,
      ← physicalL2SobolevDatum_norm (w - v) (hw.sub hv),
      physicalL2SobolevDatum_sub w v hw hv]
    rw [physicalL2SobolevDatum_finite N v hv]
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp_rw [hdist]
  simpa only [sub_self, norm_zero] using (hcritical.sub_const a).norm

theorem physicalL2_cutoff_eLpNorm_tendsto (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hz : SpectralMeanZero (datumFourierCoeff v)) :
    Tendsto (fun N => eLpNorm (finiteSynthesis N (datumFourierCoeff v) - v) 2
      (volume.restrict unitCube)) atTop (𝓝 0) := by
  have h := ((physicalL2_cutoff_tendsto v hv hz).sub_const (hv.toLp v)).enorm
  have heq (N : ℕ) :
      ‖physicalFieldL2 (finiteSynthesis N (datumFourierCoeff v))
          (finiteSynthesis_contDiff N _).continuous - hv.toLp v‖ₑ =
        eLpNorm (finiteSynthesis N (datumFourierCoeff v) - v) 2
          (volume.restrict unitCube) := by
    rw [physicalFieldL2, ← MemLp.toLp_sub, Lp.enorm_toLp]
  simpa only [heq, sub_self, enorm_zero] using h

def zeroSobolevPhysicalL2 (a : CriticalSobolev 0) : PhysicalCubeL2 :=
  torusToPhysicalCubeL2 (torusSobolevL2 (criticalH0Equiv a))

theorem zeroSobolevPhysicalL2_continuous : Continuous zeroSobolevPhysicalL2 :=
  torusToPhysicalCubeL2.continuous.comp
    (torusSobolevL2.continuous.comp criticalH0Equiv.continuous)

theorem zeroSobolevPhysicalL2_finite (a : CriticalSobolev 0)
    (hr : SpectralReality (criticalCoeff 0 a)) (N : ℕ) :
    zeroSobolevPhysicalL2 (criticalFiniteSobolev 0 N (criticalCoeff 0 a)) =
      physicalFieldL2 (finiteSynthesis N (criticalCoeff 0 a))
        (finiteSynthesis_contDiff N _).continuous := by
  have heq : torusSobolevL2 (criticalH0Equiv (criticalFiniteSobolev 0 N (criticalCoeff 0 a))) =
      torusPhysicalFieldL2 (finiteSynthesis N (criticalCoeff 0 a))
        (finiteSynthesis_contDiff N _).continuous := by
    apply torusVectorFourierCoeff_injective
    rw [torusSobolevL2_fourierCoeff, criticalH0Equiv_coeff, criticalFiniteSobolev_coeff,
      torusPhysicalFieldL2_fourierCoeff,
      criticalGalerkin_datumFourierCoeff_finiteSynthesis N _ hr]
  unfold zeroSobolevPhysicalL2
  rw [heq]
  exact torusToPhysicalCubeL2_physicalField _ _ (finiteSynthesis_periodic N _)

theorem zeroSobolevPhysicalL2_fourierCoeff (a : CriticalSobolev 0)
    (hr : SpectralReality (criticalCoeff 0 a))
    (hz : SpectralMeanZero (criticalCoeff 0 a)) :
    datumFourierCoeff (zeroSobolevPhysicalL2 a : Field) = criticalCoeff 0 a := by
  have hcut := criticalFiniteSobolev_tendsto 0 a hz
  have hphysical := zeroSobolevPhysicalL2_continuous.continuousAt.tendsto.comp hcut
  funext k i
  have hleft := (criticalCubeFourierFunctional k i).continuous.continuousAt.tendsto.comp hphysical
  have hright := (criticalCoeff_continuous 0 k i).continuousAt.tendsto.comp hcut
  have heq (N : ℕ) : criticalCubeFourierFunctional k i
      (zeroSobolevPhysicalL2 (criticalFiniteSobolev 0 N (criticalCoeff 0 a))) =
      criticalCoeff 0 (criticalFiniteSobolev 0 N (criticalCoeff 0 a)) k i := by
    rw [zeroSobolevPhysicalL2_finite a hr N, criticalCubeFourierFunctional_physicalField,
      criticalGalerkin_datumFourierCoeff_finiteSynthesis N _ hr,
      criticalFiniteSobolev_coeff]
  have hleft' : Tendsto
      (fun N => criticalCoeff 0 (criticalFiniteSobolev 0 N (criticalCoeff 0 a)) k i)
      atTop (𝓝 (datumFourierCoeff (zeroSobolevPhysicalL2 a : Field) k i)) := by
    simpa only [Function.comp_def, heq, criticalCubeFourierFunctional_apply] using hleft
  exact tendsto_nhds_unique hleft' hright

theorem zeroSobolevPhysicalL2_norm (a : CriticalSobolev 0)
    (hr : SpectralReality (criticalCoeff 0 a))
    (hz : SpectralMeanZero (criticalCoeff 0 a)) : ‖zeroSobolevPhysicalL2 a‖ = ‖a‖ := by
  have hback : physicalL2SobolevDatum (zeroSobolevPhysicalL2 a : Field)
      (Lp.memLp _) = a := by
    apply criticalCoeff_injective 0
    rw [physicalL2SobolevDatum_coeff, zeroSobolevPhysicalL2_fourierCoeff a hr hz]
  have h := physicalL2SobolevDatum_norm (zeroSobolevPhysicalL2 a : Field) (Lp.memLp _)
  rw [hback, Lp.toLp_coeFn] at h
  exact h.symm

theorem torusSobolevH0_physical_fourierCoeff (c : TorusSobolev 0)
    (hr : SpectralReality c.val) (hz : SpectralMeanZero c.val) :
    datumFourierCoeff (torusToPhysicalCubeL2 (torusSobolevL2 c) : Field) = c.val := by
  let a : CriticalSobolev 0 := criticalH0Equiv.symm c
  have hc : criticalCoeff 0 a = c.val := by
    simpa only [a, criticalH0Equiv.apply_symm_apply] using (criticalH0Equiv_coeff a).symm
  have har : SpectralReality (criticalCoeff 0 a) := by rw [hc]; exact hr
  have haz : SpectralMeanZero (criticalCoeff 0 a) := by rw [hc]; exact hz
  have h := zeroSobolevPhysicalL2_fourierCoeff a har haz
  simpa only [zeroSobolevPhysicalL2, a, criticalH0Equiv.apply_symm_apply, hc] using h

theorem torusSobolevH0_physical_norm (c : TorusSobolev 0)
    (hr : SpectralReality c.val) (hz : SpectralMeanZero c.val) :
    ‖torusToPhysicalCubeL2 (torusSobolevL2 c)‖ = ‖c‖ := by
  let a : CriticalSobolev 0 := criticalH0Equiv.symm c
  have hc : criticalCoeff 0 a = c.val := by
    simpa only [a, criticalH0Equiv.apply_symm_apply] using (criticalH0Equiv_coeff a).symm
  have har : SpectralReality (criticalCoeff 0 a) := by rw [hc]; exact hr
  have haz : SpectralMeanZero (criticalCoeff 0 a) := by rw [hc]; exact hz
  simpa only [zeroSobolevPhysicalL2, a, criticalH0Equiv.apply_symm_apply,
    criticalH0Equiv.symm.norm_map] using zeroSobolevPhysicalL2_norm a har haz

end QuasiFeffermanB
