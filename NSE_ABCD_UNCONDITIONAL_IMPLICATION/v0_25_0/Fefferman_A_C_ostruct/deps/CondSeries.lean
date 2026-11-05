import CondPoly
import CondDatum

namespace CondFeffA
open Fefferman.ConcreteReal

/-- Cauchy product of exp(-s) and the convergent geometric series at -s. -/
theorem radial_series_hasSum (s : ℝ) (hs : |s| < 1) :
    HasSum (fun n => CondPoly.radialCoeff n * s ^ n) (Real.exp (-s) / (1+s)) := by
  let f := fun k : ℕ => (-s)^k / (k.factorial : ℝ)
  let g := fun k : ℕ => (-s)^k
  have hf : HasSum f (Real.exp (-s)) := by
    simpa only [f, Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (-s)
  have hg : HasSum g (1+s)⁻¹ := by
    have hneg : ‖-s‖ < 1 := by simpa [Real.norm_eq_abs] using hs
    simpa only [g, sub_neg_eq_add] using hasSum_geometric_of_norm_lt_one hneg
  have hprod := hasSum_sum_range_mul_of_summable_norm hf.summable.norm hg.summable.norm
  rw [hf.tsum_eq, hg.tsum_eq, ← div_eq_mul_inv] at hprod
  have hcoef (n : ℕ) :
      ∑ k ∈ Finset.range (n+1), f k * g (n-k) = CondPoly.radialCoeff n * s^n := by
    calc
      ∑ k ∈ Finset.range (n+1), f k * g (n-k) =
          ∑ k ∈ Finset.range (n+1), (-s)^n * (k.factorial : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
        have hp : (-s)^k * (-s)^(n-k) = (-s)^n := by
          rw [← pow_add, Nat.add_sub_of_le hk']
        dsimp [f, g]
        rw [div_eq_mul_inv, mul_right_comm, hp]
      _ = CondPoly.radialCoeff n * s^n := by
        rw [← Finset.mul_sum]
        simp only [CondPoly.radialCoeff, CondPoly.expPartial,
          show -s = (-1 : ℝ) * s by ring, mul_pow]
        ring
  simpa only [hcoef] using hprod

theorem radial_hasFPowerSeriesAt :
    HasFPowerSeriesAt (fun s : ℝ => Real.exp (-s) / (1+s))
      (FormalMultilinearSeries.ofScalars ℝ CondPoly.radialCoeff) 0 := by
  let p := FormalMultilinearSeries.ofScalars ℝ CondPoly.radialCoeff
  have hcoeff (n : ℕ) : |CondPoly.radialCoeff n| ≤ Real.exp 1 := by
    have h0 : 0 ≤ CondPoly.expPartial n := by unfold CondPoly.expPartial; positivity
    have hle : CondPoly.expPartial n ≤ Real.exp 1 := by
      simpa [CondPoly.expPartial, one_div] using
        Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) (n+1)
    simpa [CondPoly.radialCoeff, abs_mul, abs_pow, abs_of_nonneg h0] using hle
  have hr := p.le_radius_of_bound (Real.exp 1) (r := (1 : NNReal)) (fun n => by
    simpa [p, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs] using hcoeff n)
  refine ⟨1, ?_, by norm_num, ?_⟩
  · simpa using hr
  · intro s hs
    have hd : edist s 0 < ENNReal.ofReal 1 := by
      change edist s 0 < 1 at hs
      simpa using hs
    have hlt : |s| < 1 := by simpa [Real.dist_eq] using edist_lt_ofReal.mp hd
    simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
      radial_series_hasSum s hlt

theorem psi_radial_hasSum (x : RSpace) (hx : |normSq3 x| < 1) :
    HasSum (fun n => CondPoly.radialCoeff n * normSq3 x ^ n) (psi x) :=
  radial_series_hasSum (normSq3 x) hx

end CondFeffA
