import CondRaw

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal Set
noncomputable section

private abbrev ZM := RSpace × ℝ
private abbrev S : Set ZM := {z | 0 ≤ z.2}
private abbrev et : ZM := (0,1)

private def dir (v : ZM) (F : ZM → ℝ) (z : ZM) : ℝ := fderivWithin ℝ F S z v

private theorem dir_smooth {F : ZM → ℝ} (hF : ContDiffOn ℝ ⊤ F S) (v : ZM) :
    ContDiffOn ℝ ⊤ (dir v F) S := by
  have hdf : ContDiffOn ℝ ⊤ (fderivWithin ℝ F S) S :=
    hF.fderivWithin raw_uniqueDiffOn le_top
  exact hdf.clm_apply (g := fun _ => v) contDiffOn_const

private theorem dir_congr {F G : ZM → ℝ} (h : EqOn F G S) (v : ZM) :
    EqOn (dir v F) (dir v G) S := by
  intro z hz
  unfold dir
  rw [fderivWithin_congr' h hz]

private theorem dir_two {F : ZM → ℝ} (hF : ContDiffOn ℝ ⊤ F S)
    (v w : ZM) (z : ZM) (hz : z ∈ S) :
    dir v (dir w F) z = fderivWithin ℝ (fderivWithin ℝ F S) S z v w := by
  have hdf : ContDiffOn ℝ ⊤ (fderivWithin ℝ F S) S :=
    hF.fderivWithin raw_uniqueDiffOn le_top
  unfold dir
  rw [fderivWithin_clm_apply (c := fderivWithin ℝ F S) (u := fun _ : ZM => w)
    (raw_uniqueDiffOn z hz) (hdf.differentiableOn (by simp) z hz) (by fun_prop)]
  simp

private theorem dir_swap {F : ZM → ℝ} (hF : ContDiffOn ℝ ⊤ F S) (v w : ZM) :
    EqOn (dir v (dir w F)) (dir w (dir v F)) S := by
  intro z hz
  rw [dir_two hF v w z hz, dir_two hF w v z hz]
  exact (hF z hz).isSymmSndFDerivWithinAt_of_omega raw_uniqueDiffOn hz v w

private def Dt : ℕ → (ZM → ℝ) → ZM → ℝ
  | 0, F => F
  | n+1, F => dir et (Dt n F)

private theorem dt_smooth {F : ZM → ℝ} (hF : ContDiffOn ℝ ⊤ F S) (n : ℕ) :
    ContDiffOn ℝ ⊤ (Dt n F) S := by
  induction n with
  | zero => exact hF
  | succ n ih => exact dir_smooth ih et

private theorem dt_swap {F : ZM → ℝ} (hF : ContDiffOn ℝ ⊤ F S) (v : ZM) (n : ℕ) :
    EqOn (Dt n (dir v F)) (dir v (Dt n F)) S := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    exact (dir_congr ih et).trans (dir_swap (dt_smooth hF n) et v)

private theorem slice_deriv {F : ZM → ℝ} (hF : ContDiffOn ℝ ⊤ F S)
    (x : RSpace) (t : ℝ) (ht : 0 ≤ t) :
    derivWithin (fun r : ℝ => F (x,r)) (Ici 0) t = dir et F (x,t) := by
  let L : ℝ → ZM := fun r => (x,r)
  have hL : HasDerivWithinAt L et (Ici 0) t :=
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t)).hasDerivWithinAt
  have hP := (hF.differentiableOn (by simp) (x,t) ht).hasFDerivWithinAt
  have h := hP.comp_hasDerivWithinAt (f := L) t hL (fun _ hr => hr)
  exact h.derivWithin (uniqueDiffOn_Ici 0 t ht)

private theorem slice_iter {F : ZM → ℝ} (hF : ContDiffOn ℝ ⊤ F S) (n : ℕ)
    (x : RSpace) (t : ℝ) (ht : 0 ≤ t) :
    iteratedDerivWithin n (fun r => F (x,r)) (Ici 0) t = Dt n F (x,t) := by
  induction n generalizing t with
  | zero => simp [Dt]
  | succ n ih =>
    rw [iteratedDerivWithin_succ]
    calc
      _ = derivWithin (fun r => Dt n F (x,r)) (Ici 0) t :=
        derivWithin_congr (fun r hr => ih r hr) (ih t ht)
      _ = _ := slice_deriv (dt_smooth hF n) x t ht

/-- The spatial derivative of an order-n right time jet agrees with the right
time jet of the spatial derivative, including at the initial face. -/
theorem raw_space_time_commute {F : RSpace × ℝ → ℝ}
    (hF : ContDiffOn ℝ ⊤ F {z | 0 ≤ z.2}) (i : Fin 3) (n : ℕ) (x : RSpace) :
    rightJet (fun t => spatialDerivative i (fun y => F (y,t)) x) n =
      spatialDerivative i (fun y => rightJet (fun t => F (y,t)) n) x := by
  let v : ZM := (basisDirection i, 0)
  have hx : EqOn (fun t => spatialDerivative i (fun y => F (y,t)) x)
      (fun t => dir v F (x,t)) (Ici 0) :=
    fun t ht => raw_space_deriv_within_eq hF i (x,t) ht
  have hj : (fun y => rightJet (fun t => F (y,t)) n) = fun y => Dt n F (y,0) :=
    funext fun y => slice_iter hF n y 0 le_rfl
  rw [hj]
  calc
    _ = iteratedDerivWithin n (fun t => dir v F (x,t)) (Ici 0) 0 :=
      iteratedDerivWithin_congr hx (Set.self_mem_Ici : (0 : ℝ) ∈ Set.Ici 0)
    _ = Dt n (dir v F) (x,0) := slice_iter (dir_smooth hF v) n x 0 le_rfl
    _ = dir v (Dt n F) (x,0) := dt_swap hF v n (by change (0 : ℝ) ≤ 0; exact le_refl 0)
    _ = _ := (raw_space_deriv_within_eq (dt_smooth hF n) i (x,0) (by change (0 : ℝ) ≤ 0; exact le_refl 0)).symm

end
end CondFeffA

#print axioms CondFeffA.raw_space_time_commute
