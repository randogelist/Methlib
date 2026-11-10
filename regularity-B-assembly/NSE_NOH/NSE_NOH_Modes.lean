import NSE_NOH_Geometry

/-!
# NSE_NOH - exact rank-two Fourier lattice and triad closure

Purely algebraic results for the subgroup of Fourier frequencies with k_1=0.
Does NOT establish an L² Fourier-support theorem, distributional invariance,
NSE existence, or positive-time smoothness.  No new axioms or sorry.
Prepared for native cached Windows Lean 4.33.0; not run locally.
FIX7: interpret subgroup-membership hypotheses as pointwise equalities before simp.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

namespace NSE_NOH

/- The exact subgroup of three-dimensional integer modes satisfying k_1=0. -/
def X1ZeroModes : AddSubgroup (Fin 3 → ℤ) where
  carrier := {k | k 0 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro a b ha hb
    -- Membership must be unfolded in the hypotheses, not only in the goal.
    change a 0 = 0 at ha
    change b 0 = 0 at hb
    change (a + b) 0 = 0
    simpa only [Pi.add_apply, ha, hb, zero_add]
  neg_mem' := by
    intro a ha
    change a 0 = 0 at ha
    change (-a) 0 = 0
    simpa only [Pi.neg_apply, ha, neg_zero]

/- The existing modeEmbedding2 is a homomorphism of additive mode groups. -/
theorem modeEmbedding2_add (p q : Fin 2 → ℤ) :
    modeEmbedding2 (p + q) = modeEmbedding2 p + modeEmbedding2 q := by
  funext i
  fin_cases i <;> simp [modeEmbedding2, Pi.add_apply]

theorem modeEmbedding2_neg (p : Fin 2 → ℤ) :
    modeEmbedding2 (-p) = -modeEmbedding2 p := by
  funext i
  fin_cases i <;> simp [modeEmbedding2, Pi.neg_apply]

/- Exact additive group equivalence, not just a bare set bijection. -/
def planarModesAddEquiv : (Fin 2 → ℤ) ≃+ X1ZeroModes where
  toFun k := ⟨modeEmbedding2 k, rfl⟩
  invFun k := modeProjection2 k.1
  left_inv k := modeProjection2_modeEmbedding2 k
  right_inv k := by
    apply Subtype.ext
    exact modeEmbedding2_modeProjection2 k.1 k.2
  map_add' := by
    intro p q
    apply Subtype.ext
    exact modeEmbedding2_add p q

/- The 2D3C Fourier plane is closed under frequency addition. -/
theorem x1zero_triad_closed (p q : Fin 3 → ℤ)
    (hp : p 0 = 0) (hq : q 0 = 0) :
    (p + q) 0 = 0 := by
  simp [Pi.add_apply, hp, hq]

theorem x1zero_triad_target (p q k : Fin 3 → ℤ)
    (hp : p 0 = 0) (hq : q 0 = 0)
    (htriad : p + q = k) : k 0 = 0 := by
  rw [← htriad]
  exact x1zero_triad_closed p q hp hq

end NSE_NOH

#check NSE_NOH.X1ZeroModes
#check NSE_NOH.planarModesAddEquiv
#print axioms NSE_NOH.modeEmbedding2_add
#print axioms NSE_NOH.planarModesAddEquiv
#print axioms NSE_NOH.x1zero_triad_target
