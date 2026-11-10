import NSE_NOH_Geometry

/-!
# NSE_NOH - exact algebraic 2D3C convection / divergence reduction (FIX8)

A jet consists of velocity and spatial derivative values at ONE point.
Theorems below are elementary algebra over the ACTUAL three-component
velocity and the exact zero-x1 row of its planar gradient lift.

These are not yet the analytic derivative / chain-rule theorems for
actual smooth torus functions.  They cannot, by themselves, construct
2D energy solutions, scalar flows, or the unconditional NSE_NOH root.
No admitted PDE theorem, sorry, or custom axiom. No local Lean execution.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

namespace NSE_NOH

/- Physical velocity components from one passive scalar and one planar velocity. -/
def jetLiftVelocity (w : ℝ) (v : Vector 2) : Vector 3 :=
  ![w, v 0, v 1]

/- The 3x3 Jacobian is zero in x1 and consists of two active planar rows.
   Outer index is derivative direction; inner index is velocity component. -/
def jetLiftSpatialGrad (gradW : Vector 2) (gradV : Fin 2 → Vector 2) :
    Fin 3 → Vector 3 :=
  ![ ![0, 0, 0],
     ![gradW 0, gradV 0 0, gradV 0 1],
     ![gradW 1, gradV 1 0, gradV 1 1] ]

/- Exact vector value of (u dot grad)u for a given jet. -/
def advectionJet (n : ℕ) (a : Vector n) (grad : Fin n → Vector n) : Vector n :=
  fun i => ∑ j : Fin n, a j * grad j i

def divergenceJet (n : ℕ) (grad : Fin n → Vector n) : ℝ :=
  ∑ j : Fin n, grad j j

/- The first three-component equation becomes the passive-scalar advection. -/
theorem advectionJet_lift_scalar
    (w : ℝ) (v gradW : Vector 2) (gradV : Fin 2 → Vector 2) :
    advectionJet 3 (jetLiftVelocity w v) (jetLiftSpatialGrad gradW gradV) 0 =
      v 0 * gradW 0 + v 1 * gradW 1 := by
  simp [advectionJet, jetLiftVelocity, jetLiftSpatialGrad,
    Fin.sum_univ_succ, Fin.sum_univ_two]

/- Planar momentum components have NO passive-scalar convective term. -/
theorem advectionJet_lift_planar_zero
    (w : ℝ) (v gradW : Vector 2) (gradV : Fin 2 → Vector 2) :
    advectionJet 3 (jetLiftVelocity w v) (jetLiftSpatialGrad gradW gradV) 1 =
      v 0 * gradV 0 0 + v 1 * gradV 1 0 := by
  simp [advectionJet, jetLiftVelocity, jetLiftSpatialGrad,
    Fin.sum_univ_succ, Fin.sum_univ_two]

theorem advectionJet_lift_planar_one
    (w : ℝ) (v gradW : Vector 2) (gradV : Fin 2 → Vector 2) :
    advectionJet 3 (jetLiftVelocity w v) (jetLiftSpatialGrad gradW gradV) 2 =
      v 0 * gradV 0 1 + v 1 * gradV 1 1 := by
  simp [advectionJet, jetLiftVelocity, jetLiftSpatialGrad,
    Fin.sum_univ_succ, Fin.sum_univ_two]

/- Three-component incompressibility reduces to planar divergence. -/
theorem divergenceJet_lift (gradW : Vector 2) (gradV : Fin 2 → Vector 2) :
    divergenceJet 3 (jetLiftSpatialGrad gradW gradV) =
      divergenceJet 2 gradV := by
  simp [divergenceJet, jetLiftSpatialGrad,
    Fin.sum_univ_succ, Fin.sum_univ_two]

/- Algebraic PDE at one point, WITHOUT time/space derivative existence claims. -/
def NSEJet (n : ℕ) (ν : ℝ) (a dt : Vector n) (grad : Fin n → Vector n)
    (lap gradPressure : Vector n) : Prop :=
  (∀ i : Fin n, dt i + advectionJet n a grad i + gradPressure i = ν * lap i) ∧
  divergenceJet n grad = 0

/- The exact algebraic reduction from TWO planar momentum equations,
   one passive equation, and planar incompressibility to THREE momentum
   equations and 3D incompressibility, at a fixed positive-time point. -/
theorem NSEJet_lift
    (ν w dtW lapW : ℝ)
    (v dtV lapV gradPressure gradW : Vector 2)
    (gradV : Fin 2 → Vector 2)
    (hPlanar : NSEJet 2 ν v dtV gradV lapV gradPressure)
    (hPassive : dtW + v 0 * gradW 0 + v 1 * gradW 1 = ν * lapW) :
    NSEJet 3 ν (jetLiftVelocity w v) (jetLiftVelocity dtW dtV)
      (jetLiftSpatialGrad gradW gradV)
      (jetLiftVelocity lapW lapV) (jetLiftVelocity 0 gradPressure) := by
  change (∀ i : Fin 2,
    dtV i + advectionJet 2 v gradV i + gradPressure i = ν * lapV i) ∧
    divergenceJet 2 gradV = 0 at hPlanar
  rcases hPlanar with ⟨hMom, hDiv⟩
  change (∀ i : Fin 3,
    jetLiftVelocity dtW dtV i +
      advectionJet 3 (jetLiftVelocity w v) (jetLiftSpatialGrad gradW gradV) i +
      jetLiftVelocity 0 gradPressure i = ν * jetLiftVelocity lapW lapV i) ∧
    divergenceJet 3 (jetLiftSpatialGrad gradW gradV) = 0
  constructor
  · intro i
    fin_cases i
    · -- FIX8: normalize the Fin 3 index and lift components definitionally.
      -- The FIX7 rewrite failed on a residual `((fun i => i) ⟨0, ...⟩)` index.
      change dtW +
        advectionJet 3 (jetLiftVelocity w v) (jetLiftSpatialGrad gradW gradV)
          (0 : Fin 3) + (0 : ℝ) = ν * lapW
      rw [advectionJet_lift_scalar]
      simpa only [add_zero, ← add_assoc] using hPassive
    · change dtV (0 : Fin 2) +
        advectionJet 3 (jetLiftVelocity w v) (jetLiftSpatialGrad gradW gradV)
          (1 : Fin 3) + gradPressure 0 = ν * lapV 0
      rw [advectionJet_lift_planar_zero]
      simpa only [advectionJet, Fin.sum_univ_two] using hMom 0
    · change dtV (1 : Fin 2) +
        advectionJet 3 (jetLiftVelocity w v) (jetLiftSpatialGrad gradW gradV)
          (2 : Fin 3) + gradPressure 1 = ν * lapV 1
      rw [advectionJet_lift_planar_one]
      simpa only [advectionJet, Fin.sum_univ_two] using hMom 1
  · rw [divergenceJet_lift]
    exact hDiv

end NSE_NOH

#print axioms NSE_NOH.advectionJet_lift_scalar
#print axioms NSE_NOH.advectionJet_lift_planar_zero
#print axioms NSE_NOH.advectionJet_lift_planar_one
#print axioms NSE_NOH.divergenceJet_lift
#print axioms NSE_NOH.NSEJet_lift
