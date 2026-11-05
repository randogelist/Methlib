import CondDatum

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal
open Polynomial
noncomputable section

/-- Componentwise spatial Laplacian for the viscosity-one heat term. -/
def heatStep (v : RInitial) : RInitial :=
  fun x i => laplacian realAnalysis (fun y => v y i) x

/-- Positive Newton potential, the formal inverse of -Δ on the whole space. -/
def newtonPotential (g : RSpace → ℝ) (x : RSpace) : ℝ :=
  ∫ y : RSpace, g y / (4 * Real.pi * euclideanNorm3 (x - y))

def fieldDiv (v : RInitial) (x : RSpace) : ℝ :=
  sum3 realAnalysis (fun i => spatialDerivative i (fun y => v y i) x)

def transport (v w : RInitial) (x : RSpace) (i : Fin 3) : ℝ :=
  sum3 realAnalysis (fun j => v x j * spatialDerivative j (fun y => w y i) x)

/-- The chosen whole-space formula P F = F + grad (-Δ)⁻¹ div F.
Its identification with the pressure-normalized NSE jets is an input at the root. -/
def projectedTransport (v w : RInitial) : RInitial :=
  let F := transport v w
  fun x i => F x i + spatialDerivative i (newtonPotential (fieldDiv F)) x

abbrev JetTable := ℕ → ℕ → RInitial

/-- At time order n, row index k represents amplitude degree k+1.
For degree k+2 the transport convolution has index pairs (l,k-l). -/
def nextRow (n : ℕ) (T : JetTable) : ℕ → RInitial
  | 0 => heatStep (T n 0)
  | k+1 => fun x i =>
      heatStep (T n (k+1)) x i -
        ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
          ∑ l ∈ Finset.range (k+1),
            projectedTransport (T j l) (T (n-j) (k-l)) x i

/-- Finite diagonal construction. Each step adds the next time row;
all earlier rows are retained. The initial time jet is c times the profile. -/
def jetTable : ℕ → JetTable
  | 0 => fun _ k => if k = 0 then profile else 0
  | n+1 => fun j k => if j = n+1 then
      (if k ≤ n+1 then nextRow n (jetTable n) k else 0) else jetTable n j k

def heatIterate : ℕ → RInitial
  | 0 => profile
  | n+1 => heatStep (heatIterate n)

theorem first_mode_eq_heat (n : ℕ) : jetTable n n 0 = heatIterate n := by
  induction n with
  | zero => simp [jetTable, heatIterate]
  | succ n ih =>
    simpa only [jetTable, if_pos rfl, Nat.zero_le, if_true, nextRow, heatIterate]
      using (congrArg heatStep ih)

/-- At (x,i)=(0,0), the n-th physical right time derivative is to be
identified with evaluation of this explicit polynomial at amplitude c. -/
def jetPolynomial (n : ℕ) : Polynomial ℝ :=
  monomial 1 (jetTable n n 0 0 0) +
    ∑ k ∈ Finset.range n, monomial (k+2) (jetTable n n (k+1) 0 0)

/-- The zeroth time jet is exactly the initial velocity at the sampled position. -/
theorem jetPolynomial_initial (c : ℝ) : (jetPolynomial 0).eval c = datum c 0 0 := by
  simp [jetPolynomial, jetTable, datum, Polynomial.eval_monomial, mul_comm]

theorem jetPolynomial_eval (n : ℕ) (c : ℝ) :
    (jetPolynomial n).eval c = jetTable n n 0 0 0 * c +
      ∑ k ∈ Finset.range n, jetTable n n (k+1) 0 0 * c^(k+2) := by
  simp only [jetPolynomial, Polynomial.eval_add, Polynomial.eval_monomial,
    Polynomial.eval_finsetSum, pow_one]

theorem jetPolynomial_linear (n : ℕ) :
    (jetPolynomial n).coeff 1 = heatIterate n 0 0 := by
  have hn (k : ℕ) : k+2 ≠ 1 := by omega
  simp [jetPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    hn, first_mode_eq_heat]

theorem jetPolynomial_degree (n : ℕ) : (jetPolynomial n).natDegree ≤ n+1 := by
  unfold jetPolynomial
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (Polynomial.natDegree_monomial_le _).trans (by omega)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    exact (Polynomial.natDegree_monomial_le _).trans (by omega)

end
end CondFeffA
