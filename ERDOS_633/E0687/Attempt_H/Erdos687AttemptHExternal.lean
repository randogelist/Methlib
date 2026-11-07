import Bridge687
open Filter Asymptotics
namespace Erdos687AttemptH
theorem erdos_687_part_ii :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =o[atTop]
      (fun x : ℕ => (x : ℝ) ^ 2) :=
  Erdos687.erdos_687.parts.ii
theorem erdos_687_quantitative :
    (fun x : ℕ => (Erdos687.Y x : ℝ)) =O[atTop]
      (fun x : ℕ => (x : ℝ) ^ 2 /
        (Real.log x * Real.log (Real.log x)) ^ 2) :=
  Erdos687.Y_isBigO
end Erdos687AttemptH
