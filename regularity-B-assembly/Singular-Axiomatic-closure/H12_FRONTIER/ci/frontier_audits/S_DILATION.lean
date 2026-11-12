import SingularClosure.H12Frontier.Dilation
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory
open scoped ENNReal Pointwise
namespace SingularClosure.H12Frontier
noncomputable section
example (r : ℝ) (hr : 0 < r) :
    Measure.map (fun x : Vec => r⁻¹ • x) (volume.restrict (dilatedCube r)) =
      ENNReal.ofReal (r ^ 3) • volume.restrict unitCube := map_dilatedCube r hr
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.map_dilatedCube"
#print axioms SingularClosure.H12Frontier.map_dilatedCube
example (r : ℝ) (hr : 0 < r) (f : Vec → Vec) (hf : Continuous f) :
    eLpNorm (dilatedField r f) 3 (volume.restrict (dilatedCube r)) =
      ENNReal.ofReal r * eLpNorm f 3 (volume.restrict unitCube) :=
  dilated_eLpNorm_three r hr f hf
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.dilated_eLpNorm_three"
#print axioms SingularClosure.H12Frontier.dilated_eLpNorm_three
example (r : ℝ) (hr : 0 < r) (f : Vec → Vec) (hf : Continuous f) :
    eLpNorm (dilatedField r f) 6 (volume.restrict (dilatedCube r)) =
      ENNReal.ofReal (Real.sqrt r) * eLpNorm f 6 (volume.restrict unitCube) :=
  dilated_eLpNorm_six r hr f hf
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.dilated_eLpNorm_six"
#print axioms SingularClosure.H12Frontier.dilated_eLpNorm_six
example (r : ℝ) (hr : 0 < r) (f : Vec → Vec) (hf : Continuous f) :
    eLpNorm (dilatedField r f) 2 (volume.restrict (dilatedCube r)) =
      ENNReal.ofReal (r * Real.sqrt r) * eLpNorm f 2 (volume.restrict unitCube) :=
  dilated_eLpNorm_two r hr f hf
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.dilated_eLpNorm_two"
#print axioms SingularClosure.H12Frontier.dilated_eLpNorm_two

example (r : ℝ) (hr : 0 < r) (x : Vec) :
    x ∈ dilatedCube r ↔ ∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ r :=
  mem_dilatedCube_iff r hr x
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.mem_dilatedCube_iff"
#print axioms SingularClosure.H12Frontier.mem_dilatedCube_iff

example (k : Frequency) (x : Vec) :
    fourierCharacter k (paperScale⁻¹ • x) = paperCharacter k x :=
  fourierCharacter_dilated k x
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.fourierCharacter_dilated"
#print axioms SingularClosure.H12Frontier.fourierCharacter_dilated

example (N : ℕ) (c : FourierCoeff) :
    dilatedField paperScale (finiteSynthesis N c) = paperFiniteSynthesis N c :=
  dilatedFiniteSynthesis_eq_paper N c
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.dilatedFiniteSynthesis_eq_paper"
#print axioms SingularClosure.H12Frontier.dilatedFiniteSynthesis_eq_paper
end
end SingularClosure.H12Frontier
