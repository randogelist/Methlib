import QuasiFeffermanB.CaloricPhysicalControl
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.caloric_fourierCharacter_norm"
#check @QuasiFeffermanB.caloric_fourierCharacter_norm
#eval IO.println "TYPE_END:QuasiFeffermanB.caloric_fourierCharacter_norm"
#print axioms QuasiFeffermanB.caloric_fourierCharacter_norm

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.FINITE_SYNTHESIS_NORM_LE_CHI0"
#check @QuasiFeffermanB.FINITE_SYNTHESIS_NORM_LE_CHI0
#eval IO.println "TYPE_END:QuasiFeffermanB.FINITE_SYNTHESIS_NORM_LE_CHI0"
#print axioms QuasiFeffermanB.FINITE_SYNTHESIS_NORM_LE_CHI0

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.CONVECTION_NORM_SQ_LE_GRADIENT_DENSITY"
#check @QuasiFeffermanB.CONVECTION_NORM_SQ_LE_GRADIENT_DENSITY
#eval IO.println "TYPE_END:QuasiFeffermanB.CONVECTION_NORM_SQ_LE_GRADIENT_DENSITY"
#print axioms QuasiFeffermanB.CONVECTION_NORM_SQ_LE_GRADIENT_DENSITY

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.PHYSICAL_PAIRING_SQUARE_LE_ENERGY_PRODUCT"
#check @QuasiFeffermanB.PHYSICAL_PAIRING_SQUARE_LE_ENERGY_PRODUCT
#eval IO.println "TYPE_END:QuasiFeffermanB.PHYSICAL_PAIRING_SQUARE_LE_ENERGY_PRODUCT"
#print axioms QuasiFeffermanB.PHYSICAL_PAIRING_SQUARE_LE_ENERGY_PRODUCT

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.FINITE_CONVECTION_ENERGY_LE_CHI0"
#check @QuasiFeffermanB.FINITE_CONVECTION_ENERGY_LE_CHI0
#eval IO.println "TYPE_END:QuasiFeffermanB.FINITE_CONVECTION_ENERGY_LE_CHI0"
#print axioms QuasiFeffermanB.FINITE_CONVECTION_ENERGY_LE_CHI0

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.FINITE_ENSTROPHY_TRANSPORT_SQUARE_LE_CHI0"
#check @QuasiFeffermanB.FINITE_ENSTROPHY_TRANSPORT_SQUARE_LE_CHI0
#eval IO.println "TYPE_END:QuasiFeffermanB.FINITE_ENSTROPHY_TRANSPORT_SQUARE_LE_CHI0"
#print axioms QuasiFeffermanB.FINITE_ENSTROPHY_TRANSPORT_SQUARE_LE_CHI0

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.GALERKIN_CHI0_CONTINUOUS"
#check @QuasiFeffermanB.GALERKIN_CHI0_CONTINUOUS
#eval IO.println "TYPE_END:QuasiFeffermanB.GALERKIN_CHI0_CONTINUOUS"
#print axioms QuasiFeffermanB.GALERKIN_CHI0_CONTINUOUS

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.GALERKIN_H1_INITIAL_ENSTROPHY_BOUND"
#check @QuasiFeffermanB.GALERKIN_H1_INITIAL_ENSTROPHY_BOUND
#eval IO.println "TYPE_END:QuasiFeffermanB.GALERKIN_H1_INITIAL_ENSTROPHY_BOUND"
#print axioms QuasiFeffermanB.GALERKIN_H1_INITIAL_ENSTROPHY_BOUND

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.CALORIC_H1_GALERKIN_ENSTROPHY_ACCUMULATION"
#check @QuasiFeffermanB.CALORIC_H1_GALERKIN_ENSTROPHY_ACCUMULATION
#eval IO.println "TYPE_END:QuasiFeffermanB.CALORIC_H1_GALERKIN_ENSTROPHY_ACCUMULATION"
#print axioms QuasiFeffermanB.CALORIC_H1_GALERKIN_ENSTROPHY_ACCUMULATION
