import QFALC001Reduction

set_option pp.universes false
set_option pp.explicit true
set_option pp.fullNames true

#eval IO.println "TYPE_BEGIN:QFA.LC001SpectralReduction.integrable_norm_sq"
#check @QFA.LC001SpectralReduction.integrable_norm_sq
#eval IO.println "TYPE_END:QFA.LC001SpectralReduction.integrable_norm_sq"
#print axioms QFA.LC001SpectralReduction.integrable_norm_sq

#eval IO.println "TYPE_BEGIN:QFA.LC001SpectralReduction.integral_norm_sq_eq_norm_sq"
#check @QFA.LC001SpectralReduction.integral_norm_sq_eq_norm_sq
#eval IO.println "TYPE_END:QFA.LC001SpectralReduction.integral_norm_sq_eq_norm_sq"
#print axioms QFA.LC001SpectralReduction.integral_norm_sq_eq_norm_sq

#eval IO.println "TYPE_BEGIN:QFA.LC001SpectralReduction.integrable_gradient_fourier_sum"
#check @QFA.LC001SpectralReduction.integrable_gradient_fourier_sum
#eval IO.println "TYPE_END:QFA.LC001SpectralReduction.integrable_gradient_fourier_sum"
#print axioms QFA.LC001SpectralReduction.integrable_gradient_fourier_sum

#eval IO.println "TYPE_BEGIN:QFA.LC001SpectralReduction.integral_gradient_fourier_sum"
#check @QFA.LC001SpectralReduction.integral_gradient_fourier_sum
#eval IO.println "TYPE_END:QFA.LC001SpectralReduction.integral_gradient_fourier_sum"
#print axioms QFA.LC001SpectralReduction.integral_gradient_fourier_sum

#eval IO.println "TYPE_BEGIN:QFA.LC001SpectralReduction.nativeSpectralRealization_of_fourierNormAE"
#check @QFA.LC001SpectralReduction.nativeSpectralRealization_of_fourierNormAE
#eval IO.println "TYPE_END:QFA.LC001SpectralReduction.nativeSpectralRealization_of_fourierNormAE"
#print axioms QFA.LC001SpectralReduction.nativeSpectralRealization_of_fourierNormAE

#eval IO.println "TYPE_BEGIN:QFA.LC001SpectralReduction.fourierNormAEToNativeSpectralEndpoint"
#check @QFA.LC001SpectralReduction.fourierNormAEToNativeSpectralEndpoint
#eval IO.println "TYPE_END:QFA.LC001SpectralReduction.fourierNormAEToNativeSpectralEndpoint"
#print axioms QFA.LC001SpectralReduction.fourierNormAEToNativeSpectralEndpoint
