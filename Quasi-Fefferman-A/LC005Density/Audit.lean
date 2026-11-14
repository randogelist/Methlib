import QFALC005

set_option pp.universes false
set_option pp.explicit true
set_option pp.fullNames true

#eval IO.println "TYPE_BEGIN:SchwartzMap.qfa_dense_hasCompactSupport"
#check @SchwartzMap.qfa_dense_hasCompactSupport
#eval IO.println "TYPE_END:SchwartzMap.qfa_dense_hasCompactSupport"
#print axioms SchwartzMap.qfa_dense_hasCompactSupport

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.denseCompactSchwartzTests"
#check @QFA.Endpoints.Representation.CompactSchwartz.denseCompactSchwartzTests
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.CompactSchwartz.denseCompactSchwartzTests"
#print axioms QFA.Endpoints.Representation.CompactSchwartz.denseCompactSchwartzTests

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz_unconditional"
#check @QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz_unconditional
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz_unconditional"
#print axioms QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz_unconditional

#eval IO.println "TYPE_BEGIN:QFA.Endpoints.Representation.CompactSchwartz.compactSchwartzToSchwartzEndpoint"
#check @QFA.Endpoints.Representation.CompactSchwartz.compactSchwartzToSchwartzEndpoint
#eval IO.println "TYPE_END:QFA.Endpoints.Representation.CompactSchwartz.compactSchwartzToSchwartzEndpoint"
#print axioms QFA.Endpoints.Representation.CompactSchwartz.compactSchwartzToSchwartzEndpoint
