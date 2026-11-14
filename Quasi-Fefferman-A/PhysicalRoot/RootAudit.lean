import QUASI_FEFFERMAN_A

set_option pp.universes false
set_option pp.explicit true
set_option pp.fullNames true

#eval IO.println "TYPE_BEGIN:QFA.PhysicalRoot.selectedTail_restricted_singleton"
#check @QFA.PhysicalRoot.selectedTail_restricted_singleton
#eval IO.println "TYPE_END:QFA.PhysicalRoot.selectedTail_restricted_singleton"
#print axioms QFA.PhysicalRoot.selectedTail_restricted_singleton

#eval IO.println "TYPE_BEGIN:QFA.PhysicalRoot.selectedTail_smooth"
#check @QFA.PhysicalRoot.selectedTail_smooth
#eval IO.println "TYPE_END:QFA.PhysicalRoot.selectedTail_smooth"
#print axioms QFA.PhysicalRoot.selectedTail_smooth

#eval IO.println "TYPE_BEGIN:QFA.PhysicalRoot.selectedTail_root_conclusion"
#check @QFA.PhysicalRoot.selectedTail_root_conclusion
#eval IO.println "TYPE_END:QFA.PhysicalRoot.selectedTail_root_conclusion"
#print axioms QFA.PhysicalRoot.selectedTail_root_conclusion

#eval IO.println "TYPE_BEGIN:QFA.PhysicalRoot.QUASI_FEFFERMAN_A"
#check @QFA.PhysicalRoot.QUASI_FEFFERMAN_A
#eval IO.println "TYPE_END:QFA.PhysicalRoot.QUASI_FEFFERMAN_A"
#print axioms QFA.PhysicalRoot.QUASI_FEFFERMAN_A
