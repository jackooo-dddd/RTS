import Prosa.Util.List
import Validation.fixtures.utility_foundation.ListLastComputationInterface

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.rem_in"
#check @Prosa.Util.List.rem_in
#eval IO.println "FREEZE_END Prosa.Util.List.rem_in"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.in_neq_impl_rem_in"
#check @Prosa.Util.List.in_neq_impl_rem_in
#eval IO.println "FREEZE_END Prosa.Util.List.in_neq_impl_rem_in"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.filter_size_rem"
#check @Prosa.Util.List.filter_size_rem
#eval IO.println "FREEZE_END Prosa.Util.List.filter_size_rem"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.in_seq_equiv_undup"
#check @Prosa.Util.List.in_seq_equiv_undup
#eval IO.println "FREEZE_END Prosa.Util.List.in_seq_equiv_undup"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.seq1_some"
#check @Prosa.Util.List.seq1_some
#eval IO.println "FREEZE_END Prosa.Util.List.seq1_some"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.seq_elim_last"
#check @Prosa.Util.List.seq_elim_last
#eval IO.println "FREEZE_END Prosa.Util.List.seq_elim_last"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.in_cat"
#check @Prosa.Util.List.in_cat
#eval IO.println "FREEZE_END Prosa.Util.List.in_cat"

#print axioms Prosa.Util.List.rem_in
#print axioms Prosa.Util.List.in_neq_impl_rem_in
#print axioms Prosa.Util.List.filter_size_rem
#print axioms Prosa.Util.List.in_seq_equiv_undup
#print axioms Prosa.Util.List.seq1_some
#print axioms Prosa.Util.List.seq_elim_last
#print axioms Prosa.Util.List.in_cat
#print axioms Prosa.Validation.ListLastInterface.generic_mem_eraseDups
