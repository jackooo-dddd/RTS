import Prosa.Util.List
import Validation.fixtures.utility_foundation.ListLastComputationInterface

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.filter_in_pred0"
#check @Prosa.Util.List.filter_in_pred0
#eval IO.println "FREEZE_END Prosa.Util.List.filter_in_pred0"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.rem_all"
#check @Prosa.Util.List.rem_all
#eval IO.println "FREEZE_END Prosa.Util.List.rem_all"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.nin_rem_all"
#check @Prosa.Util.List.nin_rem_all
#eval IO.println "FREEZE_END Prosa.Util.List.nin_rem_all"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.in_rem_all"
#check @Prosa.Util.List.in_rem_all
#eval IO.println "FREEZE_END Prosa.Util.List.in_rem_all"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.rem_lt_id"
#check @Prosa.Util.List.rem_lt_id
#eval IO.println "FREEZE_END Prosa.Util.List.rem_lt_id"

#print axioms Prosa.Util.List.filter_in_pred0
#print axioms Prosa.Util.List.rem_all
#print axioms Prosa.Util.List.nin_rem_all
#print axioms Prosa.Util.List.in_rem_all
#print axioms Prosa.Util.List.rem_lt_id
#print axioms Prosa.Validation.ListLastInterface.generic_rem_all_nil
#print axioms Prosa.Validation.ListLastInterface.generic_rem_all_cons
