import Prosa.Util.List

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.last0_cons"
#check @Prosa.Util.List.last0_cons
#eval IO.println "FREEZE_END Prosa.Util.List.last0_cons"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.last0_cat"
#check @Prosa.Util.List.last0_cat
#eval IO.println "FREEZE_END Prosa.Util.List.last0_cat"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.last0_nth"
#check @Prosa.Util.List.last0_nth
#eval IO.println "FREEZE_END Prosa.Util.List.last0_nth"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.last0_ex_cat"
#check @Prosa.Util.List.last0_ex_cat
#eval IO.println "FREEZE_END Prosa.Util.List.last0_ex_cat"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.last0_filter"
#check @Prosa.Util.List.last0_filter
#eval IO.println "FREEZE_END Prosa.Util.List.last0_filter"

#print axioms Prosa.Util.List.last0_cons
#print axioms Prosa.Util.List.last0_cat
#print axioms Prosa.Util.List.last0_nth
#print axioms Prosa.Util.List.last0_ex_cat
#print axioms Prosa.Util.List.last0_filter
