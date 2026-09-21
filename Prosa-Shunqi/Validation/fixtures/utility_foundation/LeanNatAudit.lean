import Prosa.Util.Nat

#eval IO.println "FREEZE_BEGIN Prosa.Util.Nat.subnACA"
#check @Prosa.Util.Nat.subnACA
#eval IO.println "FREEZE_END Prosa.Util.Nat.subnACA"

#eval IO.println "FREEZE_BEGIN Prosa.Util.Nat.leq_subRL_impl"
#check @Prosa.Util.Nat.leq_subRL_impl
#eval IO.println "FREEZE_END Prosa.Util.Nat.leq_subRL_impl"

#print axioms Prosa.Util.Nat.subnACA
#print axioms Prosa.Util.Nat.leq_subRL_impl
