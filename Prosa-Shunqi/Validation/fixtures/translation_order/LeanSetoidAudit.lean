import Prosa.Util.Setoid

#eval IO.println "FREEZE_BEGIN Prosa.Util.Setoid.leb"
#check @Prosa.Util.Setoid.leb
#print Prosa.Util.Setoid.leb
#eval IO.println "FREEZE_END Prosa.Util.Setoid.leb"

#eval IO.println "FREEZE_BEGIN Prosa.Util.Setoid.leb_eq"
#check @Prosa.Util.Setoid.leb_eq
#eval IO.println "FREEZE_END Prosa.Util.Setoid.leb_eq"

#eval IO.println "FREEZE_BEGIN Prosa.Util.Setoid.leqRW"
#check @Prosa.Util.Setoid.leqRW
#print Prosa.Util.Setoid.leqRW
#eval IO.println "FREEZE_END Prosa.Util.Setoid.leqRW"

#print axioms Prosa.Util.Setoid.leb_eq
#print axioms Prosa.Util.Setoid.leqRW
#print axioms Prosa.Util.Setoid.leb
