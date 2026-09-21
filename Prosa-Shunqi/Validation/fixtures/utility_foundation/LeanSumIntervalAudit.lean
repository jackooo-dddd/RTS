import Prosa.Util.Sum

#eval IO.println "FREEZE_BEGIN Prosa.Util.Sum.sum_of_ones"
#check @Prosa.Util.Sum.sum_of_ones
#print Prosa.Util.Sum.sum_of_ones
#eval IO.println "FREEZE_END Prosa.Util.Sum.sum_of_ones"

#eval IO.println "FREEZE_BEGIN Prosa.Util.Sum.big_nat_eq0"
#check @Prosa.Util.Sum.big_nat_eq0
#print Prosa.Util.Sum.big_nat_eq0
#eval IO.println "FREEZE_END Prosa.Util.Sum.big_nat_eq0"

#eval IO.println "FREEZE_BEGIN Prosa.Util.Sum.sum_le_summation_range"
#check @Prosa.Util.Sum.sum_le_summation_range
#print Prosa.Util.Sum.sum_le_summation_range
#eval IO.println "FREEZE_END Prosa.Util.Sum.sum_le_summation_range"

#print axioms Prosa.Util.Sum.sum_of_ones
#print axioms Prosa.Util.Sum.big_nat_eq0
#print axioms Prosa.Util.Sum.sum_le_summation_range
