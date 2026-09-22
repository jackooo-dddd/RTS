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

#eval IO.println "FREEZE_BEGIN Prosa.Util.Sum.big_sum_eq_in_eq_sized_intervals"
#check @Prosa.Util.Sum.big_sum_eq_in_eq_sized_intervals
#print Prosa.Util.Sum.big_sum_eq_in_eq_sized_intervals
#eval IO.println "FREEZE_END Prosa.Util.Sum.big_sum_eq_in_eq_sized_intervals"

#eval IO.println "FREEZE_BEGIN Prosa.Util.Sum.pigeonhole_on_interval"
#check @Prosa.Util.Sum.pigeonhole_on_interval
#print Prosa.Util.Sum.pigeonhole_on_interval
#eval IO.println "FREEZE_END Prosa.Util.Sum.pigeonhole_on_interval"

#eval IO.println "FREEZE_BEGIN Prosa.Util.Sum.sum_ge_2_nat"
#check @Prosa.Util.Sum.sum_ge_2_nat
#print Prosa.Util.Sum.sum_ge_2_nat
#eval IO.println "FREEZE_END Prosa.Util.Sum.sum_ge_2_nat"

#print axioms Prosa.Util.Sum.sum_of_ones
#print axioms Prosa.Util.Sum.big_nat_eq0
#print axioms Prosa.Util.Sum.sum_le_summation_range
#print axioms Prosa.Util.Sum.big_sum_eq_in_eq_sized_intervals
#print axioms Prosa.Util.Sum.pigeonhole_on_interval
#print axioms Prosa.Util.Sum.sum_ge_2_nat
