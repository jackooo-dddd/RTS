import Prosa.Util.UnitGrowth

#eval IO.println "FREEZE_BEGIN Prosa.Util.UnitGrowth.unit_growth_function"
#check @Prosa.Util.UnitGrowth.unit_growth_function
#print Prosa.Util.UnitGrowth.unit_growth_function
#eval IO.println "FREEZE_END Prosa.Util.UnitGrowth.unit_growth_function"

#eval IO.println "FREEZE_BEGIN Prosa.Util.UnitGrowth.unit_growth_function_k_steps_bounded"
#check @Prosa.Util.UnitGrowth.unit_growth_function_k_steps_bounded
#eval IO.println "FREEZE_END Prosa.Util.UnitGrowth.unit_growth_function_k_steps_bounded"

#eval IO.println "FREEZE_BEGIN Prosa.Util.UnitGrowth.exists_intermediate_point"
#check @Prosa.Util.UnitGrowth.exists_intermediate_point
#eval IO.println "FREEZE_END Prosa.Util.UnitGrowth.exists_intermediate_point"

#eval IO.println "FREEZE_BEGIN Prosa.Util.UnitGrowth.exists_intermediate_point_leq"
#check @Prosa.Util.UnitGrowth.exists_intermediate_point_leq
#eval IO.println "FREEZE_END Prosa.Util.UnitGrowth.exists_intermediate_point_leq"

#eval IO.println "FREEZE_BEGIN Prosa.Util.UnitGrowth.exists_first_intermediate_point"
#check @Prosa.Util.UnitGrowth.exists_first_intermediate_point
#eval IO.println "FREEZE_END Prosa.Util.UnitGrowth.exists_first_intermediate_point"

#eval IO.println "FREEZE_BEGIN Prosa.Util.UnitGrowth.slowed"
#check @Prosa.Util.UnitGrowth.slowed
#print Prosa.Util.UnitGrowth.slowed
#eval IO.println "FREEZE_END Prosa.Util.UnitGrowth.slowed"

#eval IO.println "FREEZE_BEGIN Prosa.Util.UnitGrowth.slowed_respects_pointwise_leq"
#check @Prosa.Util.UnitGrowth.slowed_respects_pointwise_leq
#eval IO.println "FREEZE_END Prosa.Util.UnitGrowth.slowed_respects_pointwise_leq"

#eval IO.println "FREEZE_BEGIN Prosa.Util.UnitGrowth.slowed_is_unit_step"
#check @Prosa.Util.UnitGrowth.slowed_is_unit_step
#eval IO.println "FREEZE_END Prosa.Util.UnitGrowth.slowed_is_unit_step"

#eval IO.println "FREEZE_BEGIN Prosa.Util.UnitGrowth.slowed_respects_monotone"
#check @Prosa.Util.UnitGrowth.slowed_respects_monotone
#eval IO.println "FREEZE_END Prosa.Util.UnitGrowth.slowed_respects_monotone"

#eval IO.println "FREEZE_BEGIN Prosa.Util.UnitGrowth.slowed_never_exceeds"
#check @Prosa.Util.UnitGrowth.slowed_never_exceeds
#eval IO.println "FREEZE_END Prosa.Util.UnitGrowth.slowed_never_exceeds"

#eval IO.println "FREEZE_BEGIN Prosa.Util.UnitGrowth.bound_preserved_under_slowed"
#check @Prosa.Util.UnitGrowth.bound_preserved_under_slowed
#eval IO.println "FREEZE_END Prosa.Util.UnitGrowth.bound_preserved_under_slowed"

#eval IO.println "FREEZE_BEGIN Prosa.Util.UnitGrowth.slowed_subtraction_value_preservation"
#check @Prosa.Util.UnitGrowth.slowed_subtraction_value_preservation
#eval IO.println "FREEZE_END Prosa.Util.UnitGrowth.slowed_subtraction_value_preservation"

#print axioms Prosa.Util.UnitGrowth.unit_growth_function
#print axioms Prosa.Util.UnitGrowth.unit_growth_function_k_steps_bounded
#print axioms Prosa.Util.UnitGrowth.exists_intermediate_point
#print axioms Prosa.Util.UnitGrowth.exists_intermediate_point_leq
#print axioms Prosa.Util.UnitGrowth.exists_first_intermediate_point
#print axioms Prosa.Util.UnitGrowth.slowed
#print axioms Prosa.Util.UnitGrowth.slowed_respects_pointwise_leq
#print axioms Prosa.Util.UnitGrowth.slowed_is_unit_step
#print axioms Prosa.Util.UnitGrowth.slowed_respects_monotone
#print axioms Prosa.Util.UnitGrowth.slowed_never_exceeds
#print axioms Prosa.Util.UnitGrowth.bound_preserved_under_slowed
#print axioms Prosa.Util.UnitGrowth.slowed_subtraction_value_preservation

#check @Prosa.Util.UnitGrowth.slowed.eq_1
#check @Prosa.Util.UnitGrowth.slowed.eq_2
#print axioms Prosa.Util.UnitGrowth.slowed.eq_1
#print axioms Prosa.Util.UnitGrowth.slowed.eq_2
