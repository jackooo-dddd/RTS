import Prosa.Util.List

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.filter_last_mem"
#check @Prosa.Util.List.filter_last_mem
#eval IO.println "FREEZE_END Prosa.Util.List.filter_last_mem"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.range"
#check @Prosa.Util.List.range
#eval IO.println "FREEZE_END Prosa.Util.List.range"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.iotaD_impl"
#check @Prosa.Util.List.iotaD_impl
#eval IO.println "FREEZE_END Prosa.Util.List.iotaD_impl"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.index_iota_lt_step"
#check @Prosa.Util.List.index_iota_lt_step
#eval IO.println "FREEZE_END Prosa.Util.List.index_iota_lt_step"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.index_iota_cat"
#check @Prosa.Util.List.index_iota_cat
#eval IO.println "FREEZE_END Prosa.Util.List.index_iota_cat"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.range_filter_2cons"
#check @Prosa.Util.List.range_filter_2cons
#eval IO.println "FREEZE_END Prosa.Util.List.range_filter_2cons"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.index_iota_filter_eqx"
#check @Prosa.Util.List.index_iota_filter_eqx
#eval IO.println "FREEZE_END Prosa.Util.List.index_iota_filter_eqx"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.index_iota_filter_singl"
#check @Prosa.Util.List.index_iota_filter_singl
#eval IO.println "FREEZE_END Prosa.Util.List.index_iota_filter_singl"

#eval IO.println "FREEZE_BEGIN Prosa.Util.List.index_iota_filter_inxs"
#check @Prosa.Util.List.index_iota_filter_inxs
#eval IO.println "FREEZE_END Prosa.Util.List.index_iota_filter_inxs"

#print axioms Prosa.Util.List.filter_last_mem
#print axioms Prosa.Util.List.range
#print axioms Prosa.Util.List.iotaD_impl
#print axioms Prosa.Util.List.index_iota_lt_step
#print axioms Prosa.Util.List.index_iota_cat
#print axioms Prosa.Util.List.range_filter_2cons
#print axioms Prosa.Util.List.index_iota_filter_eqx
#print axioms Prosa.Util.List.index_iota_filter_singl
#print axioms Prosa.Util.List.index_iota_filter_inxs
