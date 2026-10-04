import Validation.fixtures.translation_order.ClassicWorkloadInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Schedule.Global.Workload.Workload.service_of_task
#check @Prosa.Classic.Model.Schedule.Global.Workload.Workload.workload
#check @Prosa.Classic.Model.Schedule.Global.Workload.Workload.workload_joblist
#check @Prosa.Classic.Model.Schedule.Global.Workload.Workload.workload_eq_workload_joblist
#check @Prosa.Validation.ClassicWorkloadInterface.bigCatFin_range'
#check @Prosa.Validation.ClassicWorkloadInterface.fin_sum_range'
#check @Prosa.Validation.ClassicWorkloadInterface.bigCat_range'
#check @Prosa.Validation.ClassicWorkloadInterface.service_at_sum
#check @Prosa.Validation.ClassicWorkloadInterface.dedup_nil
#check @Prosa.Validation.ClassicWorkloadInterface.dedup_cons_mem
#check @Prosa.Validation.ClassicWorkloadInterface.dedup_cons_not_mem

#print axioms Prosa.Classic.Model.Schedule.Global.Workload.Workload.service_of_task
#print axioms Prosa.Classic.Model.Schedule.Global.Workload.Workload.workload
#print axioms Prosa.Classic.Model.Schedule.Global.Workload.Workload.workload_joblist
#print axioms Prosa.Classic.Model.Schedule.Global.Workload.Workload.workload_eq_workload_joblist
#print axioms Prosa.Validation.ClassicWorkloadInterface.bigCatFin_range'
#print axioms Prosa.Validation.ClassicWorkloadInterface.fin_sum_range'
#print axioms Prosa.Validation.ClassicWorkloadInterface.bigCat_range'
#print axioms Prosa.Validation.ClassicWorkloadInterface.service_at_sum
#print axioms Prosa.Validation.ClassicWorkloadInterface.dedup_nil
#print axioms Prosa.Validation.ClassicWorkloadInterface.dedup_cons_mem
#print axioms Prosa.Validation.ClassicWorkloadInterface.dedup_cons_not_mem
