import Validation.fixtures.translation_order.ClassicUniServiceInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_jobs
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_higher_or_equal_priority_tasks
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_higher_or_equal_priority_jobs
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_jobs_le_workload
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_jobs_le_delta
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.task_service_of_jobs_received_in
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.task_service_between
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.service_monotonic
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.service_during_cat
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.incremental_service_during
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_jobs_le_1
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.total_service_of_jobs_le_delta
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.low_service_implies_existence_of_idle_time
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_jobs_cat_scheduling_interval
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_jobs_cat_arrival_interval
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.workload_eq_service_impl_all_jobs_have_completed
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.all_jobs_have_completed_impl_workload_eq_service
#check @Prosa.Classic.Model.Schedule.Uni.Service.Service.all_jobs_have_completed_equiv_workload_eq_service
#check @Prosa.Validation.ClassicUniServiceInterface.bigCat_range'
#check @Prosa.Validation.ClassicUniServiceInterface.production_sumSeq_nil
#check @Prosa.Validation.ClassicUniServiceInterface.production_sumSeq_cons
#check @Prosa.Validation.ClassicUniServiceInterface.production_sumFiltered_nil
#check @Prosa.Validation.ClassicUniServiceInterface.production_sumFiltered_cons_true
#check @Prosa.Validation.ClassicUniServiceInterface.production_sumFiltered_cons_false

#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_jobs
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_higher_or_equal_priority_tasks
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_higher_or_equal_priority_jobs
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_jobs_le_workload
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_jobs_le_delta
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.task_service_of_jobs_received_in
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.task_service_between
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.service_monotonic
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.service_during_cat
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.incremental_service_during
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_jobs_le_1
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.total_service_of_jobs_le_delta
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.low_service_implies_existence_of_idle_time
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_jobs_cat_scheduling_interval
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.service_of_jobs_cat_arrival_interval
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.workload_eq_service_impl_all_jobs_have_completed
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.all_jobs_have_completed_impl_workload_eq_service
#print axioms Prosa.Classic.Model.Schedule.Uni.Service.Service.all_jobs_have_completed_equiv_workload_eq_service
#print axioms Prosa.Validation.ClassicUniServiceInterface.bigCat_range'
#print axioms Prosa.Validation.ClassicUniServiceInterface.production_sumSeq_nil
#print axioms Prosa.Validation.ClassicUniServiceInterface.production_sumSeq_cons
#print axioms Prosa.Validation.ClassicUniServiceInterface.production_sumFiltered_nil
#print axioms Prosa.Validation.ClassicUniServiceInterface.production_sumFiltered_cons_true
#print axioms Prosa.Validation.ClassicUniServiceInterface.production_sumFiltered_cons_false
