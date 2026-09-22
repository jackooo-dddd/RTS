import Validation.fixtures.translation_order.ServiceComputationInterface

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Service.scheduled_at"
#check @Prosa.Behavior.Service.scheduled_at
#eval IO.println "FREEZE_END Prosa.Behavior.Service.scheduled_at"
#print axioms Prosa.Behavior.Service.scheduled_at

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Service.service_at"
#check @Prosa.Behavior.Service.service_at
#eval IO.println "FREEZE_END Prosa.Behavior.Service.service_at"
#print axioms Prosa.Behavior.Service.service_at

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Service.receives_service_at"
#check @Prosa.Behavior.Service.receives_service_at
#eval IO.println "FREEZE_END Prosa.Behavior.Service.receives_service_at"
#print axioms Prosa.Behavior.Service.receives_service_at

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Service.service_during"
#check @Prosa.Behavior.Service.service_during
#eval IO.println "FREEZE_END Prosa.Behavior.Service.service_during"
#print axioms Prosa.Behavior.Service.service_during

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Service.service"
#check @Prosa.Behavior.Service.service
#eval IO.println "FREEZE_END Prosa.Behavior.Service.service"
#print axioms Prosa.Behavior.Service.service

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Service.completed_by"
#check @Prosa.Behavior.Service.completed_by
#eval IO.println "FREEZE_END Prosa.Behavior.Service.completed_by"
#print axioms Prosa.Behavior.Service.completed_by

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Service.completes_at"
#check @Prosa.Behavior.Service.completes_at
#eval IO.println "FREEZE_END Prosa.Behavior.Service.completes_at"
#print axioms Prosa.Behavior.Service.completes_at

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Service.job_response_time_bound"
#check @Prosa.Behavior.Service.job_response_time_bound
#eval IO.println "FREEZE_END Prosa.Behavior.Service.job_response_time_bound"
#print axioms Prosa.Behavior.Service.job_response_time_bound

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Service.job_meets_deadline"
#check @Prosa.Behavior.Service.job_meets_deadline
#eval IO.println "FREEZE_END Prosa.Behavior.Service.job_meets_deadline"
#print axioms Prosa.Behavior.Service.job_meets_deadline

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Service.pending"
#check @Prosa.Behavior.Service.pending
#eval IO.println "FREEZE_END Prosa.Behavior.Service.pending"
#print axioms Prosa.Behavior.Service.pending

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Service.pending_earlier_and_at"
#check @Prosa.Behavior.Service.pending_earlier_and_at
#eval IO.println "FREEZE_END Prosa.Behavior.Service.pending_earlier_and_at"
#print axioms Prosa.Behavior.Service.pending_earlier_and_at

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Service.remaining_cost"
#check @Prosa.Behavior.Service.remaining_cost
#eval IO.println "FREEZE_END Prosa.Behavior.Service.remaining_cost"
#print axioms Prosa.Behavior.Service.remaining_cost

#check @Prosa.Validation.ScheduleInterface.coreEnumeration
#print axioms Prosa.Validation.ScheduleInterface.coreEnumeration
#check @Prosa.Validation.ScheduleInterface.production_scheduled_in_eq_true_iff
#print axioms Prosa.Validation.ScheduleInterface.production_scheduled_in_eq_true_iff
#check @Prosa.Validation.ScheduleInterface.production_service_in_as_list_sum
#print axioms Prosa.Validation.ScheduleInterface.production_service_in_as_list_sum

#check @Prosa.Validation.ServiceInterface.serviceDuringProjection
#print axioms Prosa.Validation.ServiceInterface.serviceDuringProjection
#check @Prosa.Validation.ServiceInterface.serviceDuringProjection_guard
#print axioms Prosa.Validation.ServiceInterface.serviceDuringProjection_guard
#check @Prosa.Validation.ServiceInterface.scheduled_at_eq
#print axioms Prosa.Validation.ServiceInterface.scheduled_at_eq
#check @Prosa.Validation.ServiceInterface.service_at_eq
#print axioms Prosa.Validation.ServiceInterface.service_at_eq
#check @Prosa.Validation.ServiceInterface.receives_service_at_eq
#print axioms Prosa.Validation.ServiceInterface.receives_service_at_eq
#check @Prosa.Validation.ServiceInterface.service_eq
#print axioms Prosa.Validation.ServiceInterface.service_eq
#check @Prosa.Validation.ServiceInterface.completed_by_eq
#print axioms Prosa.Validation.ServiceInterface.completed_by_eq
#check @Prosa.Validation.ServiceInterface.completes_at_eq
#print axioms Prosa.Validation.ServiceInterface.completes_at_eq
#check @Prosa.Validation.ServiceInterface.job_response_time_bound_eq
#print axioms Prosa.Validation.ServiceInterface.job_response_time_bound_eq
#check @Prosa.Validation.ServiceInterface.job_meets_deadline_eq
#print axioms Prosa.Validation.ServiceInterface.job_meets_deadline_eq
#check @Prosa.Validation.ServiceInterface.pending_eq
#print axioms Prosa.Validation.ServiceInterface.pending_eq
#check @Prosa.Validation.ServiceInterface.pending_earlier_and_at_eq
#print axioms Prosa.Validation.ServiceInterface.pending_earlier_and_at_eq
#check @Prosa.Validation.ServiceInterface.remaining_cost_eq
#print axioms Prosa.Validation.ServiceInterface.remaining_cost_eq

#check @Prosa.Validation.ServiceInterface.scheduledAtProjection
#print axioms Prosa.Validation.ServiceInterface.scheduledAtProjection
#check @Prosa.Validation.ServiceInterface.serviceAtProjection
#print axioms Prosa.Validation.ServiceInterface.serviceAtProjection
#check @Prosa.Validation.ServiceInterface.receivesServiceAtProjection
#print axioms Prosa.Validation.ServiceInterface.receivesServiceAtProjection
#check @Prosa.Validation.ServiceInterface.serviceProjection
#print axioms Prosa.Validation.ServiceInterface.serviceProjection
#check @Prosa.Validation.ServiceInterface.completedByProjection
#print axioms Prosa.Validation.ServiceInterface.completedByProjection
#check @Prosa.Validation.ServiceInterface.completesAtProjection
#print axioms Prosa.Validation.ServiceInterface.completesAtProjection
#check @Prosa.Validation.ServiceInterface.jobResponseTimeBoundProjection
#print axioms Prosa.Validation.ServiceInterface.jobResponseTimeBoundProjection
#check @Prosa.Validation.ServiceInterface.jobMeetsDeadlineProjection
#print axioms Prosa.Validation.ServiceInterface.jobMeetsDeadlineProjection
#check @Prosa.Validation.ServiceInterface.pendingProjection
#print axioms Prosa.Validation.ServiceInterface.pendingProjection
#check @Prosa.Validation.ServiceInterface.pendingEarlierAndAtProjection
#print axioms Prosa.Validation.ServiceInterface.pendingEarlierAndAtProjection
#check @Prosa.Validation.ServiceInterface.remainingCostProjection
#print axioms Prosa.Validation.ServiceInterface.remainingCostProjection

#check @Prosa.Validation.ServiceInterface.scheduledAtProjection_guard
#print axioms Prosa.Validation.ServiceInterface.scheduledAtProjection_guard
#check @Prosa.Validation.ServiceInterface.serviceAtProjection_guard
#print axioms Prosa.Validation.ServiceInterface.serviceAtProjection_guard
#check @Prosa.Validation.ServiceInterface.receivesServiceAtProjection_guard
#print axioms Prosa.Validation.ServiceInterface.receivesServiceAtProjection_guard
#check @Prosa.Validation.ServiceInterface.serviceProjection_guard
#print axioms Prosa.Validation.ServiceInterface.serviceProjection_guard
#check @Prosa.Validation.ServiceInterface.completedByProjection_guard
#print axioms Prosa.Validation.ServiceInterface.completedByProjection_guard
#check @Prosa.Validation.ServiceInterface.completesAtProjection_guard
#print axioms Prosa.Validation.ServiceInterface.completesAtProjection_guard
#check @Prosa.Validation.ServiceInterface.jobResponseTimeBoundProjection_guard
#print axioms Prosa.Validation.ServiceInterface.jobResponseTimeBoundProjection_guard
#check @Prosa.Validation.ServiceInterface.jobMeetsDeadlineProjection_guard
#print axioms Prosa.Validation.ServiceInterface.jobMeetsDeadlineProjection_guard
#check @Prosa.Validation.ServiceInterface.pendingProjection_guard
#print axioms Prosa.Validation.ServiceInterface.pendingProjection_guard
#check @Prosa.Validation.ServiceInterface.pendingEarlierAndAtProjection_guard
#print axioms Prosa.Validation.ServiceInterface.pendingEarlierAndAtProjection_guard
#check @Prosa.Validation.ServiceInterface.remainingCostProjection_guard
#print axioms Prosa.Validation.ServiceInterface.remainingCostProjection_guard
