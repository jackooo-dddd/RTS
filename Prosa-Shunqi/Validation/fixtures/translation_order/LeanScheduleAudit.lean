import Validation.fixtures.translation_order.ScheduleComputationInterface

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Schedule.ProcessorState"
#check @Prosa.Behavior.Schedule.ProcessorState
#check @Prosa.Behavior.Schedule.ProcessorState.mk
#check @Prosa.Behavior.Schedule.ProcessorState.State
#check @Prosa.Behavior.Schedule.ProcessorState.Core
#check @Prosa.Behavior.Schedule.ProcessorState.coreFintype
#check @Prosa.Behavior.Schedule.ProcessorState.coreDecidableEq
#check @Prosa.Behavior.Schedule.ProcessorState.scheduled_on
#check @Prosa.Behavior.Schedule.ProcessorState.supply_on
#check @Prosa.Behavior.Schedule.ProcessorState.service_on
#check @Prosa.Behavior.Schedule.ProcessorState.service_on_le_supply_on
#check @Prosa.Behavior.Schedule.ProcessorState.service_on_implies_scheduled_on
#eval IO.println "FREEZE_END Prosa.Behavior.Schedule.ProcessorState"
#print axioms Prosa.Behavior.Schedule.ProcessorState

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Schedule.ProcessorState.scheduled_in"
#check @Prosa.Behavior.Schedule.ProcessorState.scheduled_in
#eval IO.println "FREEZE_END Prosa.Behavior.Schedule.ProcessorState.scheduled_in"
#print axioms Prosa.Behavior.Schedule.ProcessorState.scheduled_in

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Schedule.ProcessorState.supply_in"
#check @Prosa.Behavior.Schedule.ProcessorState.supply_in
#eval IO.println "FREEZE_END Prosa.Behavior.Schedule.ProcessorState.supply_in"
#print axioms Prosa.Behavior.Schedule.ProcessorState.supply_in

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Schedule.ProcessorState.service_in"
#check @Prosa.Behavior.Schedule.ProcessorState.service_in
#eval IO.println "FREEZE_END Prosa.Behavior.Schedule.ProcessorState.service_in"
#print axioms Prosa.Behavior.Schedule.ProcessorState.service_in

#eval IO.println "FREEZE_BEGIN Prosa.Behavior.Schedule.schedule"
#check @Prosa.Behavior.Schedule.schedule
#eval IO.println "FREEZE_END Prosa.Behavior.Schedule.schedule"
#print axioms Prosa.Behavior.Schedule.schedule

#check @Prosa.Behavior.Schedule.ProcessorState.scheduled_in_eq_true_iff
#print axioms Prosa.Behavior.Schedule.ProcessorState.scheduled_in_eq_true_iff

#check @Prosa.Validation.ScheduleInterface.coreEnumeration
#print axioms Prosa.Validation.ScheduleInterface.coreEnumeration
#check @Prosa.Validation.ScheduleInterface.coreEnumeration_nodup
#print axioms Prosa.Validation.ScheduleInterface.coreEnumeration_nodup
#check @Prosa.Validation.ScheduleInterface.coreEnumeration_complete
#print axioms Prosa.Validation.ScheduleInterface.coreEnumeration_complete
#check @Prosa.Validation.ScheduleInterface.production_scheduled_in_eq_true_iff
#print axioms Prosa.Validation.ScheduleInterface.production_scheduled_in_eq_true_iff
#check @Prosa.Validation.ScheduleInterface.production_supply_in_eq
#print axioms Prosa.Validation.ScheduleInterface.production_supply_in_eq
#check @Prosa.Validation.ScheduleInterface.production_service_in_eq
#print axioms Prosa.Validation.ScheduleInterface.production_service_in_eq
#check @Prosa.Validation.ScheduleInterface.production_supply_in_as_list_sum
#print axioms Prosa.Validation.ScheduleInterface.production_supply_in_as_list_sum
#check @Prosa.Validation.ScheduleInterface.production_service_in_as_list_sum
#print axioms Prosa.Validation.ScheduleInterface.production_service_in_as_list_sum
#check @Prosa.Validation.ScheduleInterface.production_schedule_eq
#print axioms Prosa.Validation.ScheduleInterface.production_schedule_eq
