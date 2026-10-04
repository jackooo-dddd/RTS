import Validation.fixtures.translation_order.ClassicUniLastExecutionInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.time_after_last_execution
#check @Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.last_execution_after_arrival
#check @Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.last_execution_monotonic
#check @Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.last_execution_idempotent
#check @Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.last_execution_bounded_by_identity
#check @Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.same_service_implies_same_last_execution
#check @Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.same_service_since_last_execution
#check @Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.exists_last_execution_with_smaller_service
#check @Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.less_service_before_start_of_suspension
#check @Prosa.Validation.ClassicUniLastExecutionInterface.finRange_map_shift
#check @Prosa.Validation.ClassicUniLastExecutionInterface.finRange_map_val
#check @Prosa.Validation.ClassicUniLastExecutionInterface.finRange_any
#check @Prosa.Validation.ClassicUniLastExecutionInterface.map_finRange_eq_map_range'
#check @Prosa.Validation.ClassicUniLastExecutionInterface.maxFiltered_eq_foldr_cond
#check @Prosa.Validation.ClassicUniLastExecutionInterface.maxFiltered_finRange

#print axioms Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.time_after_last_execution
#print axioms Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.last_execution_after_arrival
#print axioms Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.last_execution_monotonic
#print axioms Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.last_execution_idempotent
#print axioms Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.last_execution_bounded_by_identity
#print axioms Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.same_service_implies_same_last_execution
#print axioms Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.same_service_since_last_execution
#print axioms Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.exists_last_execution_with_smaller_service
#print axioms Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution.less_service_before_start_of_suspension
#print axioms Prosa.Validation.ClassicUniLastExecutionInterface.finRange_map_shift
#print axioms Prosa.Validation.ClassicUniLastExecutionInterface.finRange_map_val
#print axioms Prosa.Validation.ClassicUniLastExecutionInterface.finRange_any
#print axioms Prosa.Validation.ClassicUniLastExecutionInterface.map_finRange_eq_map_range'
#print axioms Prosa.Validation.ClassicUniLastExecutionInterface.maxFiltered_eq_foldr_cond
#print axioms Prosa.Validation.ClassicUniLastExecutionInterface.maxFiltered_finRange
