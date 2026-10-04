import Validation.fixtures.translation_order.ClassicUniPlatformInterface
set_option pp.fieldNotation false

#check @Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.work_conserving
#check @Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.respects_FP_policy
#check @Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.respects_JLFP_policy
#check @Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.respects_JLDP_policy
#check @Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.job_never_backlogged_response_time_holds

#print axioms Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.work_conserving
#print axioms Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.respects_FP_policy
#print axioms Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.respects_JLFP_policy
#print axioms Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.respects_JLDP_policy
#print axioms Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.job_never_backlogged_response_time_holds
