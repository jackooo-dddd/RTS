import Validation.fixtures.translation_order.ReadyComputationInterface

#check @Prosa.Behavior.Ready.JobReady
#print axioms Prosa.Behavior.Ready.JobReady
#check @Prosa.Behavior.Ready.backlogged
#print axioms Prosa.Behavior.Ready.backlogged
#check @Prosa.Behavior.Ready.jobs_come_from_arrival_sequence
#print axioms Prosa.Behavior.Ready.jobs_come_from_arrival_sequence
#check @Prosa.Behavior.Ready.jobs_must_arrive_to_execute
#print axioms Prosa.Behavior.Ready.jobs_must_arrive_to_execute
#check @Prosa.Behavior.Ready.jobs_must_be_ready_to_execute
#print axioms Prosa.Behavior.Ready.jobs_must_be_ready_to_execute
#check @Prosa.Behavior.Ready.completed_jobs_dont_execute
#print axioms Prosa.Behavior.Ready.completed_jobs_dont_execute
#check @Prosa.Behavior.Ready.valid_schedule
#print axioms Prosa.Behavior.Ready.valid_schedule

#check @Prosa.Validation.ReadyInterface.backloggedProjection
#print axioms Prosa.Validation.ReadyInterface.backloggedProjection
#check @Prosa.Validation.ReadyInterface.jobsComeFromArrivalSequenceProjection
#print axioms Prosa.Validation.ReadyInterface.jobsComeFromArrivalSequenceProjection
#check @Prosa.Validation.ReadyInterface.jobsMustArriveToExecuteProjection
#print axioms Prosa.Validation.ReadyInterface.jobsMustArriveToExecuteProjection
#check @Prosa.Validation.ReadyInterface.jobsMustBeReadyToExecuteProjection
#print axioms Prosa.Validation.ReadyInterface.jobsMustBeReadyToExecuteProjection
#check @Prosa.Validation.ReadyInterface.completedJobsDontExecuteProjection
#print axioms Prosa.Validation.ReadyInterface.completedJobsDontExecuteProjection
#check @Prosa.Validation.ReadyInterface.validScheduleProjection
#print axioms Prosa.Validation.ReadyInterface.validScheduleProjection

#check @Prosa.Validation.ReadyInterface.backloggedProjection_guard
#print axioms Prosa.Validation.ReadyInterface.backloggedProjection_guard
#check @Prosa.Validation.ReadyInterface.jobsComeFromArrivalSequenceProjection_guard
#print axioms Prosa.Validation.ReadyInterface.jobsComeFromArrivalSequenceProjection_guard
#check @Prosa.Validation.ReadyInterface.jobsMustArriveToExecuteProjection_guard
#print axioms Prosa.Validation.ReadyInterface.jobsMustArriveToExecuteProjection_guard
#check @Prosa.Validation.ReadyInterface.jobsMustBeReadyToExecuteProjection_guard
#print axioms Prosa.Validation.ReadyInterface.jobsMustBeReadyToExecuteProjection_guard
#check @Prosa.Validation.ReadyInterface.completedJobsDontExecuteProjection_guard
#print axioms Prosa.Validation.ReadyInterface.completedJobsDontExecuteProjection_guard
#check @Prosa.Validation.ReadyInterface.validScheduleProjection_guard
#print axioms Prosa.Validation.ReadyInterface.validScheduleProjection_guard
