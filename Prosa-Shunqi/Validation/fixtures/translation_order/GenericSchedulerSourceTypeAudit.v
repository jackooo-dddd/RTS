From prosa Require Import implementation.definitions.generic_scheduler.

Check @prosa.implementation.definitions.generic_scheduler.PointwisePolicy.
Check @prosa.implementation.definitions.generic_scheduler.empty_schedule.
Check @prosa.implementation.definitions.generic_scheduler.schedule_up_to.
Check @prosa.implementation.definitions.generic_scheduler.generic_schedule.

Definition generic_scheduler_pointwise_policy_type_guard :
  forall (Job : JobType) (PState : ProcessorState Job), Type :=
  @prosa.implementation.definitions.generic_scheduler.PointwisePolicy.

Definition generic_scheduler_empty_schedule_type_guard :
  forall (Job : JobType) (PState : ProcessorState Job),
    PState -> schedule PState :=
  @prosa.implementation.definitions.generic_scheduler.empty_schedule.

Definition generic_scheduler_schedule_up_to_type_guard :
  forall (Job : JobType) (PState : ProcessorState Job),
    PointwisePolicy PState -> PState -> instant -> schedule PState :=
  @prosa.implementation.definitions.generic_scheduler.schedule_up_to.

Definition generic_scheduler_generic_schedule_type_guard :
  forall (Job : JobType) (PState : ProcessorState Job),
    PointwisePolicy PState -> PState -> instant -> PState :=
  @prosa.implementation.definitions.generic_scheduler.generic_schedule.

Print Assumptions prosa.implementation.definitions.generic_scheduler.PointwisePolicy.
Print Assumptions prosa.implementation.definitions.generic_scheduler.empty_schedule.
Print Assumptions prosa.implementation.definitions.generic_scheduler.schedule_up_to.
Print Assumptions prosa.implementation.definitions.generic_scheduler.generic_schedule.
