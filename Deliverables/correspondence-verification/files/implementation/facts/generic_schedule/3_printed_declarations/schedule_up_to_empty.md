# `schedule_up_to_empty`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.generic_schedule.schedule_up_to_empty`
- Lean: `Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_empty`
- Certificate: `schedule_up_to_empty_correspondence`

## Official Rocq

```coq
schedule_up_to_empty :
forall {Job : JobType} {PState : ProcessorState Job} (policy : @PointwisePolicy Job PState)
  (idle_state : @State Job PState) (h t : nat),
is_true (h < t) -> @schedule_up_to Job PState policy idle_state h t = idle_state

schedule_up_to_empty is not universe polymorphic
Arguments schedule_up_to_empty {Job PState} policy idle_state (h t)%nat_scope _
schedule_up_to_empty is opaque
Expands to: Constant prosa.implementation.facts.generic_schedule.schedule_up_to_empty
Declared in library prosa.implementation.facts.generic_schedule, line 53, characters 8-28
@schedule_up_to_empty
     : forall (Job : JobType) (PState : ProcessorState Job) (policy : @PointwisePolicy Job PState)
         (idle_state : @State Job PState) (h t : nat),
       is_true (h < t) -> @schedule_up_to Job PState policy idle_state h t = idle_state
```

## Lean

```lean
@Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_empty : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (policy : Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy PState)
  (idle_state : Prosa.Behavior.Schedule.ProcessorState.State Job) (h t : ℕ),
  h < t → Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to policy idle_state h t = idle_state
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_empty
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (policy : Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy Job
                     inst_3 PState)
         (idle_state : Prosa_Behavior_Schedule_ProcessorState_State Job
                         inst_3
                         PState)
         (h t : Nat),
       LT_lt_inst1 Nat instLTNat h t ->
       @eq
         (Prosa_Behavior_Schedule_ProcessorState_State Job
            inst_3 PState)
         (Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to Job
            inst_3 PState policy
            idle_state h t)
         idle_state
```
