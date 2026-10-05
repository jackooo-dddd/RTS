# `schedule_up_to_prefix_inclusion`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.generic_schedule.schedule_up_to_prefix_inclusion`
- Lean: `Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_prefix_inclusion`
- Certificate: `schedule_up_to_prefix_inclusion_correspondence`

## Official Rocq

```coq
schedule_up_to_prefix_inclusion :
forall {Job : JobType} {PState : ProcessorState Job} (policy : @PointwisePolicy Job PState)
  (idle_state : @State Job PState) (h1 h2 : nat),
is_true (h1 <= h2) ->
forall t : nat,
is_true (t <= h1) ->
@schedule_up_to Job PState policy idle_state h1 t = @schedule_up_to Job PState policy idle_state h2 t

schedule_up_to_prefix_inclusion is not universe polymorphic
Arguments schedule_up_to_prefix_inclusion {Job PState} policy idle_state (h1 h2)%nat_scope _ t%nat_scope _
schedule_up_to_prefix_inclusion is opaque
Expands to: Constant prosa.implementation.facts.generic_schedule.schedule_up_to_prefix_inclusion
Declared in library prosa.implementation.facts.generic_schedule, line 70, characters 8-39
@schedule_up_to_prefix_inclusion
     : forall (Job : JobType) (PState : ProcessorState Job) (policy : @PointwisePolicy Job PState)
         (idle_state : @State Job PState) (h1 h2 : nat),
       is_true (h1 <= h2) ->
       forall t : nat,
       is_true (t <= h1) ->
       @schedule_up_to Job PState policy idle_state h1 t = @schedule_up_to Job PState policy idle_state h2 t
```

## Lean

```lean
@Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_prefix_inclusion : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (policy : Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy PState)
  (idle_state : Prosa.Behavior.Schedule.ProcessorState.State Job) (h1 h2 : ℕ),
  h1 ≤ h2 →
    ∀ t ≤ h1,
      Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to policy idle_state h1 t =
        Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to policy idle_state h2 t
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_prefix_inclusion
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (policy : Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy Job
                     inst_3 PState)
         (idle_state : Prosa_Behavior_Schedule_ProcessorState_State Job
                         inst_3
                         PState)
         (h1 h2 : Nat),
       LE_le_inst1 Nat instLENat h1 h2 ->
       forall t : Nat,
       LE_le_inst1 Nat instLENat t h1 ->
       @eq
         (Prosa_Behavior_Schedule_ProcessorState_State Job
            inst_3 PState)
         (Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to Job
            inst_3 PState policy
            idle_state h1 t)
         (Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to Job
            inst_3 PState policy
            idle_state h2 t)
```
