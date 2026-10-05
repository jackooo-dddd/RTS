# `schedule_up_to_identical_prefix`

- Kind (Rocq): Corollary
- Rocq: `prosa.implementation.facts.generic_schedule.schedule_up_to_identical_prefix`
- Lean: `Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_identical_prefix`
- Certificate: `schedule_up_to_identical_prefix_correspondence`

## Official Rocq

```coq
schedule_up_to_identical_prefix :
forall {Job : JobType} {PState : ProcessorState Job} (policy : @PointwisePolicy Job PState)
  (idle_state : @State Job PState) (h t : nat),
is_true (t <= h.+1) ->
@identical_prefix Job PState (@schedule_up_to Job PState policy idle_state h)
  (@generic_schedule Job PState policy idle_state) t

schedule_up_to_identical_prefix is not universe polymorphic
Arguments schedule_up_to_identical_prefix {Job PState} policy idle_state (h t)%nat_scope _ t _
schedule_up_to_identical_prefix is opaque
Expands to: Constant prosa.implementation.facts.generic_schedule.schedule_up_to_identical_prefix
Declared in library prosa.implementation.facts.generic_schedule, line 87, characters 12-43
@schedule_up_to_identical_prefix
     : forall (Job : JobType) (PState : ProcessorState Job) (policy : @PointwisePolicy Job PState)
         (idle_state : @State Job PState) (h t : nat),
       is_true (t <= h.+1) ->
       @identical_prefix Job PState (@schedule_up_to Job PState policy idle_state h)
         (@generic_schedule Job PState policy idle_state) t
```

## Lean

```lean
@Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_identical_prefix : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (policy : Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy PState)
  (idle_state : Prosa.Behavior.Schedule.ProcessorState.State Job) (h t : ℕ),
  t ≤ h + 1 →
    Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix
      (Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to policy idle_state h)
      (Prosa.Implementation.Definitions.GenericScheduler.generic_schedule policy idle_state) t
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_identical_prefix
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
       LE_le_inst1 Nat instLENat t
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) h
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))) ->
       Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix Job
         inst_3 PState
         (Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to Job
            inst_3 PState policy
            idle_state h)
         (Prosa_Implementation_Definitions_GenericScheduler_generic_schedule Job
            inst_3 PState policy
            idle_state)
         t
```
