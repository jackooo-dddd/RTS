# `schedule_up_to_widen`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.generic_schedule.schedule_up_to_widen`
- Lean: `Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_widen`
- Certificate: `schedule_up_to_widen_correspondence`

## Official Rocq

```coq
schedule_up_to_widen :
forall {Job : JobType} {PState : ProcessorState Job} (policy : @PointwisePolicy Job PState)
  (idle_state : @State Job PState) (h t : nat),
is_true (t <= h) ->
@schedule_up_to Job PState policy idle_state h t = @schedule_up_to Job PState policy idle_state h.+1 t

schedule_up_to_widen is not universe polymorphic
Arguments schedule_up_to_widen {Job PState} policy idle_state (h t)%nat_scope _
schedule_up_to_widen is opaque
Expands to: Constant prosa.implementation.facts.generic_schedule.schedule_up_to_widen
Declared in library prosa.implementation.facts.generic_schedule, line 41, characters 8-28
@schedule_up_to_widen
     : forall (Job : JobType) (PState : ProcessorState Job) (policy : @PointwisePolicy Job PState)
         (idle_state : @State Job PState) (h t : nat),
       is_true (t <= h) ->
       @schedule_up_to Job PState policy idle_state h t = @schedule_up_to Job PState policy idle_state h.+1 t
```

## Lean

```lean
@Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_widen : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (policy : Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy PState)
  (idle_state : Prosa.Behavior.Schedule.ProcessorState.State Job) (h t : ℕ),
  t ≤ h →
    Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to policy idle_state h t =
      Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to policy idle_state (h + 1) t
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_widen
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
       LE_le_inst1 Nat instLENat t h ->
       @eq
         (Prosa_Behavior_Schedule_ProcessorState_State Job
            inst_3 PState)
         (Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to Job
            inst_3 PState policy
            idle_state h t)
         (Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to Job
            inst_3 PState policy
            idle_state
            (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) h
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
            t)
```
