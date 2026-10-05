# `schedule_up_to_def`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.generic_schedule.schedule_up_to_def`
- Lean: `Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_def`
- Certificate: `schedule_up_to_def_correspondence`

## Official Rocq

```coq
schedule_up_to_def :
forall {Job : JobType} {PState : ProcessorState Job} (policy : @PointwisePolicy Job PState)
  (idle_state : @State Job PState) (t : instant),
@schedule_up_to Job PState policy idle_state t t =
policy
  ((fun t0 : nat =>
    match t0 with
    | 0 => @empty_schedule Job PState idle_state
    | t'.+1 => @schedule_up_to Job PState policy idle_state t'
    end) t)
  t

schedule_up_to_def is not universe polymorphic
Arguments schedule_up_to_def {Job PState} policy idle_state t
schedule_up_to_def is opaque
Expands to: Constant prosa.implementation.facts.generic_schedule.schedule_up_to_def
Declared in library prosa.implementation.facts.generic_schedule, line 27, characters 8-26
@schedule_up_to_def
     : forall (Job : JobType) (PState : ProcessorState Job) (policy : @PointwisePolicy Job PState)
         (idle_state : @State Job PState) (t : instant),
       @schedule_up_to Job PState policy idle_state t t =
       policy
         match t with
         | 0 => @empty_schedule Job PState idle_state
         | t'.+1 => @schedule_up_to Job PState policy idle_state t'
         end t
```

## Lean

```lean
@Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_def : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (policy : Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy PState)
  (idle_state : Prosa.Behavior.Schedule.ProcessorState.State Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to policy idle_state t t =
    policy
      (match t with
      | 0 => Prosa.Implementation.Definitions.GenericScheduler.empty_schedule idle_state
      | Nat.succ t' => Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to policy idle_state t')
      t
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_def
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (policy : Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy Job
                     inst_3 PState)
         (idle_state : Prosa_Behavior_Schedule_ProcessorState_State Job
                         inst_3
                         PState)
         (t : Prosa_Behavior_Time_instant),
       @eq
         (Prosa_Behavior_Schedule_ProcessorState_State Job
            inst_3 PState)
         (Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to Job
            inst_3 PState policy
            idle_state t t)
         (policy
            (Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_def_match_1
               (fun _ : Prosa_Behavior_Time_instant =>
                Prosa_Behavior_Schedule_schedule Job
                  inst_3 PState)
               t
               (fun _ : Unit =>
                Prosa_Implementation_Definitions_GenericScheduler_empty_schedule Job
                  inst_3 PState
                  idle_state)
               (fun t' : Prosa_Behavior_Time_instant =>
                Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to Job
                  inst_3 PState
                  policy idle_state t'))
            t)
```
