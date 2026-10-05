# `not_scheduled_remains_incomplete`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.not_scheduled_remains_incomplete`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.not_scheduled_remains_incomplete`
- Certificate: `not_scheduled_remains_incomplete_correspondence`

## Official Rocq

```coq
not_scheduled_remains_incomplete :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (j : Equality.sort Job) (t : instant),
is_true (~~ @completed_by Job PState sched H j t) ->
is_true (~~ @scheduled_at Job PState sched j t) -> is_true (~~ @completed_by Job PState sched H j t.+1)

not_scheduled_remains_incomplete is not universe polymorphic
Arguments not_scheduled_remains_incomplete {Job H PState} sched j t _ _
not_scheduled_remains_incomplete is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.not_scheduled_remains_incomplete
Declared in library prosa.analysis.facts.behavior.completion, line 148, characters 8-40
@not_scheduled_remains_incomplete
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (~~ @completed_by Job PState sched H j t) ->
       is_true (~~ @scheduled_at Job PState sched j t) ->
       is_true (~~ @completed_by Job PState sched H j t.+1)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.not_scheduled_remains_incomplete : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (t : Prosa.Behavior.Time.instant),
  (!Prosa.Behavior.Service.completed_by sched j t) = true →
    (!Prosa.Behavior.Service.scheduled_at sched j t) = true →
      (!Prosa.Behavior.Service.completed_by sched j (t + 1)) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_not_scheduled_remains_incomplete
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3 PState sched
               inst_6 j t))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_scheduled_at Job
               inst_3 PState sched j t))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3 PState sched
               inst_6 j
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))))
         Bool_true
```
