# `scheduled_at_precedes_completes_at`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.completes_at.scheduled_at_precedes_completes_at`
- Lean: `Prosa.Analysis.Facts.CompletesAt.scheduled_at_precedes_completes_at`
- Certificate: `scheduled_at_precedes_completes_at_correspondence`

## Official Rocq

```coq
scheduled_at_precedes_completes_at :
forall {Job : JobType} {H0 : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (j : Equality.sort Job) (t : instant),
is_true (0 < t) ->
is_true (@completes_at Job PState sched H0 j t) -> is_true (@scheduled_at Job PState sched j t.-1)

scheduled_at_precedes_completes_at is not universe polymorphic
Arguments scheduled_at_precedes_completes_at {Job H0 PState} sched j t _ _
scheduled_at_precedes_completes_at is opaque
Expands to: Constant prosa.analysis.facts.completes_at.scheduled_at_precedes_completes_at
Declared in library prosa.analysis.facts.completes_at, line 32, characters 8-42
@scheduled_at_precedes_completes_at
     : forall (Job : JobType) (H0 : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (0 < t) ->
       is_true (@completes_at Job PState sched H0 j t) -> is_true (@scheduled_at Job PState sched j t.-1)
```

## Lean

```lean
@Prosa.Analysis.Facts.CompletesAt.scheduled_at_precedes_completes_at : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (t : Prosa.Behavior.Time.instant),
  0 < t →
    Prosa.Behavior.Service.completes_at sched j t = true → Prosa.Behavior.Service.scheduled_at sched j (t - 1) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_CompletesAt_scheduled_at_precedes_completes_at
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
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t ->
       @eq Bool
         (Prosa_Behavior_Service_completes_at Job
            inst_3 PState sched
            inst_6 j t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j
            (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
         Bool_true
```
