# `service_delta_implies_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.service_delta_implies_scheduled`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_delta_implies_scheduled`
- Certificate: `service_delta_implies_scheduled_correspondence`

## Official Rocq

```coq
service_delta_implies_scheduled :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant),
is_true (@service Job PState sched j t < @service Job PState sched j t.+1) ->
is_true (@scheduled_at Job PState sched j t)

service_delta_implies_scheduled is not universe polymorphic
Arguments service_delta_implies_scheduled {Job PState} sched j t _
service_delta_implies_scheduled is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_delta_implies_scheduled
Declared in library prosa.analysis.facts.behavior.service, line 344, characters 8-39
@service_delta_implies_scheduled
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (@service Job PState sched j t < @service Job PState sched j t.+1) ->
       is_true (@scheduled_at Job PState sched j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_delta_implies_scheduled : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.service sched j t < Prosa.Behavior.Service.service sched j (t + 1) →
    Prosa.Behavior.Service.scheduled_at sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_delta_implies_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t)
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))) ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true
```
