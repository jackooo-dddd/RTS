# `service_at_implies_scheduled_at`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.service_at_implies_scheduled_at`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_at_implies_scheduled_at`
- Certificate: `service_at_implies_scheduled_at_correspondence`

## Official Rocq

```coq
service_at_implies_scheduled_at :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant),
is_true (0 < @service_at Job PState sched j t) -> is_true (@scheduled_at Job PState sched j t)

service_at_implies_scheduled_at is not universe polymorphic
Arguments service_at_implies_scheduled_at {Job PState} sched j t _
service_at_implies_scheduled_at is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_at_implies_scheduled_at
Declared in library prosa.analysis.facts.behavior.service, line 334, characters 8-39
@service_at_implies_scheduled_at
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (0 < @service_at Job PState sched j t) -> is_true (@scheduled_at Job PState sched j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_at_implies_scheduled_at : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
  0 < Prosa.Behavior.Service.service_at sched j t → Prosa.Behavior.Service.scheduled_at sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_at_implies_scheduled_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j t) ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true
```
