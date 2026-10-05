# `service_during_instant`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.service_during_instant`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_during_instant`
- Certificate: `service_during_instant_correspondence`

## Official Rocq

```coq
service_during_instant :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant),
@service_during Job PState sched j t t.+1 = @service_at Job PState sched j t

service_during_instant is not universe polymorphic
Arguments service_during_instant {Job PState} sched j t
service_during_instant is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_during_instant
Declared in library prosa.analysis.facts.behavior.service, line 56, characters 8-30
@service_during_instant
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       @service_during Job PState sched j t t.+1 = @service_at Job PState sched j t
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_during_instant : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.service_during sched j t (t + 1) = Prosa.Behavior.Service.service_at sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_during_instant
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j t)
```
