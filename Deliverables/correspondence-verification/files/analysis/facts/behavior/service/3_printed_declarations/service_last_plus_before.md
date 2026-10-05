# `service_last_plus_before`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.service.service_last_plus_before`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_last_plus_before`
- Certificate: `service_last_plus_before_correspondence`

## Official Rocq

```coq
service_last_plus_before :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant),
@service Job PState sched j t + @service_at Job PState sched j t = @service Job PState sched j t.+1

service_last_plus_before is not universe polymorphic
Arguments service_last_plus_before {Job PState} sched j t
service_last_plus_before is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_last_plus_before
Declared in library prosa.analysis.facts.behavior.service, line 104, characters 12-36
@service_last_plus_before
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       @service Job PState sched j t + @service_at Job PState sched j t = @service Job PState sched j t.+1
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_last_plus_before : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.service sched j t + Prosa.Behavior.Service.service_at sched j t =
    Prosa.Behavior.Service.service sched j (t + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_last_plus_before
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Prosa_Behavior_Job_work
         (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
            (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
            (Prosa_Behavior_Service_service Job
               inst_3 PState sched j t)
            (Prosa_Behavior_Service_service_at Job
               inst_3 PState sched j t))
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
```
