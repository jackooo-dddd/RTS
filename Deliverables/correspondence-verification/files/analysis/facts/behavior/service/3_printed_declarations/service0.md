# `service0`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.service.service0`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service0`
- Certificate: `service0_correspondence`

## Official Rocq

```coq
service0 :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (j : Equality.sort Job),
@service Job PState sched j 0 = 0

service0 is not universe polymorphic
Arguments service0 {Job PState} sched j
service0 is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service0
Declared in library prosa.analysis.facts.behavior.service, line 50, characters 12-20
@service0
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job),
       @service Job PState sched j 0 = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service0 : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job),
  Prosa.Behavior.Service.service sched j 0 = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service0
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job),
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)))
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
```
