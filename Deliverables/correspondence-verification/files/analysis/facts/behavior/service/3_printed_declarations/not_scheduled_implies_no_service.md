# `not_scheduled_implies_no_service`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.service.not_scheduled_implies_no_service`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.not_scheduled_implies_no_service`
- Certificate: `not_scheduled_implies_no_service_correspondence`

## Official Rocq

```coq
not_scheduled_implies_no_service :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant),
is_true (~~ @scheduled_at Job PState sched j t) -> @service_at Job PState sched j t = 0

not_scheduled_implies_no_service is not universe polymorphic
Arguments not_scheduled_implies_no_service {Job PState} sched j t _
not_scheduled_implies_no_service is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.not_scheduled_implies_no_service
Declared in library prosa.analysis.facts.behavior.service, line 316, characters 12-44
@not_scheduled_implies_no_service
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (~~ @scheduled_at Job PState sched j t) -> @service_at Job PState sched j t = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.not_scheduled_implies_no_service : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
  (!Prosa.Behavior.Service.scheduled_at sched j t) = true → Prosa.Behavior.Service.service_at sched j t = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_not_scheduled_implies_no_service
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_scheduled_at Job
               inst_3 PState sched j t))
         Bool_true ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j t)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
```
