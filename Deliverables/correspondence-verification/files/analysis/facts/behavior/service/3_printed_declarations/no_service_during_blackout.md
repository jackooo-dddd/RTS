# `no_service_during_blackout`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.no_service_during_blackout`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.no_service_during_blackout`
- Certificate: `no_service_during_blackout_correspondence`

## Official Rocq

```coq
no_service_during_blackout :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant),
is_true (@is_blackout Job PState sched t) -> @service_at Job PState sched j t = 0

no_service_during_blackout is not universe polymorphic
Arguments no_service_during_blackout {Job PState} sched j t _
no_service_during_blackout is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.no_service_during_blackout
Declared in library prosa.analysis.facts.behavior.service, line 722, characters 8-34
@no_service_during_blackout
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (@is_blackout Job PState sched t) -> @service_at Job PState sched j t = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.no_service_during_blackout : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Processor.Supply.is_blackout sched t = true → Prosa.Behavior.Service.service_at sched j t = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_no_service_during_blackout
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Processor_Supply_is_blackout Job
            inst_3 PState sched t)
         Bool_true ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j t)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
```
