# `no_blackout_when_service_received`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.no_blackout_when_service_received`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.no_blackout_when_service_received`
- Certificate: `no_blackout_when_service_received_correspondence`

## Official Rocq

```coq
no_blackout_when_service_received :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant),
is_true (@receives_service_at Job PState sched j t) -> is_true (~~ @is_blackout Job PState sched t)

no_blackout_when_service_received is not universe polymorphic
Arguments no_blackout_when_service_received {Job PState} sched j t _
no_blackout_when_service_received is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.no_blackout_when_service_received
Declared in library prosa.analysis.facts.behavior.service, line 712, characters 8-41
@no_blackout_when_service_received
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (@receives_service_at Job PState sched j t) -> is_true (~~ @is_blackout Job PState sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.no_blackout_when_service_received : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.receives_service_at sched j t = true →
    (!Prosa.Model.Processor.Supply.is_blackout sched t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_no_blackout_when_service_received
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_receives_service_at Job
            inst_3 PState sched j t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Model_Processor_Supply_is_blackout Job
               inst_3 PState sched t))
         Bool_true
```
