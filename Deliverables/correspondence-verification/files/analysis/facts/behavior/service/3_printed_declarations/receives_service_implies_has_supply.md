# `receives_service_implies_has_supply`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.receives_service_implies_has_supply`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.receives_service_implies_has_supply`
- Certificate: `receives_service_implies_has_supply_correspondence`

## Official Rocq

```coq
receives_service_implies_has_supply :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant),
is_true (@receives_service_at Job PState sched j t) -> is_true (@has_supply Job PState sched t)

receives_service_implies_has_supply is not universe polymorphic
Arguments receives_service_implies_has_supply {Job PState} sched j t _
receives_service_implies_has_supply is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.receives_service_implies_has_supply
Declared in library prosa.analysis.facts.behavior.service, line 702, characters 8-43
@receives_service_implies_has_supply
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (@receives_service_at Job PState sched j t) -> is_true (@has_supply Job PState sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.receives_service_implies_has_supply : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.receives_service_at sched j t = true → Prosa.Model.Processor.Supply.has_supply sched t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_receives_service_implies_has_supply
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
         (Prosa_Model_Processor_Supply_has_supply Job
            inst_3 PState sched t)
         Bool_true
```
