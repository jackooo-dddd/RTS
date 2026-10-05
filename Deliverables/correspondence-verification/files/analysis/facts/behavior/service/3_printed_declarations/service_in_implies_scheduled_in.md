# `service_in_implies_scheduled_in`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.service_in_implies_scheduled_in`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_in_implies_scheduled_in`
- Certificate: `service_in_implies_scheduled_in_correspondence`

## Official Rocq

```coq
service_in_implies_scheduled_in :
forall {Job : JobType} {PState : ProcessorState Job} (j : Equality.sort Job) (s : @State Job PState),
is_true (~~ @scheduled_in Job PState j s) -> @service_in Job PState j s = 0

service_in_implies_scheduled_in is not universe polymorphic
Arguments service_in_implies_scheduled_in {Job PState} j s _
service_in_implies_scheduled_in is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_in_implies_scheduled_in
Declared in library prosa.analysis.facts.behavior.service, line 305, characters 8-39
@service_in_implies_scheduled_in
     : forall (Job : JobType) (PState : ProcessorState Job) (j : Equality.sort Job) (s : @State Job PState),
       is_true (~~ @scheduled_in Job PState j s) -> @service_in Job PState j s = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_in_implies_scheduled_in : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job} (j : Job)
  (s : Prosa.Behavior.Schedule.ProcessorState.State Job), (!PState.scheduled_in j s) = true → PState.service_in j s = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_in_implies_scheduled_in
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (j : Job)
         (s : Prosa_Behavior_Schedule_ProcessorState_State Job
                inst_3 PState),
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Schedule_ProcessorState_scheduled_in Job
               inst_3 PState j s))
         Bool_true ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Schedule_ProcessorState_service_in Job
            inst_3 PState j s)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
```
