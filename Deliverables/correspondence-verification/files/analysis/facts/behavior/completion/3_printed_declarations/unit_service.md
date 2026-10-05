# `unit_service`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.unit_service`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.unit_service`
- Certificate: `unit_service_correspondence`

## Official Rocq

```coq
unit_service :
forall {Job : JobType} {PState : ProcessorState Job} (j : Equality.sort Job),
@unit_service_proc_model Job PState ->
forall s : @State Job PState, is_true (@service_in Job PState j s <= 1)

unit_service is not universe polymorphic
Arguments unit_service {Job PState} j H_unit_service s
unit_service is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.unit_service
Declared in library prosa.analysis.facts.behavior.completion, line 202, characters 8-20
@unit_service
     : forall (Job : JobType) (PState : ProcessorState Job) (j : Equality.sort Job),
       @unit_service_proc_model Job PState ->
       forall s : @State Job PState, is_true (@service_in Job PState j s <= 1)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.unit_service : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (j : Job),
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (s : Prosa.Behavior.Schedule.ProcessorState.State Job), PState.service_in j s ≤ 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_unit_service
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (j : Job),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall
         s : Prosa_Behavior_Schedule_ProcessorState_State Job
               inst_3 PState,
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Behavior_Schedule_ProcessorState_service_in Job
            inst_3 PState j s)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
```
