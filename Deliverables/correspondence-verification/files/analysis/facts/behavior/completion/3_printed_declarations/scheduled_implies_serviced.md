# `scheduled_implies_serviced`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.completion.scheduled_implies_serviced`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_serviced`
- Certificate: `scheduled_implies_serviced_correspondence`

## Official Rocq

```coq
scheduled_implies_serviced :
forall {Job : JobType} {PState : ProcessorState Job} (j : Equality.sort Job),
@ideal_progress_proc_model Job PState ->
forall s : @State Job PState,
is_true (@scheduled_in Job PState j s) -> is_true (0 < @service_in Job PState j s)

scheduled_implies_serviced is not universe polymorphic
Arguments scheduled_implies_serviced {Job PState} j H_scheduled_implies_serviced s _
scheduled_implies_serviced is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.scheduled_implies_serviced
Declared in library prosa.analysis.facts.behavior.completion, line 123, characters 12-38
@scheduled_implies_serviced
     : forall (Job : JobType) (PState : ProcessorState Job) (j : Equality.sort Job),
       @ideal_progress_proc_model Job PState ->
       forall s : @State Job PState,
       is_true (@scheduled_in Job PState j s) -> is_true (0 < @service_in Job PState j s)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.scheduled_implies_serviced : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job} (j : Job),
  Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
    ∀ (s : Prosa.Behavior.Schedule.ProcessorState.State Job), PState.scheduled_in j s = true → 0 < PState.service_in j s
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_scheduled_implies_serviced
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (j : Job),
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       forall
         s : Prosa_Behavior_Schedule_ProcessorState_State Job
               inst_3 PState,
       @eq Bool
         (Prosa_Behavior_Schedule_ProcessorState_scheduled_in Job
            inst_3 PState j s)
         Bool_true ->
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Schedule_ProcessorState_service_in Job
            inst_3 PState j s)
```
