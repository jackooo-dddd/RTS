# `ideal_progress_proc_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.platform_properties.ideal_progress_proc_model`
- Lean: `Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model`
- Certificate: `ideal_progress_proc_model_correspondence`

## Official Rocq

```coq
ideal_progress_proc_model : forall {Job : JobType}, ProcessorState Job -> Prop

ideal_progress_proc_model is not universe polymorphic
Arguments ideal_progress_proc_model {Job} PState
ideal_progress_proc_model is transparent
Expands to: Constant prosa.model.processor.platform_properties.ideal_progress_proc_model
Declared in library prosa.model.processor.platform_properties, line 23, characters 13-38
@ideal_progress_proc_model
     : forall Job : JobType, ProcessorState Job -> Prop
```

Body:

```coq
ideal_progress_proc_model =
fun (Job : JobType) (PState : ProcessorState Job) =>
forall (j : Equality.sort Job) (s : @State Job PState),
is_true (@scheduled_in Job PState j s) -> is_true (0 < @service_in Job PState j s)
     : forall {Job : JobType}, ProcessorState Job -> Prop

Arguments ideal_progress_proc_model {Job} PState
```

## Lean

```lean
@Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → Prop
def Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → Prop :=
fun {Job} [DecidableEq Job] PState =>
  ∀ (j : Job) (s : Prosa.Behavior.Schedule.ProcessorState.State Job),
    PState.scheduled_in j s = true → 0 < PState.service_in j s
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3) =>
forall (j : Job)
  (s : Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState),
@eq Bool
  (Prosa_Behavior_Schedule_ProcessorState_scheduled_in Job
     inst_3 PState j s)
  Bool_true ->
LT_lt_inst1 Prosa_Behavior_Job_work instLTNat (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
  (Prosa_Behavior_Schedule_ProcessorState_service_in Job
     inst_3 PState j s)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
  inst_3 PState
```
