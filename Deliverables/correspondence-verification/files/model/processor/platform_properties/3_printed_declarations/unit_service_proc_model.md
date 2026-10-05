# `unit_service_proc_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.platform_properties.unit_service_proc_model`
- Lean: `Prosa.Model.Processor.PlatformProperties.unit_service_proc_model`
- Certificate: `unit_service_proc_model_correspondence`

## Official Rocq

```coq
unit_service_proc_model : forall {Job : JobType}, ProcessorState Job -> Prop

unit_service_proc_model is not universe polymorphic
Arguments unit_service_proc_model {Job} PState
unit_service_proc_model is transparent
Expands to: Constant prosa.model.processor.platform_properties.unit_service_proc_model
Declared in library prosa.model.processor.platform_properties, line 18, characters 13-36
@unit_service_proc_model
     : forall Job : JobType, ProcessorState Job -> Prop
```

Body:

```coq
unit_service_proc_model =
fun (Job : JobType) (PState : ProcessorState Job) =>
forall (j : Equality.sort Job) (s : @State Job PState), is_true (@service_in Job PState j s <= 1)
     : forall {Job : JobType}, ProcessorState Job -> Prop

Arguments unit_service_proc_model {Job} PState
```

## Lean

```lean
@Prosa.Model.Processor.PlatformProperties.unit_service_proc_model : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → Prop
def Prosa.Model.Processor.PlatformProperties.unit_service_proc_model.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → Prop :=
fun {Job} [DecidableEq Job] PState =>
  ∀ (j : Job) (s : Prosa.Behavior.Schedule.ProcessorState.State Job), PState.service_in j s ≤ 1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_PlatformProperties_unit_service_proc_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Processor_PlatformProperties_unit_service_proc_model@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3) =>
forall (j : Job)
  (s : Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState),
LE_le_inst1 Prosa_Behavior_Job_work instLENat
  (Prosa_Behavior_Schedule_ProcessorState_service_in Job
     inst_3 PState j s)
  (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
  inst_3 PState
```
