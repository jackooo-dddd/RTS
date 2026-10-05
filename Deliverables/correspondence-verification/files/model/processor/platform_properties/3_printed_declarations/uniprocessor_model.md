# `uniprocessor_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.platform_properties.uniprocessor_model`
- Lean: `Prosa.Model.Processor.PlatformProperties.uniprocessor_model`
- Certificate: `uniprocessor_model_correspondence`

## Official Rocq

```coq
uniprocessor_model : forall {Job : JobType}, ProcessorState Job -> Prop

uniprocessor_model is not universe polymorphic
Arguments uniprocessor_model {Job} PState
uniprocessor_model is transparent
Expands to: Constant prosa.model.processor.platform_properties.uniprocessor_model
Declared in library prosa.model.processor.platform_properties, line 28, characters 13-31
@uniprocessor_model
     : forall Job : JobType, ProcessorState Job -> Prop
```

Body:

```coq
uniprocessor_model =
fun (Job : JobType) (PState : ProcessorState Job) =>
forall (j1 j2 : Equality.sort Job) (s : @schedule Job PState) (t : instant),
is_true (@scheduled_at Job PState s j1 t) -> is_true (@scheduled_at Job PState s j2 t) -> j1 = j2
     : forall {Job : JobType}, ProcessorState Job -> Prop

Arguments uniprocessor_model {Job} PState
```

## Lean

```lean
@Prosa.Model.Processor.PlatformProperties.uniprocessor_model : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → Prop
def Prosa.Model.Processor.PlatformProperties.uniprocessor_model.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → Prop :=
fun {Job} [DecidableEq Job] PState =>
  ∀ (j1 j2 : Job) (sched : Prosa.Behavior.Schedule.schedule PState) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Service.scheduled_at sched j1 t = true →
      Prosa.Behavior.Service.scheduled_at sched j2 t = true → j1 = j2
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_PlatformProperties_uniprocessor_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Processor_PlatformProperties_uniprocessor_model@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3) =>
forall (j1 j2 : Job)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (t : Prosa_Behavior_Time_instant),
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job
     inst_3 PState sched j1 t)
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job
     inst_3 PState sched j2 t)
  Bool_true ->
@eq Job j1 j2
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
  inst_3 PState
```
