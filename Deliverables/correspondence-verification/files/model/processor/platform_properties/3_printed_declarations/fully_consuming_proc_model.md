# `fully_consuming_proc_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.platform_properties.fully_consuming_proc_model`
- Lean: `Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model`
- Certificate: `fully_consuming_proc_model_correspondence`

## Official Rocq

```coq
fully_consuming_proc_model : forall {Job : JobType}, ProcessorState Job -> Prop

fully_consuming_proc_model is not universe polymorphic
Arguments fully_consuming_proc_model {Job} PState
fully_consuming_proc_model is transparent
Expands to: Constant prosa.model.processor.platform_properties.fully_consuming_proc_model
Declared in library prosa.model.processor.platform_properties, line 56, characters 13-39
@fully_consuming_proc_model
     : forall Job : JobType, ProcessorState Job -> Prop
```

Body:

```coq
fully_consuming_proc_model =
fun (Job : JobType) (PState : ProcessorState Job) =>
forall (j : Equality.sort Job) (s : @schedule Job PState) (t : instant),
is_true (@scheduled_at Job PState s j t) -> @service_at Job PState s j t = @supply_at Job PState s t
     : forall {Job : JobType}, ProcessorState Job -> Prop

Arguments fully_consuming_proc_model {Job} PState
```

## Lean

```lean
@Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → Prop
def Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → Prop :=
fun {Job} [DecidableEq Job] PState =>
  ∀ (j : Job) (sched : Prosa.Behavior.Schedule.schedule PState) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Service.scheduled_at sched j t = true →
      Prosa.Behavior.Service.service_at sched j t = Prosa.Model.Processor.Supply.supply_at sched t
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3) =>
forall (j : Job)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (t : Prosa_Behavior_Time_instant),
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job
     inst_3 PState sched j t)
  Bool_true ->
@eq Prosa_Behavior_Job_work
  (Prosa_Behavior_Service_service_at Job
     inst_3 PState sched j t)
  (Prosa_Model_Processor_Supply_supply_at Job
     inst_3 PState sched t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
  inst_3 PState
```
