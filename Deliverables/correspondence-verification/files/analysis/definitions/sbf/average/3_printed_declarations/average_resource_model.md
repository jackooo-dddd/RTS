# `average_resource_model`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.sbf.average.average_resource_model`
- Lean: `Prosa.Analysis.Definitions.Sbf.Average.average_resource_model`
- Certificate: `average_resource_model_correspondence`

## Official Rocq

```coq
average_resource_model :
forall {Job : JobType} {PState : ProcessorState Job},
duration -> duration -> duration -> @schedule Job PState -> Prop

average_resource_model is not universe polymorphic
Arguments average_resource_model {Job PState} Π Θ ν sched
average_resource_model is transparent
Expands to: Constant prosa.analysis.definitions.sbf.average.average_resource_model
Declared in library prosa.analysis.definitions.sbf.average, line 26, characters 13-35
@average_resource_model
     : forall (Job : JobType) (PState : ProcessorState Job),
       duration -> duration -> duration -> @schedule Job PState -> Prop
```

Body:

```coq
average_resource_model =
fun (Job : JobType) (PState : ProcessorState Job) (Π Θ ν : duration) (sched : @schedule Job PState) =>
is_true (Θ <= Π) /\
(forall t1 t2 : duration,
 is_true (let Δ := t2 - t1 in ((Δ - ν) * Θ) %/ Π <= @supply_during Job PState sched t1 t2))
     : forall {Job : JobType} {PState : ProcessorState Job},
       duration -> duration -> duration -> @schedule Job PState -> Prop

Arguments average_resource_model {Job PState} Π Θ ν sched
```

## Lean

```lean
@Prosa.Analysis.Definitions.Sbf.Average.average_resource_model : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Time.duration →
        Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Schedule.schedule PState → Prop
def Prosa.Analysis.Definitions.Sbf.Average.average_resource_model.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Time.duration →
        Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Job} [DecidableEq Job] {PState} period allocation delay sched =>
  period ≥ allocation ∧
    ∀ (t1 t2 : Prosa.Behavior.Time.duration),
      Prosa.Model.Processor.Supply.supply_during sched t1 t2 ≥ (t2 - t1 - delay) * allocation / period
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Sbf_Average_average_resource_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Sbf_Average_average_resource_model@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (period allocation delay : Prosa_Behavior_Time_duration)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState) =>
And (GE_ge_inst1 Prosa_Behavior_Time_duration instLENat period allocation)
  (forall t1 t2 : Prosa_Behavior_Time_duration,
   GE_ge_inst1 Prosa_Behavior_Job_work instLENat
     (Prosa_Model_Processor_Supply_supply_during Job
        inst_3 PState sched t1 t2)
     (HDiv_hDiv_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
        (instHDiv_inst1 Prosa_Behavior_Time_duration Nat_instDiv)
        (HMul_hMul_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
           Prosa_Behavior_Time_duration (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
           (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
              Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
              (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                 Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) t2 t1)
              delay)
           allocation)
        period))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp

Arguments Prosa_Analysis_Definitions_Sbf_Average_average_resource_model Job
  inst_3 PState 
  period allocation delay sched
```
