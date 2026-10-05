# `supply_bound_function_respected`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.sbf.plain.supply_bound_function_respected`
- Lean: `Prosa.Analysis.Definitions.Sbf.Plain.supply_bound_function_respected`
- Certificate: `plain_supply_bound_function_respected_correspondence`

## Official Rocq

```coq
supply_bound_function_respected :
forall {Job : JobType} {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> (duration -> work) -> Prop

supply_bound_function_respected is not universe polymorphic
Arguments supply_bound_function_respected {Job PState} arr_seq sched SBF%function_scope
supply_bound_function_respected is transparent
Expands to: Constant prosa.analysis.definitions.sbf.plain.supply_bound_function_respected
Declared in library prosa.analysis.definitions.sbf.plain, line 27, characters 13-44
@supply_bound_function_respected
     : forall (Job : JobType) (PState : ProcessorState Job),
       arrival_sequence Job -> @schedule Job PState -> (duration -> work) -> Prop
```

Body:

```coq
supply_bound_function_respected =
fun (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) =>
     : forall {Job : JobType} {PState : ProcessorState Job},
       arrival_sequence Job -> @schedule Job PState -> (duration -> work) -> Prop

Arguments supply_bound_function_respected {Job PState} arr_seq sched SBF%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.Sbf.Plain.supply_bound_function_respected : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState → (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop
def Prosa.Analysis.Definitions.Sbf.Plain.supply_bound_function_respected.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState → (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop :=
fun {Job} [DecidableEq Job] {PState} arr_seq sched SBF =>
  Prosa.Analysis.Definitions.Sbf.Pred.pred_sbf_respected arr_seq sched (fun x x_1 x_2 => True) SBF
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Sbf_Plain_supply_bound_function_respected
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Sbf_Plain_supply_bound_function_respected@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (SBF : Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) =>
Prosa_Analysis_Definitions_Sbf_Pred_pred_sbf_respected Job
  inst_3 PState arr_seq sched
  (fun (_ : Job) (_ _ : Prosa_Behavior_Time_instant) => True) SBF
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp

Arguments Prosa_Analysis_Definitions_Sbf_Plain_supply_bound_function_respected Job
  inst_3 PState 
  arr_seq sched SBF%_function_scope
```
