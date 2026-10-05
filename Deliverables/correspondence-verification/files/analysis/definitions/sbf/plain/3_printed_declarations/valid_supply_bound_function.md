# `valid_supply_bound_function`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.sbf.plain.valid_supply_bound_function`
- Lean: `Prosa.Analysis.Definitions.Sbf.Plain.valid_supply_bound_function`
- Certificate: `plain_valid_supply_bound_function_correspondence`

## Official Rocq

```coq
valid_supply_bound_function :
forall {Job : JobType} {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> (duration -> work) -> Prop

valid_supply_bound_function is not universe polymorphic
Arguments valid_supply_bound_function {Job PState} arr_seq sched SBF%function_scope
valid_supply_bound_function is transparent
Expands to: Constant prosa.analysis.definitions.sbf.plain.valid_supply_bound_function
Declared in library prosa.analysis.definitions.sbf.plain, line 32, characters 13-40
@valid_supply_bound_function
     : forall (Job : JobType) (PState : ProcessorState Job),
       arrival_sequence Job -> @schedule Job PState -> (duration -> work) -> Prop
```

Body:

```coq
valid_supply_bound_function =
fun (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) =>
     : forall {Job : JobType} {PState : ProcessorState Job},
       arrival_sequence Job -> @schedule Job PState -> (duration -> work) -> Prop

Arguments valid_supply_bound_function {Job PState} arr_seq sched SBF%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.Sbf.Plain.valid_supply_bound_function : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState → (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop
def Prosa.Analysis.Definitions.Sbf.Plain.valid_supply_bound_function.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState → (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop :=
fun {Job} [DecidableEq Job] {PState} arr_seq sched SBF =>
  Prosa.Analysis.Definitions.Sbf.Pred.valid_pred_sbf arr_seq sched (fun x x_1 x_2 => True) SBF
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Sbf_Plain_valid_supply_bound_function
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
Prosa_Analysis_Definitions_Sbf_Plain_valid_supply_bound_function@{u_1 u_2 u_3 Lean.u_1+1.0
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
Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf Job
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

Arguments Prosa_Analysis_Definitions_Sbf_Plain_valid_supply_bound_function Job
  inst_3 PState 
  arr_seq sched SBF%_function_scope
```
