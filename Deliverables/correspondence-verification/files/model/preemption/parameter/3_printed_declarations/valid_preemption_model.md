# `valid_preemption_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.parameter.valid_preemption_model`
- Lean: `Prosa.Model.Preemption.Parameter.valid_preemption_model`
- Certificate: `valid_preemption_model_correspondence`

## Official Rocq

```coq
valid_preemption_model :
forall {Job : JobType},
JobCost Job ->
JobPreemptable Job ->
forall {PState : ProcessorState Job}, arrival_sequence Job -> @schedule Job PState -> Prop

valid_preemption_model is not universe polymorphic
Arguments valid_preemption_model {Job H0 H1 PState} arr_seq sched
valid_preemption_model is transparent
Expands to: Constant prosa.model.preemption.parameter.valid_preemption_model
Declared in library prosa.model.preemption.parameter, line 127, characters 13-35
@valid_preemption_model
     : forall Job : JobType,
       JobCost Job ->
       JobPreemptable Job ->
       forall PState : ProcessorState Job, arrival_sequence Job -> @schedule Job PState -> Prop
```

Body:

```coq
valid_preemption_model =
fun (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptable Job) (PState : ProcessorState Job)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) =>
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cannot_become_nonpreemptive_before_execution Job H1 j) /\
is_true (@job_cannot_be_nonpreemptive_after_completion Job H0 H1 j) /\
@not_preemptive_implies_scheduled Job H1 PState sched j /\
@execution_starts_with_preemption_point Job H1 PState sched j
     : forall {Job : JobType},
       JobCost Job ->
       JobPreemptable Job ->
       forall {PState : ProcessorState Job}, arrival_sequence Job -> @schedule Job PState -> Prop

Arguments valid_preemption_model {Job H0 H1 PState} arr_seq sched
```

## Lean

```lean
@Prosa.Model.Preemption.Parameter.valid_preemption_model : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Schedule.schedule PState → Prop
```

Body:

```lean
def Prosa.Model.Preemption.Parameter.valid_preemption_model.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Preemption.Parameter.JobPreemptable Job]
    {PState} arr_seq sched =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      Prosa.Model.Preemption.Parameter.job_cannot_become_nonpreemptive_before_execution j = true ∧
        Prosa.Model.Preemption.Parameter.job_cannot_be_nonpreemptive_after_completion j = true ∧
          Prosa.Model.Preemption.Parameter.not_preemptive_implies_scheduled sched j ∧
            Prosa.Model.Preemption.Parameter.execution_starts_with_preemption_point sched j
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_Parameter_valid_preemption_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp
```

Body:

```coq
Prosa_Model_Preemption_Parameter_valid_preemption_model@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                             inst_3)
  (inst_9 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                             Job
                                                                             inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq j ->
And
  (@eq Bool
     (Prosa_Model_Preemption_Parameter_job_cannot_become_nonpreemptive_before_execution Job
        inst_3
        inst_9 j)
     Bool_true)
  (And
     (@eq Bool
        (Prosa_Model_Preemption_Parameter_job_cannot_be_nonpreemptive_after_completion Job
           inst_3
           inst_6
           inst_9 j)
        Bool_true)
     (And
        (Prosa_Model_Preemption_Parameter_not_preemptive_implies_scheduled Job
           inst_3
           inst_9 PState sched j)
        (Prosa_Model_Preemption_Parameter_execution_starts_with_preemption_point Job
           inst_3
           inst_9 PState sched j)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp

Arguments Prosa_Model_Preemption_Parameter_valid_preemption_model Job
  inst_3
  inst_6
  inst_9 PState arr_seq 
  sched
```
