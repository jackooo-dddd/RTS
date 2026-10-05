# `consistent_job_segment_count`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.limited_preemptive.consistent_job_segment_count`
- Lean: `Prosa.Model.Task.Preemption.LimitedPreemptive.consistent_job_segment_count`
- Certificate: `consistent_job_segment_count_correspondence`

## Official Rocq

```coq
consistent_job_segment_count :
forall {Task : TaskType},
TaskPreemptionPoints Task ->
forall {Job : JobType}, JobTask Job Task -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop

consistent_job_segment_count is not universe polymorphic
Arguments consistent_job_segment_count {Task H0 Job H1 H4} arr_seq
consistent_job_segment_count is transparent
Expands to: Constant prosa.model.task.preemption.limited_preemptive.consistent_job_segment_count
Declared in library prosa.model.task.preemption.limited_preemptive, line 56, characters 13-41
@consistent_job_segment_count
     : forall Task : TaskType,
       TaskPreemptionPoints Task ->
       forall Job : JobType, JobTask Job Task -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop
```

Body:

```coq
consistent_job_segment_count =
fun (Task : TaskType) (H0 : TaskPreemptionPoints Task) (Job : JobType) (H1 : JobTask Job Task)
  (H4 : JobPreemptionPoints Job) (arr_seq : arrival_sequence Job) =>
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
@size work (@job_preemptive_points Job H4 j) =
@size work (@task_preemption_points Task H0 (@job_task Job Task H1 j))
     : forall {Task : TaskType},
       TaskPreemptionPoints Task ->
       forall {Job : JobType}, JobTask Job Task -> JobPreemptionPoints Job -> arrival_sequence Job -> Prop

Arguments consistent_job_segment_count {Task H0 Job H1 H4} arr_seq
```

## Lean

```lean
@Prosa.Model.Task.Preemption.LimitedPreemptive.consistent_job_segment_count : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
```

Body:

```lean
def Prosa.Model.Task.Preemption.LimitedPreemptive.consistent_job_segment_count.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
    arr_seq =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      (Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j).length =
        (Prosa.Model.Task.Preemption.Parameters.task_preemption_points (Prosa.Model.Task.Concept.job_task j)).length
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_LimitedPreemptive_consistent_job_segment_count
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_13 Task
         inst_3 ->
       Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
         inst_13 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_13 ->
       SProp
```

Body:

```coq
Prosa_Model_Task_Preemption_LimitedPreemptive_consistent_job_segment_count@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_9 : 
   Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
     inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_13 : DecidableEq Job)
  (inst_16 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_13 Task
     inst_3)
  (inst_26 : 
   Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
     inst_13)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_13) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_13 arr_seq j ->
@eq Nat
  (List_length_inst1 Prosa_Behavior_Job_work
     (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
        inst_13
        inst_26 j))
  (List_length_inst1 Prosa_Behavior_Job_work
     (Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_task_preemption_points Task
        inst_3
        inst_9
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_13 Task
           inst_3
           inst_16 j)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_13 Task
         inst_3 ->
       Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
         inst_13 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_13 ->
       SProp

Arguments Prosa_Model_Task_Preemption_LimitedPreemptive_consistent_job_segment_count 
  Task inst_3
  inst_9 
  Job inst_13
  inst_16
  inst_26 
  arr_seq
```
