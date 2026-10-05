# `valid_fixed_preemption_points_task_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.limited_preemptive.valid_fixed_preemption_points_task_model`
- Lean: `Prosa.Model.Task.Preemption.LimitedPreemptive.valid_fixed_preemption_points_task_model`
- Certificate: `valid_fixed_preemption_points_task_model_correspondence`

## Official Rocq

```coq
valid_fixed_preemption_points_task_model :
forall {Task : TaskType},
TaskCost Task ->
TaskPreemptionPoints Task ->
forall {Job : JobType},
JobTask Job Task -> JobPreemptionPoints Job -> arrival_sequence Job -> TaskSet (Equality.sort Task) -> Prop

valid_fixed_preemption_points_task_model is not universe polymorphic
Arguments valid_fixed_preemption_points_task_model {Task H H0 Job H1 H4} arr_seq ts
valid_fixed_preemption_points_task_model is transparent
Expands to: Constant prosa.model.task.preemption.limited_preemptive.valid_fixed_preemption_points_task_model
Declared in library prosa.model.task.preemption.limited_preemptive, line 78, characters 13-53
@valid_fixed_preemption_points_task_model
     : forall Task : TaskType,
       TaskCost Task ->
       TaskPreemptionPoints Task ->
       forall Job : JobType,
       JobTask Job Task ->
       JobPreemptionPoints Job -> arrival_sequence Job -> TaskSet (Equality.sort Task) -> Prop
```

Body:

```coq
valid_fixed_preemption_points_task_model =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskPreemptionPoints Task) (Job : JobType)
  (H1 : JobTask Job Task) (H4 : JobPreemptionPoints Job) (arr_seq : arrival_sequence Job)
  (ts : TaskSet (Equality.sort Task)) =>
@task_beginning_of_execution_in_preemption_points Task H0 ts /\
@task_end_of_execution_in_preemption_points Task H H0 ts /\
@nondecreasing_task_preemption_points Task H0 ts /\
@consistent_job_segment_count Task H0 Job H1 H4 arr_seq /\
@job_respects_segment_lengths Task H0 Job H1 H4 arr_seq /\ @task_segments_are_nonempty Task H0 ts
     : forall {Task : TaskType},
       TaskCost Task ->
       TaskPreemptionPoints Task ->
       forall {Job : JobType},
       JobTask Job Task ->
       JobPreemptionPoints Job -> arrival_sequence Job -> TaskSet (Equality.sort Task) -> Prop

Arguments valid_fixed_preemption_points_task_model {Task H H0 Job H1 H4} arr_seq ts
```

## Lean

```lean
@Prosa.Model.Task.Preemption.LimitedPreemptive.valid_fixed_preemption_points_task_model : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst_3 : DecidableEq Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Model.Task.Concept.TaskSet Task → Prop
```

Body:

```lean
def Prosa.Model.Task.Preemption.LimitedPreemptive.valid_fixed_preemption_points_task_model.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst_3 : DecidableEq Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Model.Task.Concept.TaskSet Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
    arr_seq ts =>
  Prosa.Model.Task.Preemption.LimitedPreemptive.task_beginning_of_execution_in_preemption_points ts ∧
    Prosa.Model.Task.Preemption.LimitedPreemptive.task_end_of_execution_in_preemption_points ts ∧
      Prosa.Model.Task.Preemption.LimitedPreemptive.nondecreasing_task_preemption_points ts ∧
        Prosa.Model.Task.Preemption.LimitedPreemptive.consistent_job_segment_count arr_seq ∧
          Prosa.Model.Task.Preemption.LimitedPreemptive.job_respects_segment_lengths arr_seq ∧
            Prosa.Model.Task.Preemption.LimitedPreemptive.task_segments_are_nonempty ts
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_LimitedPreemptive_valid_fixed_preemption_points_task_model
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
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
       Prosa_Model_Task_Concept_TaskSet Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Preemption_LimitedPreemptive_valid_fixed_preemption_points_task_model@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
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
               inst_13)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) =>
And
  (Prosa_Model_Task_Preemption_LimitedPreemptive_task_beginning_of_execution_in_preemption_points Task
     inst_3
     inst_9 ts)
  (And
     (Prosa_Model_Task_Preemption_LimitedPreemptive_task_end_of_execution_in_preemption_points Task
        inst_3
        inst_6
        inst_9 ts)
     (And
        (Prosa_Model_Task_Preemption_LimitedPreemptive_nondecreasing_task_preemption_points Task
           inst_3
           inst_9 ts)
        (And
           (Prosa_Model_Task_Preemption_LimitedPreemptive_consistent_job_segment_count Task
              inst_3
              inst_9 Job
              inst_13
              inst_16
              inst_26 arr_seq)
           (And
              (Prosa_Model_Task_Preemption_LimitedPreemptive_job_respects_segment_lengths Task
                 inst_3
                 inst_9 Job
                 inst_13
                 inst_16
                 inst_26 arr_seq)
              (Prosa_Model_Task_Preemption_LimitedPreemptive_task_segments_are_nonempty Task
                 inst_3
                 inst_9 ts)))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
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
       Prosa_Model_Task_Concept_TaskSet Task -> SProp

Arguments Prosa_Model_Task_Preemption_LimitedPreemptive_valid_fixed_preemption_points_task_model 
  Task inst_3
  inst_6
  inst_9 
  Job inst_13
  inst_16
  inst_26 
  arr_seq ts
```
