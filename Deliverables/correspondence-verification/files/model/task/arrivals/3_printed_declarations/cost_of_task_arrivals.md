# `cost_of_task_arrivals`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrivals.cost_of_task_arrivals`
- Lean: `Prosa.Model.Task.Arrivals.cost_of_task_arrivals`
- Certificate: `cost_of_task_arrivals_correspondence`

## Official Rocq

```coq
cost_of_task_arrivals :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task -> JobCost Job -> arrival_sequence Job -> Equality.sort Task -> instant -> instant -> nat

cost_of_task_arrivals is not universe polymorphic
Arguments cost_of_task_arrivals {Job Task H H1} arr_seq tsk t1 t2
cost_of_task_arrivals is transparent
Expands to: Constant prosa.model.task.arrivals.cost_of_task_arrivals
Declared in library prosa.model.task.arrivals, line 45, characters 13-34
@cost_of_task_arrivals
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task ->
       JobCost Job -> arrival_sequence Job -> Equality.sort Task -> instant -> instant -> nat
```

Body:

```coq
cost_of_task_arrivals =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H1 : JobCost Job)
  (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task) (t1 t2 : instant) =>
\sum_(j <- @task_arrivals_between Job Task H arr_seq tsk t1 t2) @job_cost Job H1 j
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task ->
       JobCost Job -> arrival_sequence Job -> Equality.sort Task -> instant -> instant -> nat

Arguments cost_of_task_arrivals {Job Task H H1} arr_seq tsk t1 t2
```

## Lean

```lean
@Prosa.Model.Task.Arrivals.cost_of_task_arrivals : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Task → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
def Prosa.Model.Task.Arrivals.cost_of_task_arrivals.{u_1, u_2} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Task → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobCost Job] arr_seq tsk t1 t2 =>
  (List.map Prosa.Behavior.Job.job_cost (Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 t2)).sum
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrivals_cost_of_task_arrivals
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Task -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Model_Task_Arrivals_cost_of_task_arrivals@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (inst_10 : Prosa_Model_Task_Concept_JobTask Job
                                                                       inst_3
                                                                       Task
                                                                       inst_7)
  (inst_17 : Prosa_Behavior_Job_JobCost Job
                                                                       inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (tsk : Task) (t1 t2 : Prosa_Behavior_Time_instant) =>
List_sum_inst1 Prosa_Behavior_Job_work instAddNat
  (MulZeroClass_toZero_inst1 Prosa_Behavior_Job_work Nat_instMulZeroClass)
  (List_map_inst2 Job Prosa_Behavior_Job_work
     (Prosa_Behavior_Job_JobCost_job_cost Job inst_3
        inst_17)
     (Prosa_Model_Task_Arrivals_task_arrivals_between Job
        inst_3 Task
        inst_7
        inst_10 arr_seq tsk t1 t2))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Task -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Model_Task_Arrivals_cost_of_task_arrivals Job
  inst_3 Task
  inst_7
  inst_10
  inst_17 arr_seq tsk t1 
  t2
```
