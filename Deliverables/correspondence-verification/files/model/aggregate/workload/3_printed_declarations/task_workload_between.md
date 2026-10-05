# `task_workload_between`

- Kind (Rocq): Definition
- Rocq: `prosa.model.aggregate.workload.task_workload_between`
- Lean: `Prosa.Model.Aggregate.Workload.task_workload_between`
- Certificate: `task_workload_between_correspondence`

## Official Rocq

```coq
task_workload_between :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task -> JobCost Job -> arrival_sequence Job -> Equality.sort Task -> instant -> instant -> nat

task_workload_between is not universe polymorphic
Arguments task_workload_between {Task Job H0 H1} arr_seq tsk t1 t2
task_workload_between is transparent
Expands to: Constant prosa.model.aggregate.workload.task_workload_between
Declared in library prosa.model.aggregate.workload, line 31, characters 13-34
@task_workload_between
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       JobCost Job -> arrival_sequence Job -> Equality.sort Task -> instant -> instant -> nat
```

Body:

```coq
task_workload_between =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobCost Job)
  (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task) (t1 t2 : instant) =>
@task_workload Task Job H0 H1 tsk (@arrivals_between Job arr_seq t1 t2)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       JobCost Job -> arrival_sequence Job -> Equality.sort Task -> instant -> instant -> nat

Arguments task_workload_between {Task Job H0 H1} arr_seq tsk t1 t2
```

## Lean

```lean
@Prosa.Model.Aggregate.Workload.task_workload_between : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Task → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Model.Aggregate.Workload.task_workload_between.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Task → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobCost Job] arr_seq tsk t1 t2 =>
  Prosa.Model.Aggregate.Workload.task_workload tsk (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Aggregate_Workload_task_workload_between
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Task -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Model_Aggregate_Workload_task_workload_between@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                            Job
                                                                            inst_7
                                                                            Task
                                                                            inst_3)
  (inst_14 : Prosa_Behavior_Job_JobCost Job
                                                                            inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (tsk : Task) (t1 t2 : Prosa_Behavior_Time_instant) =>
Prosa_Model_Aggregate_Workload_task_workload Task
  inst_3 Job
  inst_7
  inst_10
  inst_14 tsk
  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
     inst_7 arr_seq t1 t2)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Task -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Model_Aggregate_Workload_task_workload_between Task
  inst_3 Job
  inst_7
  inst_10
  inst_14 arr_seq tsk 
  t1 t2
```
