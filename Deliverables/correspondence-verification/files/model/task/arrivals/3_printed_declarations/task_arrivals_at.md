# `task_arrivals_at`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrivals.task_arrivals_at`
- Lean: `Prosa.Model.Task.Arrivals.task_arrivals_at`
- Certificate: `task_arrivals_at_correspondence`

## Official Rocq

```coq
task_arrivals_at :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> instant -> seq (Equality.sort Job)

task_arrivals_at is not universe polymorphic
Arguments task_arrivals_at {Job Task H} arr_seq tsk t
task_arrivals_at is transparent
Expands to: Constant prosa.model.task.arrivals.task_arrivals_at
Declared in library prosa.model.task.arrivals, line 37, characters 13-29
@task_arrivals_at
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> instant -> seq (Equality.sort Job)
```

Body:

```coq
task_arrivals_at =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (t : instant) =>
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> instant -> seq (Equality.sort Job)

Arguments task_arrivals_at {Job Task H} arr_seq tsk t
```

## Lean

```lean
@Prosa.Model.Task.Arrivals.task_arrivals_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prosa.Behavior.Time.instant → List Job
def Prosa.Model.Task.Arrivals.task_arrivals_at.{u_1, u_2} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prosa.Behavior.Time.instant → List Job :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task] arr_seq tsk t =>
  List.filter (Prosa.Model.Task.Concept.job_of_task tsk) (Prosa.Behavior.Arrival_sequence.arrivals_at arr_seq t)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrivals_task_arrivals_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Task -> Prosa_Behavior_Time_instant -> List Job
```

Body:

```coq
Prosa_Model_Task_Arrivals_task_arrivals_at@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (inst_10 : Prosa_Model_Task_Concept_JobTask Job
                                                                       inst_3
                                                                       Task
                                                                       inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (tsk : Task) (t : Prosa_Behavior_Time_instant) =>
List_filter Job
  (Prosa_Model_Task_Concept_job_of_task Job inst_3
     Task inst_7
     inst_10 tsk)
  (Prosa_Behavior_Arrival_sequence_arrivals_at Job
     inst_3 arr_seq t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Task -> Prosa_Behavior_Time_instant -> List Job

Arguments Prosa_Model_Task_Arrivals_task_arrivals_at Job
  inst_3 Task
  inst_7
  inst_10 arr_seq tsk t
```
