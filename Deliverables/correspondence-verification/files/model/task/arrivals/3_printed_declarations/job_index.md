# `job_index`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrivals.job_index`
- Lean: `Prosa.Model.Task.Arrivals.job_index`
- Certificate: `job_index_correspondence`

## Official Rocq

```coq
job_index :
forall {Task : TaskType} {Job : JobType},
JobArrival Job -> JobTask Job Task -> arrival_sequence Job -> Equality.sort Job -> nat

job_index is not universe polymorphic
Arguments job_index {Task Job H H0} arr_seq j
job_index is transparent
Expands to: Constant prosa.model.task.arrivals.job_index
Declared in library prosa.model.task.arrivals, line 113, characters 13-22
@job_index
     : forall (Task : TaskType) (Job : JobType),
       JobArrival Job -> JobTask Job Task -> arrival_sequence Job -> Equality.sort Job -> nat
```

Body:

```coq
job_index =
fun (Task : TaskType) (Job : JobType) (H : JobArrival Job) (H0 : JobTask Job Task)
  (arr_seq : arrival_sequence Job) (j : Equality.sort Job) =>
@index Job j (@task_arrivals_up_to_job_arrival Job Task H0 H arr_seq j)
     : forall {Task : TaskType} {Job : JobType},
       JobArrival Job -> JobTask Job Task -> arrival_sequence Job -> Equality.sort Job -> nat

Arguments job_index {Task Job H H0} arr_seq j
```

## Lean

```lean
@Prosa.Model.Task.Arrivals.job_index : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Job → ℕ
def Prosa.Model.Task.Arrivals.job_index.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Job → ℕ :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] arr_seq j =>
  List.idxOf j (Prosa.Model.Task.Arrivals.task_arrivals_up_to_job_arrival arr_seq j)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrivals_job_index
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_7 ->
       Prosa_Model_Task_Concept_JobTask Job inst_7
         Task inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Job -> Nat
```

Body:

```coq
Prosa_Model_Task_Arrivals_job_index@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0
Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : Prosa_Behavior_Job_JobArrival Job
                                                                       inst_7)
  (inst_13 : Prosa_Model_Task_Concept_JobTask Job
                                                                       inst_7
                                                                       Task
                                                                       inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (j : Job) =>
List_idxOf Job (instBEqOfDecidableEq Job inst_7) j
  (Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job
     inst_7 Task
     inst_3
     inst_13
     inst_10 arr_seq j)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_7 ->
       Prosa_Model_Task_Concept_JobTask Job inst_7
         Task inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Job -> Nat

Arguments Prosa_Model_Task_Arrivals_job_index Task
  inst_3 Job
  inst_7
  inst_10
  inst_13 arr_seq j
```
