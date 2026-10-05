# `prev_job`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrivals.prev_job`
- Lean: `Prosa.Model.Task.Arrivals.prev_job`
- Certificate: `prev_job_correspondence`

## Official Rocq

```coq
prev_job :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Job -> Equality.sort Job

prev_job is not universe polymorphic
Arguments prev_job {Job Task H H0} arr_seq j
prev_job is transparent
Expands to: Constant prosa.model.task.arrivals.prev_job
Declared in library prosa.model.task.arrivals, line 136, characters 13-21
@prev_job
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Job -> Equality.sort Job
```

Body:

```coq
prev_job =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
  (arr_seq : arrival_sequence Job) =>
let task_arrivals_up_to_job_arrival := [eta @task_arrivals_up_to_job_arrival Job Task H H0 arr_seq] in
let prev_index := fun j : Equality.sort Job => @job_index Task Job H0 H arr_seq j - 1 in
fun j : Equality.sort Job => @nth (Equality.sort Job) j (task_arrivals_up_to_job_arrival j) (prev_index j)
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Job -> Equality.sort Job

Arguments prev_job {Job Task H H0} arr_seq j
```

## Lean

```lean
@Prosa.Model.Task.Arrivals.prev_job : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Job → Job
def Prosa.Model.Task.Arrivals.prev_job.{u_1, u_2} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Job → Job :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobArrival Job] arr_seq j =>
  (Prosa.Model.Task.Arrivals.task_arrivals_up_to_job_arrival arr_seq j).getD
    (Prosa.Model.Task.Arrivals.job_index arr_seq j - 1) j
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrivals_prev_job
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Job -> Job
```

Body:

```coq
Prosa_Model_Task_Arrivals_prev_job@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0
Lean.u_2+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (inst_10 : Prosa_Model_Task_Concept_JobTask Job
                                                                       inst_3
                                                                       Task
                                                                       inst_7)
  (inst_14 : Prosa_Behavior_Job_JobArrival Job
                                                                       inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (j : Job) =>
List_getD Job
  (Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job
     inst_3 Task
     inst_7
     inst_10
     inst_14 arr_seq j)
  (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
     (Prosa_Model_Task_Arrivals_job_index Task inst_7
        Job inst_3
        inst_14
        inst_10 arr_seq j)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
  j
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Job -> Job

Arguments Prosa_Model_Task_Arrivals_prev_job Job
  inst_3 Task
  inst_7
  inst_10
  inst_14 arr_seq j
```
