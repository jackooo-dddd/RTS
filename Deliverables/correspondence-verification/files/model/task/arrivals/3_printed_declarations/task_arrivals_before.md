# `task_arrivals_before`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrivals.task_arrivals_before`
- Lean: `Prosa.Model.Task.Arrivals.task_arrivals_before`
- Certificate: `task_arrivals_before_correspondence`

## Official Rocq

```coq
task_arrivals_before :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> instant -> seq (Equality.sort Job)

task_arrivals_before is not universe polymorphic
Arguments task_arrivals_before {Job Task H} arr_seq tsk t
task_arrivals_before is transparent
Expands to: Constant prosa.model.task.arrivals.task_arrivals_before
Declared in library prosa.model.task.arrivals, line 33, characters 13-33
@task_arrivals_before
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> instant -> seq (Equality.sort Job)
```

Body:

```coq
task_arrivals_before =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) =>
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> instant -> seq (Equality.sort Job)

Arguments task_arrivals_before {Job Task H} arr_seq tsk t
```

## Lean

```lean
@Prosa.Model.Task.Arrivals.task_arrivals_before : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prosa.Behavior.Time.instant → List Job
def Prosa.Model.Task.Arrivals.task_arrivals_before.{u_1, u_2} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prosa.Behavior.Time.instant → List Job :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task] arr_seq tsk t =>
  Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk 0 t
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrivals_task_arrivals_before
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
Prosa_Model_Task_Arrivals_task_arrivals_before@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
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
Prosa_Model_Task_Arrivals_task_arrivals_between Job
  inst_3 Task
  inst_7
  inst_10 arr_seq tsk
  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Task -> Prosa_Behavior_Time_instant -> List Job

Arguments Prosa_Model_Task_Arrivals_task_arrivals_before Job
  inst_3 Task
  inst_7
  inst_10 arr_seq tsk t
```
