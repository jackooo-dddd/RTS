# `task_arrivals_up_to`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrivals.task_arrivals_up_to`
- Lean: `Prosa.Model.Task.Arrivals.task_arrivals_up_to`
- Certificate: `task_arrivals_up_to_correspondence`

## Official Rocq

```coq
task_arrivals_up_to :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> instant -> seq (Equality.sort Job)

task_arrivals_up_to is not universe polymorphic
Arguments task_arrivals_up_to {Job Task H} arr_seq tsk t
task_arrivals_up_to is transparent
Expands to: Constant prosa.model.task.arrivals.task_arrivals_up_to
Declared in library prosa.model.task.arrivals, line 28, characters 13-32
@task_arrivals_up_to
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> instant -> seq (Equality.sort Job)
```

Body:

```coq
task_arrivals_up_to =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (t : instant) =>
@task_arrivals_between Job Task H arr_seq tsk 0 t.+1
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> instant -> seq (Equality.sort Job)

Arguments task_arrivals_up_to {Job Task H} arr_seq tsk t
```

## Lean

```lean
@Prosa.Model.Task.Arrivals.task_arrivals_up_to : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prosa.Behavior.Time.instant → List Job
def Prosa.Model.Task.Arrivals.task_arrivals_up_to.{u_1, u_2} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prosa.Behavior.Time.instant → List Job :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task] arr_seq tsk t =>
  Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk 0 (t + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrivals_task_arrivals_up_to
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
Prosa_Model_Task_Arrivals_task_arrivals_up_to@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
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
  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0))
  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
     (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Task -> Prosa_Behavior_Time_instant -> List Job

Arguments Prosa_Model_Task_Arrivals_task_arrivals_up_to Job
  inst_3 Task
  inst_7
  inst_10 arr_seq tsk t
```
