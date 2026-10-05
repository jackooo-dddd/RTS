# `number_of_task_arrivals_with_deadline_within`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrivals.number_of_task_arrivals_with_deadline_within`
- Lean: `Prosa.Model.Task.Arrivals.number_of_task_arrivals_with_deadline_within`
- Certificate: `number_of_task_arrivals_with_deadline_within_correspondence`

## Official Rocq

```coq
number_of_task_arrivals_with_deadline_within :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task ->
arrival_sequence Job -> Equality.sort Task -> JobDeadline Job -> instant -> instant -> nat

number_of_task_arrivals_with_deadline_within is not universe polymorphic
Arguments number_of_task_arrivals_with_deadline_within {Job Task H} arr_seq tsk {H2} t1 t2
number_of_task_arrivals_with_deadline_within is transparent
Expands to: Constant prosa.model.task.arrivals.number_of_task_arrivals_with_deadline_within
Declared in library prosa.model.task.arrivals, line 58, characters 13-57
@number_of_task_arrivals_with_deadline_within
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task ->
       arrival_sequence Job -> Equality.sort Task -> JobDeadline Job -> instant -> instant -> nat
```

Body:

```coq
number_of_task_arrivals_with_deadline_within =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (H2 : JobDeadline Job) (t1 t2 : instant) =>
@size (Equality.sort Job) (@task_arrivals_with_deadline_within Job Task H arr_seq tsk H2 t1 t2)
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task ->
       arrival_sequence Job -> Equality.sort Task -> JobDeadline Job -> instant -> instant -> nat

Arguments number_of_task_arrivals_with_deadline_within {Job Task H} arr_seq tsk {H2} t1 t2
```

## Lean

```lean
@Prosa.Model.Task.Arrivals.number_of_task_arrivals_with_deadline_within : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            Task → [Prosa.Behavior.Job.JobDeadline Job] → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
def Prosa.Model.Task.Arrivals.number_of_task_arrivals_with_deadline_within.{u_1, u_2} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            Task →
              [Prosa.Behavior.Job.JobDeadline Job] → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task] arr_seq tsk
    [Prosa.Behavior.Job.JobDeadline Job] t1 t2 =>
  (Prosa.Model.Task.Arrivals.task_arrivals_with_deadline_within arr_seq tsk t1 t2).length
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrivals_number_of_task_arrivals_with_deadline_within
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Task ->
       Prosa_Behavior_Job_JobDeadline Job inst_3 ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Model_Task_Arrivals_number_of_task_arrivals_with_deadline_within@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
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
  (tsk : Task)
  (inst_23 : Prosa_Behavior_Job_JobDeadline Job
                                                                      inst_3)
  (t1 t2 : Prosa_Behavior_Time_instant) =>
List_length Job
  (Prosa_Model_Task_Arrivals_task_arrivals_with_deadline_within Job
     inst_3 Task
     inst_7
     inst_10 arr_seq tsk
     inst_23 t1 t2)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Task ->
       Prosa_Behavior_Job_JobDeadline Job inst_3 ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Model_Task_Arrivals_number_of_task_arrivals_with_deadline_within 
  Job inst_3 Task
  inst_7
  inst_10 arr_seq tsk
  inst_23 t1 t2
```
