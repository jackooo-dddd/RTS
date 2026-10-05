# `another_hep_job_of_same_task`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.another_hep_job_of_same_task`
- Lean: `Prosa.Model.Priority.Definitions.another_hep_job_of_same_task`
- Certificate: `pd_another_hep_job_of_same_task_certificate`

## Official Rocq

```coq
another_hep_job_of_same_task :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task -> JLFP_policy Job -> Equality.sort Job -> Equality.sort Job -> bool

another_hep_job_of_same_task is not universe polymorphic
Arguments another_hep_job_of_same_task {Task Job H H0} j1 j2
another_hep_job_of_same_task is transparent
Expands to: Constant prosa.model.priority.definitions.another_hep_job_of_same_task
Declared in library prosa.model.priority.definitions, line 181, characters 13-41
@another_hep_job_of_same_task
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task -> JLFP_policy Job -> Equality.sort Job -> Equality.sort Job -> bool
```

Body:

```coq
another_hep_job_of_same_task =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JLFP_policy Job)
  (j1 j2 : Equality.sort Job) =>
@another_hep_job Job H0 j1 j2 && (@job_task Job Task H j1 == @job_task Job Task H j2)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task -> JLFP_policy Job -> Equality.sort Job -> Equality.sort Job -> bool

Arguments another_hep_job_of_same_task {Task Job H H0} j1 j2
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.another_hep_job_of_same_task : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Job → Bool
def Prosa.Model.Priority.Definitions.another_hep_job_of_same_task.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Job → Bool :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Model.Priority.Definitions.JLFP_policy Job] j1 j2 =>
  Prosa.Model.Priority.Definitions.another_hep_job j1 j2 &&
    decide (Prosa.Model.Task.Concept.job_task j1 = Prosa.Model.Task.Concept.job_task j2)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_another_hep_job_of_same_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> Job -> Bool
```

Body:

```coq
Prosa_Model_Priority_Definitions_another_hep_job_of_same_task@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
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
  (inst_14 : Prosa_Model_Priority_Definitions_JLFP_policy
                                                                              Job
                                                                              inst_7)
  (j1 j2 : Job) =>
Bool_and
  (Prosa_Model_Priority_Definitions_another_hep_job Job
     inst_7
     inst_14 j1 j2)
  (Decidable_decide
     (@eq Task
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_7 Task
           inst_3
           inst_10 j1)
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_7 Task
           inst_3
           inst_10 j2))
     (inst_3
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_7 Task
           inst_3
           inst_10 j1)
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_7 Task
           inst_3
           inst_10 j2)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> Job -> Bool

Arguments Prosa_Model_Priority_Definitions_another_hep_job_of_same_task Task
  inst_3 Job
  inst_7
  inst_10
  inst_14 a____at____internal__hyg0
  a____at____internal__hyg0
```
