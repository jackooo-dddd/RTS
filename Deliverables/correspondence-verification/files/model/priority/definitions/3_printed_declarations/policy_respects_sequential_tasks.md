# `policy_respects_sequential_tasks`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.policy_respects_sequential_tasks`
- Lean: `Prosa.Model.Priority.Definitions.policy_respects_sequential_tasks`
- Certificate: `pd_policy_respects_sequential_tasks_certificate`

## Official Rocq

```coq
policy_respects_sequential_tasks :
forall {Task : TaskType} {Job : JobType}, JobTask Job Task -> JobArrival Job -> JLFP_policy Job -> Prop

policy_respects_sequential_tasks is not universe polymorphic
Arguments policy_respects_sequential_tasks {Task Job H0 H1} JLFP
policy_respects_sequential_tasks is transparent
Expands to: Constant prosa.model.priority.definitions.policy_respects_sequential_tasks
Declared in library prosa.model.priority.definitions, line 108, characters 15-47
@policy_respects_sequential_tasks
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task -> JobArrival Job -> JLFP_policy Job -> Prop
```

Body:

```coq
policy_respects_sequential_tasks =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job) (JLFP : JLFP_policy Job) =>
forall j1 j2 : Equality.sort Job,
is_true (@job_task Job Task H0 j1 == @job_task Job Task H0 j2) ->
is_true (@job_arrival Job H1 j1 <= @job_arrival Job H1 j2) -> is_true (@hep_job Job JLFP j1 j2)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task -> JobArrival Job -> JLFP_policy Job -> Prop

Arguments policy_respects_sequential_tasks {Task Job H0 H1} JLFP
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.policy_respects_sequential_tasks : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job → Prop
def Prosa.Model.Priority.Definitions.policy_respects_sequential_tasks.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobArrival Job] JLFP =>
  ∀ (j1 j2 : Job),
    decide (Prosa.Model.Task.Concept.job_task j1 = Prosa.Model.Task.Concept.job_task j2) = true →
      Prosa.Behavior.Job.job_arrival j1 ≤ Prosa.Behavior.Job.job_arrival j2 →
        Prosa.Model.Priority.Definitions.hep_job j1 j2 = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_7 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       SProp
```

Body:

```coq
Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                             Job
                                                                             inst_7
                                                                             Task
                                                                             inst_3)
  (inst_14 : Prosa_Behavior_Job_JobArrival Job
                                                                             inst_7)
  (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_7) =>
forall j1 j2 : Job,
@eq Bool
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
  Bool_true ->
LE_le_inst1 Prosa_Behavior_Time_instant instLENat
  (Prosa_Behavior_Job_JobArrival_job_arrival Job
     inst_7
     inst_14 j1)
  (Prosa_Behavior_Job_JobArrival_job_arrival Job
     inst_7
     inst_14 j2) ->
@eq Bool
  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
     inst_7 JLFP j1 j2)
  Bool_true
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_7 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       SProp

Arguments Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks Task
  inst_3 Job
  inst_7
  inst_10
  inst_14 JLFP
```
