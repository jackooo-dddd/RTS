# `FP_to_JLFP`

- Kind (Rocq): Instance
- Rocq: `prosa.model.priority.coercion.FP_to_JLFP`
- Lean: `Prosa.Model.Priority.Coercion.FP_to_JLFP`
- Certificate: `FP_to_JLFP_correspondence`

## Official Rocq

```coq
FP_to_JLFP : forall {Job : JobType} {Task : TaskType}, JobTask Job Task -> FP_policy Task -> JLFP_policy Job

FP_to_JLFP is not universe polymorphic
Arguments FP_to_JLFP {Job Task tasks} FP _ _
FP_to_JLFP is a coercion
FP_to_JLFP is transparent
Expands to: Constant prosa.model.priority.coercion.FP_to_JLFP
Declared in library prosa.model.priority.coercion, line 15, characters 0-195
@FP_to_JLFP
     : forall (Job : JobType) (Task : TaskType), JobTask Job Task -> FP_policy Task -> JLFP_policy Job
```

Body:

```coq
FP_to_JLFP =
fun (Job : JobType) (Task : TaskType) (tasks : JobTask Job Task) (FP : FP_policy Task)
  (j1 j2 : Equality.sort Job) =>
@hep_task Task FP (@job_task Job Task tasks j1) (@job_task Job Task tasks j2)
     : forall {Job : JobType} {Task : TaskType}, JobTask Job Task -> FP_policy Task -> JLFP_policy Job

Arguments FP_to_JLFP {Job Task tasks} FP _ _
FP_to_JLFP is a coercion
```

## Lean

```lean
@Prosa.Model.Priority.Coercion.FP_to_JLFP : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [tasks : Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Model.Priority.Definitions.FP_policy Task → Prosa.Model.Priority.Definitions.JLFP_policy Job
@[instance_reducible] def Prosa.Model.Priority.Coercion.FP_to_JLFP.{u_1, u_2} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [tasks : Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Model.Priority.Definitions.FP_policy Task → Prosa.Model.Priority.Definitions.JLFP_policy Job :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task] FP =>
  {
    hep_job := fun j1 j2 =>
      Prosa.Model.Priority.Definitions.hep_task (Prosa.Model.Task.Concept.job_task j1)
        (Prosa.Model.Task.Concept.job_task j2) }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Coercion_FP_to_JLFP
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_7 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3
```

Body:

```coq
Prosa_Model_Priority_Coercion_FP_to_JLFP@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (tasks : Prosa_Model_Task_Concept_JobTask Job
             inst_3 Task
             inst_7)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_7) =>
Prosa_Model_Priority_Definitions_JLFP_policy_mk Job
  inst_3
  (fun j1 j2 : Job =>
   Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
     inst_7 FP
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_3 Task
        inst_7 tasks j1)
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_3 Task
        inst_7 tasks j2))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_7 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3

Arguments Prosa_Model_Priority_Coercion_FP_to_JLFP Job
  inst_3 Task
  inst_7 tasks FP
```
