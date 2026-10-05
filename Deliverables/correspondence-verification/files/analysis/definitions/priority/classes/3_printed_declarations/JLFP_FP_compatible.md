# `JLFP_FP_compatible`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.priority.classes.JLFP_FP_compatible`
- Lean: `Prosa.Analysis.Definitions.Priority.Classes.JLFP_FP_compatible`
- Certificate: `JLFP_FP_compatible_correspondence`

## Official Rocq

```coq
JLFP_FP_compatible :
forall {Task : TaskType} {Job : JobType}, JobTask Job Task -> JLFP_policy Job -> FP_policy Task -> Prop

JLFP_FP_compatible is not universe polymorphic
Arguments JLFP_FP_compatible {Task Job H} JLFP FP
JLFP_FP_compatible is transparent
Expands to: Constant prosa.analysis.definitions.priority.classes.JLFP_FP_compatible
Declared in library prosa.analysis.definitions.priority.classes, line 19, characters 13-31
@JLFP_FP_compatible
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task -> JLFP_policy Job -> FP_policy Task -> Prop
```

Body:

```coq
JLFP_FP_compatible =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (JLFP : JLFP_policy Job) (FP : FP_policy Task) =>
(forall j1 j2 : Equality.sort Job,
 is_true (@hep_job Job JLFP j1 j2) ->
 is_true (@hep_task Task FP (@job_task Job Task H j1) (@job_task Job Task H j2))) /\
(forall j1 j2 : Equality.sort Job,
 is_true (@hp_task Task FP (@job_task Job Task H j1) (@job_task Job Task H j2)) ->
 is_true (@hep_job Job JLFP j1 j2))
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task -> JLFP_policy Job -> FP_policy Task -> Prop

Arguments JLFP_FP_compatible {Task Job H} JLFP FP
```

## Lean

```lean
@Prosa.Analysis.Definitions.Priority.Classes.JLFP_FP_compatible : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Model.Priority.Definitions.JLFP_policy Job → Prosa.Model.Priority.Definitions.FP_policy Task → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.Priority.Classes.JLFP_FP_compatible.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Model.Priority.Definitions.JLFP_policy Job → Prosa.Model.Priority.Definitions.FP_policy Task → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] JLFP FP =>
  (∀ (j1 j2 : Job),
      Prosa.Model.Priority.Definitions.hep_job j1 j2 = true →
        Prosa.Model.Priority.Definitions.hep_task (Prosa.Model.Task.Concept.job_task j1)
            (Prosa.Model.Task.Concept.job_task j2) =
          true) ∧
    ∀ (j1 j2 : Job),
      Prosa.Model.Priority.Definitions.hp_task (Prosa.Model.Task.Concept.job_task j1)
            (Prosa.Model.Task.Concept.job_task j2) =
          true →
        Prosa.Model.Priority.Definitions.hep_job j1 j2 = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7 Task
     inst_3)
  (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_7)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3) =>
And
  (forall j1 j2 : Job,
   @eq Bool
     (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
        inst_7 JLFP j1 j2)
     Bool_true ->
   @eq Bool
     (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
        inst_3 FP
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_7 Task
           inst_3
           inst_10 j1)
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_7 Task
           inst_3
           inst_10 j2))
     Bool_true)
  (forall j1 j2 : Job,
   @eq Bool
     (Prosa_Model_Priority_Definitions_hp_task Task
        inst_3 FP
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_7 Task
           inst_3
           inst_10 j1)
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_7 Task
           inst_3
           inst_10 j2))
     Bool_true ->
   @eq Bool
     (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
        inst_7 JLFP j1 j2)
     Bool_true)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       SProp

Arguments Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible Task
  inst_3 
  Job inst_7
  inst_10 
  JLFP FP
```
