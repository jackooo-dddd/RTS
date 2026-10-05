# `hep_from_ep_task`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.priority.jlfp_with_fp.hep_from_ep_task`
- Lean: `Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_from_ep_task`
- Certificate: `hep_from_ep_task_correspondence`

## Official Rocq

```coq
hep_from_ep_task :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task -> FP_policy Task -> JLFP_policy Job -> Equality.sort Job -> Equality.sort Job -> bool

hep_from_ep_task is not universe polymorphic
Arguments hep_from_ep_task {Task Job H1 FP JLFP} j j'
hep_from_ep_task is transparent
Expands to: Constant prosa.analysis.facts.priority.jlfp_with_fp.hep_from_ep_task
Declared in library prosa.analysis.facts.priority.jlfp_with_fp, line 85, characters 13-29
@hep_from_ep_task
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       FP_policy Task -> JLFP_policy Job -> Equality.sort Job -> Equality.sort Job -> bool
```

Body:

```coq
hep_from_ep_task =
fun (Task : TaskType) (Job : JobType) (H1 : JobTask Job Task) (FP : FP_policy Task) 
  (JLFP : JLFP_policy Job) (j j' : Equality.sort Job) =>
@hep_job Job JLFP j' j && @ep_task Task FP (@job_task Job Task H1 j') (@job_task Job Task H1 j)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       FP_policy Task -> JLFP_policy Job -> Equality.sort Job -> Equality.sort Job -> bool

Arguments hep_from_ep_task {Task Job H1 FP JLFP} j j'
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_from_ep_task : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
            [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Job → Bool
```

Body:

```lean
def Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_from_ep_task.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
            [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Job → Bool :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Model.Priority.Definitions.FP_policy Task] [Prosa.Model.Priority.Definitions.JLFP_policy Job] j j' =>
  Prosa.Model.Priority.Definitions.hep_job j' j &&
    Prosa.Model.Priority.Definitions.ep_task (Prosa.Model.Task.Concept.job_task j')
      (Prosa.Model.Task.Concept.job_task j)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_from_ep_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> Job -> Bool
```

Body:

```coq
Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_from_ep_task@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_13 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7 Task
     inst_3)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_7)
  (j j' : Job) =>
Bool_and
  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
     inst_7 JLFP j' j)
  (Prosa_Model_Priority_Definitions_ep_task Task
     inst_3 FP
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_7 Task
        inst_3
        inst_13 j')
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_7 Task
        inst_3
        inst_13 j))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> Job -> Bool

Arguments Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_from_ep_task Task
  inst_3 Job
  inst_7
  inst_13 
  FP JLFP j j'
```
