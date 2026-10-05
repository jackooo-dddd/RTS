# `ep_task_hep_job`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.interference.ep_task_hep_job`
- Lean: `Prosa.Analysis.Definitions.Interference.ep_task_hep_job`
- Certificate: `ep_task_hep_job_correspondence`

## Official Rocq

```coq
ep_task_hep_job :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task -> FP_policy Task -> JLFP_policy Job -> Equality.sort Job -> Equality.sort Job -> bool

ep_task_hep_job is not universe polymorphic
Arguments ep_task_hep_job {Task Job jt FP JLFP} j1 j2
ep_task_hep_job is transparent
Expands to: Constant prosa.analysis.definitions.interference.ep_task_hep_job
Declared in library prosa.analysis.definitions.interference, line 42, characters 15-30
@ep_task_hep_job
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       FP_policy Task -> JLFP_policy Job -> Equality.sort Job -> Equality.sort Job -> bool
```

Body:

```coq
ep_task_hep_job =
fun (Task : TaskType) (Job : JobType) (jt : JobTask Job Task) (FP : FP_policy Task) 
  (JLFP : JLFP_policy Job) (j1 j2 : Equality.sort Job) =>
@hep_job Job JLFP j1 j2 && @ep_task Task FP (@job_task Job Task jt j1) (@job_task Job Task jt j2)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       FP_policy Task -> JLFP_policy Job -> Equality.sort Job -> Equality.sort Job -> bool

Arguments ep_task_hep_job {Task Job jt FP JLFP} j1 j2
```

## Lean

```lean
@Prosa.Analysis.Definitions.Interference.ep_task_hep_job : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
            [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Job → Bool
```

Body:

```lean
def Prosa.Analysis.Definitions.Interference.ep_task_hep_job.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
            [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Job → Bool :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Model.Priority.Definitions.FP_policy Task] [Prosa.Model.Priority.Definitions.JLFP_policy Job] j1 j2 =>
  Prosa.Model.Priority.Definitions.hep_job j1 j2 &&
    Prosa.Model.Priority.Definitions.ep_task (Prosa.Model.Task.Concept.job_task j1)
      (Prosa.Model.Task.Concept.job_task j2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Interference_ep_task_hep_job
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
Prosa_Analysis_Definitions_Interference_ep_task_hep_job@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7 Task
     inst_3)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (inst_16 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_7)
  (j1 j2 : Job) =>
Bool_and
  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
     inst_7
     inst_16 j1 j2)
  (Prosa_Model_Priority_Definitions_ep_task Task
     inst_3 FP
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_7 Task
        inst_3
        inst_10 j1)
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_7 Task
        inst_3
        inst_10 j2))
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

Arguments Prosa_Analysis_Definitions_Interference_ep_task_hep_job Task
  inst_3 Job
  inst_7
  inst_10 FP
  inst_16 j1 
  a____at____internal__hyg0
```
