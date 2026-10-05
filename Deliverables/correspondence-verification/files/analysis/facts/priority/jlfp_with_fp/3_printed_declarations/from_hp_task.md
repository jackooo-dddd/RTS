# `from_hp_task`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.priority.jlfp_with_fp.from_hp_task`
- Lean: `Prosa.Analysis.Facts.Priority.JlfpWithFp.from_hp_task`
- Certificate: `from_hp_task_correspondence`

## Official Rocq

```coq
from_hp_task :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task -> FP_policy Task -> Equality.sort Job -> Equality.sort Job -> bool

from_hp_task is not universe polymorphic
Arguments from_hp_task {Task Job H1 FP} j j'
from_hp_task is transparent
Expands to: Constant prosa.analysis.facts.priority.jlfp_with_fp.from_hp_task
Declared in library prosa.analysis.facts.priority.jlfp_with_fp, line 76, characters 13-25
@from_hp_task
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task -> FP_policy Task -> Equality.sort Job -> Equality.sort Job -> bool
```

Body:

```coq
from_hp_task =
fun (Task : TaskType) (Job : JobType) (H1 : JobTask Job Task) (FP : FP_policy Task)
  (j j' : Equality.sort Job) =>
@hp_task Task FP (@job_task Job Task H1 j') (@job_task Job Task H1 j)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task -> FP_policy Task -> Equality.sort Job -> Equality.sort Job -> bool

Arguments from_hp_task {Task Job H1 FP} j j'
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.JlfpWithFp.from_hp_task : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → Job → Job → Bool
```

Body:

```lean
def Prosa.Analysis.Facts.Priority.JlfpWithFp.from_hp_task.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → Job → Job → Bool :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Model.Priority.Definitions.FP_policy Task] j j' =>
  Prosa.Model.Priority.Definitions.hp_task (Prosa.Model.Task.Concept.job_task j') (Prosa.Model.Task.Concept.job_task j)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_JlfpWithFp_from_hp_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Job -> Job -> Bool
```

Body:

```coq
Prosa_Analysis_Facts_Priority_JlfpWithFp_from_hp_task@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
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
  (j j' : Job) =>
Prosa_Model_Priority_Definitions_hp_task Task
  inst_3 FP
  (Prosa_Model_Task_Concept_JobTask_job_task Job
     inst_7 Task
     inst_3
     inst_13 j')
  (Prosa_Model_Task_Concept_JobTask_job_task Job
     inst_7 Task
     inst_3
     inst_13 j)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Job -> Job -> Bool

Arguments Prosa_Analysis_Facts_Priority_JlfpWithFp_from_hp_task Task
  inst_3 Job
  inst_7
  inst_13 
  FP j j'
```
