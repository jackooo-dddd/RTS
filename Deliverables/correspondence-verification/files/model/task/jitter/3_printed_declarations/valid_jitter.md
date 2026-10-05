# `valid_jitter`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.jitter.valid_jitter`
- Lean: `Prosa.Model.Task.Jitter.valid_jitter`
- Certificate: `valid_jitter_correspondence`

## Official Rocq

```coq
valid_jitter :
forall {Task : TaskType},
TaskJitter Task -> forall {Job : JobType}, JobTask Job Task -> JobJitter Job -> Equality.sort Task -> Prop

valid_jitter is not universe polymorphic
Arguments valid_jitter {Task H Job H0 H1} tsk
valid_jitter is transparent
Expands to: Constant prosa.model.task.jitter.valid_jitter
Declared in library prosa.model.task.jitter, line 22, characters 13-25
@valid_jitter
     : forall Task : TaskType,
       TaskJitter Task ->
       forall Job : JobType, JobTask Job Task -> JobJitter Job -> Equality.sort Task -> Prop
```

Body:

```coq
valid_jitter =
fun (Task : TaskType) (H : TaskJitter Task) (Job : JobType) (H0 : JobTask Job Task) 
  (H1 : JobJitter Job) (tsk : Equality.sort Task) =>
forall j : Equality.sort Job,
@job_task Job Task H0 j = tsk -> is_true (@job_jitter Job H1 j <= @task_jitter Task H tsk)
     : forall {Task : TaskType},
       TaskJitter Task ->
       forall {Job : JobType}, JobTask Job Task -> JobJitter Job -> Equality.sort Task -> Prop

Arguments valid_jitter {Task H Job H0 H1} tsk
```

## Lean

```lean
@Prosa.Model.Task.Jitter.valid_jitter : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Jitter.TaskJitter Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] → [Prosa.Model.Readiness.Jitter.JobJitter Job] → Task → Prop
def Prosa.Model.Task.Jitter.valid_jitter.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Jitter.TaskJitter Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] → [Prosa.Model.Readiness.Jitter.JobJitter Job] → Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Jitter.TaskJitter Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Model.Readiness.Jitter.JobJitter Job] tsk =>
  ∀ (j : Job),
    Prosa.Model.Task.Concept.job_task j = tsk →
      Prosa.Model.Readiness.Jitter.job_jitter j ≤ Prosa.Model.Task.Jitter.task_jitter tsk
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Jitter_valid_jitter
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Jitter_TaskJitter Task inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Model_Readiness_Jitter_JobJitter Job
         inst_10 ->
       Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Jitter_valid_jitter@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0
Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Jitter_TaskJitter Task
                                                                    inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : Prosa_Model_Task_Concept_JobTask Job
                                                                     inst_10
                                                                     Task
                                                                     inst_3)
  (inst_17 : Prosa_Model_Readiness_Jitter_JobJitter Job
                                                                     inst_10)
  (tsk : Task) =>
forall j : Job,
@eq Task
  (Prosa_Model_Task_Concept_JobTask_job_task Job
     inst_10 Task
     inst_3
     inst_13 j)
  tsk ->
LE_le_inst1 Prosa_Behavior_Time_duration instLENat
  (Prosa_Model_Readiness_Jitter_JobJitter_job_jitter Job
     inst_10
     inst_17 j)
  (Prosa_Model_Task_Jitter_TaskJitter_task_jitter Task
     inst_3
     inst_6 tsk)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Jitter_TaskJitter Task inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Model_Readiness_Jitter_JobJitter Job
         inst_10 ->
       Task -> SProp

Arguments Prosa_Model_Task_Jitter_valid_jitter Task
  inst_3
  inst_6 Job
  inst_10
  inst_13
  inst_17 tsk
```
