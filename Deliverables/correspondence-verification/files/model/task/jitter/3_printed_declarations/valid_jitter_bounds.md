# `valid_jitter_bounds`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.jitter.valid_jitter_bounds`
- Lean: `Prosa.Model.Task.Jitter.valid_jitter_bounds`
- Certificate: `valid_jitter_bounds_correspondence`

## Official Rocq

```coq
valid_jitter_bounds :
forall {Task : TaskType},
TaskJitter Task ->
forall {Job : JobType}, JobTask Job Task -> JobJitter Job -> TaskSet (Equality.sort Task) -> Prop

valid_jitter_bounds is not universe polymorphic
Arguments valid_jitter_bounds {Task H Job H0 H1} ts
valid_jitter_bounds is transparent
Expands to: Constant prosa.model.task.jitter.valid_jitter_bounds
Declared in library prosa.model.task.jitter, line 31, characters 13-32
@valid_jitter_bounds
     : forall Task : TaskType,
       TaskJitter Task ->
       forall Job : JobType, JobTask Job Task -> JobJitter Job -> TaskSet (Equality.sort Task) -> Prop
```

Body:

```coq
valid_jitter_bounds =
fun (Task : TaskType) (H : TaskJitter Task) (Job : JobType) (H0 : JobTask Job Task) 
  (H1 : JobJitter Job) (ts : TaskSet (Equality.sort Task)) =>
forall tsk : Equality.sort Task, is_true (tsk \in ts) -> @valid_jitter Task H Job H0 H1 tsk
     : forall {Task : TaskType},
       TaskJitter Task ->
       forall {Job : JobType}, JobTask Job Task -> JobJitter Job -> TaskSet (Equality.sort Task) -> Prop

Arguments valid_jitter_bounds {Task H Job H0 H1} ts
```

## Lean

```lean
@Prosa.Model.Task.Jitter.valid_jitter_bounds : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Jitter.TaskJitter Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Model.Readiness.Jitter.JobJitter Job] → Prosa.Model.Task.Concept.TaskSet Task → Prop
def Prosa.Model.Task.Jitter.valid_jitter_bounds.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Jitter.TaskJitter Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Model.Readiness.Jitter.JobJitter Job] → Prosa.Model.Task.Concept.TaskSet Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Jitter.TaskJitter Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Model.Readiness.Jitter.JobJitter Job] ts =>
  ∀ (tsk : Task), decide (tsk ∈ ts) = true → Prosa.Model.Task.Jitter.valid_jitter tsk
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Jitter_valid_jitter_bounds
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Jitter_TaskJitter Task inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Model_Readiness_Jitter_JobJitter Job
         inst_10 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Jitter_valid_jitter_bounds@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
Lean.u_1+2.0 Lean.u_2+2.0} =
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
  (ts : Prosa_Model_Task_Concept_TaskSet Task) =>
forall tsk : Task,
@eq Bool
  (Decidable_decide
     (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
     (List_instDecidableMemOfLawfulBEq Task
        (instBEqOfDecidableEq Task inst_3)
        (instLawfulBEq Task inst_3) tsk ts))
  Bool_true ->
Prosa_Model_Task_Jitter_valid_jitter Task inst_3
  inst_6 Job
  inst_10
  inst_13
  inst_17 tsk
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Jitter_TaskJitter Task inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Model_Readiness_Jitter_JobJitter Job
         inst_10 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp

Arguments Prosa_Model_Task_Jitter_valid_jitter_bounds Task
  inst_3
  inst_6 Job
  inst_10
  inst_13
  inst_17 ts
```
