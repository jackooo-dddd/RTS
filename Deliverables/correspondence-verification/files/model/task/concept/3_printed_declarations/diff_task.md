# `diff_task`

- Kind (Rocq): Remark
- Rocq: `prosa.model.task.concept.diff_task`
- Lean: `Prosa.Model.Task.Concept.diff_task`
- Certificate: ``

## Official Rocq

```coq
diff_task :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} (tsk : Equality.sort Task)
  (j1 j2 : Equality.sort Job),
is_true (@job_of_task Job Task H tsk j1) ->
is_true (~~ @job_of_task Job Task H tsk j2) -> is_true (~~ @same_task Job Task H j1 j2)

diff_task is not universe polymorphic
Arguments diff_task {Job Task H} tsk j1 j2 _ _
diff_task is opaque
Expands to: Constant prosa.model.task.concept.diff_task
Declared in library prosa.model.task.concept, line 183, characters 9-18
@diff_task
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (tsk : Equality.sort Task)
         (j1 j2 : Equality.sort Job),
       is_true (@job_of_task Job Task H tsk j1) ->
       is_true (~~ @job_of_task Job Task H tsk j2) -> is_true (~~ @same_task Job Task H j1 j2)
```

## Lean

```lean
@Prosa.Model.Task.Concept.diff_task : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (tsk : Task) (j1 j2 : Job),
  Prosa.Model.Task.Concept.job_of_task tsk j1 = true →
    Prosa.Model.Task.Concept.job_of_task tsk j2 = false → Prosa.Model.Task.Concept.same_task j1 j2 = false
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_diff_task
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                             Job
                                                                             inst_3
                                                                             Task
                                                                             inst_7)
         (tsk : Task) (j1 j2 : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_3 Task
            inst_7
            inst_10 tsk j1)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_3 Task
            inst_7
            inst_10 tsk j2)
         Bool_false ->
       @eq Bool
         (Prosa_Model_Task_Concept_same_task Job
            inst_3 Task
            inst_7
            inst_10 j1 j2)
         Bool_false
```
