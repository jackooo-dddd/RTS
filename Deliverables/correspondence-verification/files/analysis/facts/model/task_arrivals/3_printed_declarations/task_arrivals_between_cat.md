# `task_arrivals_between_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.task_arrivals_between_cat`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_between_cat`
- Certificate: `task_arrivals_between_cat_correspondence`

## Official Rocq

```coq
task_arrivals_between_cat :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (t1 t t2 : nat),
is_true (t1 <= t) ->
is_true (t <= t2) ->
@task_arrivals_between Job Task H arr_seq tsk t1 t2 =
@task_arrivals_between Job Task H arr_seq tsk t1 t ++ @task_arrivals_between Job Task H arr_seq tsk t t2

task_arrivals_between_cat is not universe polymorphic
Arguments task_arrivals_between_cat {Job Task H} arr_seq tsk (t1 t t2)%nat_scope _ _
task_arrivals_between_cat is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.task_arrivals_between_cat
Declared in library prosa.analysis.facts.model.task_arrivals, line 32, characters 8-33
@task_arrivals_between_cat
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
         (tsk : Equality.sort Task) (t1 t t2 : nat),
       is_true (t1 <= t) ->
       is_true (t <= t2) ->
       @task_arrivals_between Job Task H arr_seq tsk t1 t2 =
       @task_arrivals_between Job Task H arr_seq tsk t1 t ++
       @task_arrivals_between Job Task H arr_seq tsk t t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_between_cat : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (tsk : Task) (t1 t t2 : ℕ),
  t1 ≤ t →
    t ≤ t2 →
      Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 t2 =
        Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 t ++
          Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_between_cat
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (tsk : Task) (t1 t t2 : Nat),
       LE_le_inst1 Nat instLENat t1 t ->
       LE_le_inst1 Nat instLENat t t2 ->
       @eq (List Job)
         (Prosa_Model_Task_Arrivals_task_arrivals_between Job
            inst_3 Task
            inst_7
            inst_10 arr_seq tsk t1 t2)
         (HAppend_hAppend (List Job) (List Job) (List Job)
            (instHAppendOfAppend (List Job) (List_instAppend Job))
            (Prosa_Model_Task_Arrivals_task_arrivals_between Job
               inst_3 Task
               inst_7
               inst_10 arr_seq tsk t1 t)
            (Prosa_Model_Task_Arrivals_task_arrivals_between Job
               inst_3 Task
               inst_7
               inst_10 arr_seq tsk t t2))
```
