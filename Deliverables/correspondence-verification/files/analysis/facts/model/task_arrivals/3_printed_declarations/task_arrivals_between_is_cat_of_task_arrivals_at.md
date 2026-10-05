# `task_arrivals_between_is_cat_of_task_arrivals_at`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.task_arrivals_between_is_cat_of_task_arrivals_at`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_between_is_cat_of_task_arrivals_at`
- Certificate: `task_arrivals_between_is_cat_of_task_arrivals_at_correspondence`

## Official Rocq

```coq
task_arrivals_between_is_cat_of_task_arrivals_at :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (t1 t2 : instant),
@task_arrivals_between Job Task H arr_seq tsk t1 t2 =
\cat_(t1<=t<t2)@task_arrivals_at Job Task H arr_seq tsk t

task_arrivals_between_is_cat_of_task_arrivals_at is not universe polymorphic
Arguments task_arrivals_between_is_cat_of_task_arrivals_at {Job Task H} arr_seq tsk t1 t2
task_arrivals_between_is_cat_of_task_arrivals_at is opaque
Expands to: Constant
            prosa.analysis.facts.model.task_arrivals.task_arrivals_between_is_cat_of_task_arrivals_at
Declared in library prosa.analysis.facts.model.task_arrivals, line 289, characters 8-56
@task_arrivals_between_is_cat_of_task_arrivals_at
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
         (tsk : Equality.sort Task) (t1 t2 : instant),
       @task_arrivals_between Job Task H arr_seq tsk t1 t2 =
       \cat_(t1<=t<t2)@task_arrivals_at Job Task H arr_seq tsk t
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_between_is_cat_of_task_arrivals_at : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (tsk : Task) (t1 t2 : Prosa.Behavior.Time.instant),
  Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 t2 =
    Prosa.Util.Notation.bigCat t1 t2 fun t => Prosa.Model.Task.Arrivals.task_arrivals_at arr_seq tsk t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_between_is_cat_of_task_arrivals_at
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
         (tsk : Task) (t1 t2 : Prosa_Behavior_Time_instant),
       @eq (List Job)
         (Prosa_Model_Task_Arrivals_task_arrivals_between Job
            inst_3 Task
            inst_7
            inst_10 arr_seq tsk t1 t2)
         (Prosa_Util_Notation_bigCat Job t1 t2
            (fun t : Nat =>
             Prosa_Model_Task_Arrivals_task_arrivals_at Job
               inst_3 Task
               inst_7
               inst_10 arr_seq tsk t))
```
