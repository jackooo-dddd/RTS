# `task_arrivals_between_sorted`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.model.task_arrivals.task_arrivals_between_sorted`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_between_sorted`
- Certificate: `task_arrivals_between_sorted_correspondence`

## Official Rocq

```coq
task_arrivals_between_sorted :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H0 arr_seq ->
forall (tsk : Equality.sort Task) (t1 t2 : instant),
is_true
  (@sorted (Equality.sort Job) (@by_arrival_times Job H0)
     (@task_arrivals_between Job Task H arr_seq tsk t1 t2))

task_arrivals_between_sorted is not universe polymorphic
Arguments task_arrivals_between_sorted {Job Task H H0} arr_seq H_consistent_arrivals tsk t1 t2
task_arrivals_between_sorted is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.task_arrivals_between_sorted
Declared in library prosa.analysis.facts.model.task_arrivals, line 314, characters 12-40
@task_arrivals_between_sorted
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H0 arr_seq ->
       forall (tsk : Equality.sort Task) (t1 t2 : instant),
       is_true
         (@sorted (Equality.sort Job) (@by_arrival_times Job H0)
            (@task_arrivals_between Job Task H arr_seq tsk t1 t2))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_between_sorted : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (tsk : Task) (t1 t2 : Prosa.Behavior.Time.instant),
      List.IsChain (fun a b => Prosa.Analysis.Facts.Behavior.Arrivals.by_arrival_times a b = true)
        (Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_between_sorted
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_3
         inst_14 arr_seq ->
       forall (tsk : Task) (t1 t2 : Prosa_Behavior_Time_instant),
       List_IsChain Job
         (fun a b : Job =>
          Prosa_Analysis_Facts_Behavior_Arrivals_by_arrival_times Job
            inst_3
            inst_14 a b =
          Bool_true)
         (Prosa_Model_Task_Arrivals_task_arrivals_between Job
            inst_3 Task
            inst_7
            inst_10 arr_seq tsk t1 t2)
```
