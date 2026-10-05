# `uniq_task_arrivals`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.uniq_task_arrivals`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.uniq_task_arrivals`
- Certificate: `uniq_task_arrivals_correspondence`

## Official Rocq

```coq
uniq_task_arrivals :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H0 arr_seq ->
forall (tsk : Equality.sort Task) (t : instant),
@arrival_sequence_uniq Job arr_seq -> is_true (@uniq Job (@task_arrivals_up_to Job Task H arr_seq tsk t))

uniq_task_arrivals is not universe polymorphic
Arguments uniq_task_arrivals {Job Task H H0} arr_seq H_consistent_arrivals tsk t _
uniq_task_arrivals is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.uniq_task_arrivals
Declared in library prosa.analysis.facts.model.task_arrivals, line 205, characters 8-26
@uniq_task_arrivals
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H0 arr_seq ->
       forall (tsk : Equality.sort Task) (t : instant),
       @arrival_sequence_uniq Job arr_seq ->
       is_true (@uniq Job (@task_arrivals_up_to Job Task H arr_seq tsk t))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.uniq_task_arrivals : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (tsk : Task) (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq arr_seq →
        (Prosa.Model.Task.Arrivals.task_arrivals_up_to arr_seq tsk t).Nodup
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_uniq_task_arrivals
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
       forall (tsk : Task) (t : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq Job
         inst_3 arr_seq ->
       List_Nodup Job
         (Prosa_Model_Task_Arrivals_task_arrivals_up_to Job
            inst_3 Task
            inst_7
            inst_10 arr_seq tsk t)
```
