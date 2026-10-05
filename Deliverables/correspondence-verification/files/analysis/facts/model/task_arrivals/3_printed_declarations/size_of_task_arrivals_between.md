# `size_of_task_arrivals_between`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.size_of_task_arrivals_between`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.size_of_task_arrivals_between`
- Certificate: `size_of_task_arrivals_between_correspondence`

## Official Rocq

```coq
size_of_task_arrivals_between :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (t1 t2 : instant),
@size (Equality.sort Job) (@task_arrivals_between Job Task H arr_seq tsk t1 t2) =
\sum_(t1 <= t < t2) @size (Equality.sort Job) (@task_arrivals_at Job Task H arr_seq tsk t)

size_of_task_arrivals_between is not universe polymorphic
Arguments size_of_task_arrivals_between {Job Task H} arr_seq tsk t1 t2
size_of_task_arrivals_between is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.size_of_task_arrivals_between
Declared in library prosa.analysis.facts.model.task_arrivals, line 300, characters 8-37
@size_of_task_arrivals_between
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
         (tsk : Equality.sort Task) (t1 t2 : instant),
       @size (Equality.sort Job) (@task_arrivals_between Job Task H arr_seq tsk t1 t2) =
       \sum_(t1 <= t < t2) @size (Equality.sort Job) (@task_arrivals_at Job Task H arr_seq tsk t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.size_of_task_arrivals_between : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (tsk : Task) (t1 t2 : Prosa.Behavior.Time.instant),
  (Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 t2).length =
    Prosa.Util.Sum.sumSeq (List.range' t1 (t2 - t1)) fun t =>
      (Prosa.Model.Task.Arrivals.task_arrivals_at arr_seq tsk t).length
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_size_of_task_arrivals_between
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
       @eq Nat
         (List_length Job
            (Prosa_Model_Task_Arrivals_task_arrivals_between Job
               inst_3 Task
               inst_7
               inst_10 arr_seq tsk t1
               t2))
         (Prosa_Util_Sum_sumSeq_inst1 Nat
            (List_range' t1
               (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                  Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1)
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
            (fun t : Nat =>
             List_length Job
               (Prosa_Model_Task_Arrivals_task_arrivals_at Job
                  inst_3 Task
                  inst_7
                  inst_10 arr_seq tsk t)))
```
