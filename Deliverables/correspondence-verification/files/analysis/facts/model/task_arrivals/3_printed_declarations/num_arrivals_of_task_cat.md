# `num_arrivals_of_task_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.num_arrivals_of_task_cat`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.num_arrivals_of_task_cat`
- Certificate: `num_arrivals_of_task_cat_correspondence`

## Official Rocq

```coq
num_arrivals_of_task_cat :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (t t1 t2 : nat),
is_true (t1 <= t <= t2) ->
@number_of_task_arrivals Job Task H arr_seq tsk t1 t2 =
@number_of_task_arrivals Job Task H arr_seq tsk t1 t + @number_of_task_arrivals Job Task H arr_seq tsk t t2

num_arrivals_of_task_cat is not universe polymorphic
Arguments num_arrivals_of_task_cat {Job Task H} arr_seq tsk (t t1 t2)%nat_scope _
num_arrivals_of_task_cat is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.num_arrivals_of_task_cat
Declared in library prosa.analysis.facts.model.task_arrivals, line 19, characters 8-32
@num_arrivals_of_task_cat
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
         (tsk : Equality.sort Task) (t t1 t2 : nat),
       is_true (t1 <= t <= t2) ->
       @number_of_task_arrivals Job Task H arr_seq tsk t1 t2 =
       @number_of_task_arrivals Job Task H arr_seq tsk t1 t +
       @number_of_task_arrivals Job Task H arr_seq tsk t t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.num_arrivals_of_task_cat : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (tsk : Task) (t t1 t2 : ℕ),
  (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
    Prosa.Model.Task.Arrivals.number_of_task_arrivals arr_seq tsk t1 t2 =
      Prosa.Model.Task.Arrivals.number_of_task_arrivals arr_seq tsk t1 t +
        Prosa.Model.Task.Arrivals.number_of_task_arrivals arr_seq tsk t t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_num_arrivals_of_task_cat
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
         (tsk : Task) (t t1 t2 : Nat),
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LE_le_inst1 Nat instLENat t t2) (Nat_decLe t t2)))
         Bool_true ->
       @eq Nat
         (Prosa_Model_Task_Arrivals_number_of_task_arrivals Job
            inst_3 Task
            inst_7
            inst_10 arr_seq tsk t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Task_Arrivals_number_of_task_arrivals Job
               inst_3 Task
               inst_7
               inst_10 arr_seq tsk t1 t)
            (Prosa_Model_Task_Arrivals_number_of_task_arrivals Job
               inst_3 Task
               inst_7
               inst_10 arr_seq tsk t t2))
```
