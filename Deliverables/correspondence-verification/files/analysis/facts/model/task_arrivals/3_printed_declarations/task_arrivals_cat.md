# `task_arrivals_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_arrivals.task_arrivals_cat`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_cat`
- Certificate: `task_arrivals_cat_correspondence`

## Official Rocq

```coq
task_arrivals_cat :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (t_m t : nat),
is_true (t_m <= t) ->
@task_arrivals_up_to Job Task H arr_seq tsk t =
@task_arrivals_up_to Job Task H arr_seq tsk t_m ++ @task_arrivals_between Job Task H arr_seq tsk t_m.+1 t.+1

task_arrivals_cat is not universe polymorphic
Arguments task_arrivals_cat {Job Task H} arr_seq tsk (t_m t)%nat_scope _
task_arrivals_cat is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.task_arrivals_cat
Declared in library prosa.analysis.facts.model.task_arrivals, line 95, characters 8-25
@task_arrivals_cat
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
         (tsk : Equality.sort Task) (t_m t : nat),
       is_true (t_m <= t) ->
       @task_arrivals_up_to Job Task H arr_seq tsk t =
       @task_arrivals_up_to Job Task H arr_seq tsk t_m ++
       @task_arrivals_between Job Task H arr_seq tsk t_m.+1 t.+1
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.task_arrivals_cat : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (tsk : Task) (t_m t : ℕ),
  t_m ≤ t →
    Prosa.Model.Task.Arrivals.task_arrivals_up_to arr_seq tsk t =
      Prosa.Model.Task.Arrivals.task_arrivals_up_to arr_seq tsk t_m ++
        Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk (t_m + 1) (t + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_cat
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
         (tsk : Task) (t_m t : Nat),
       LE_le_inst1 Nat instLENat t_m t ->
       @eq (List Job)
         (Prosa_Model_Task_Arrivals_task_arrivals_up_to Job
            inst_3 Task
            inst_7
            inst_10 arr_seq tsk t)
         (HAppend_hAppend (List Job) (List Job) (List Job)
            (instHAppendOfAppend (List Job) (List_instAppend Job))
            (Prosa_Model_Task_Arrivals_task_arrivals_up_to Job
               inst_3 Task
               inst_7
               inst_10 arr_seq tsk t_m)
            (Prosa_Model_Task_Arrivals_task_arrivals_between Job
               inst_3 Task
               inst_7
               inst_10 arr_seq tsk
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) t_m
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) t
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))))
```
