# `hyperperiod_int_mult_of_any_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.hyperperiod.hyperperiod_int_mult_of_any_task`
- Lean: `Prosa.Analysis.Facts.Hyperperiod.hyperperiod_int_mult_of_any_task`
- Certificate: `hyperperiod_int_mult_of_any_task_correspondence`

## Official Rocq

```coq
hyperperiod_int_mult_of_any_task :
forall {Task : TaskType} {H : PeriodicModel Task} (ts : TaskSet (Equality.sort Task))
  (tsk : Equality.sort Task),
is_true (tsk \in ts) -> exists k : nat, @hyperperiod Task H ts = k * @task_period Task H tsk

hyperperiod_int_mult_of_any_task is not universe polymorphic
Arguments hyperperiod_int_mult_of_any_task {Task H} ts tsk H_tsk_in_ts
hyperperiod_int_mult_of_any_task is opaque
Expands to: Constant prosa.analysis.facts.hyperperiod.hyperperiod_int_mult_of_any_task
Declared in library prosa.analysis.facts.hyperperiod, line 21, characters 8-40
@hyperperiod_int_mult_of_any_task
     : forall (Task : TaskType) (H : PeriodicModel Task) (ts : TaskSet (Equality.sort Task))
         (tsk : Equality.sort Task),
       is_true (tsk \in ts) -> exists k : nat, @hyperperiod Task H ts = k * @task_period Task H tsk
```

## Lean

```lean
@Prosa.Analysis.Facts.Hyperperiod.hyperperiod_int_mult_of_any_task : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task]
  (ts : Prosa.Model.Task.Concept.TaskSet Task) (tsk : Task),
  decide (tsk ∈ ts) = true →
    ∃ k, Prosa.Analysis.Definitions.Hyperperiod.hyperperiod ts = k * Prosa.Model.Task.Arrival.Periodic.task_period tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Hyperperiod_hyperperiod_int_mult_of_any_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
            inst_3)
         (ts : Prosa_Model_Task_Concept_TaskSet Task) (tsk : Task),
       @eq Bool
         (Decidable_decide
            (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3) tsk
               ts))
         Bool_true ->
       Exists Nat
         (fun k : Nat =>
          Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
            inst_3
            inst_6 ts =
          HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) k
            (Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task
               inst_3
               inst_6 tsk))
```
