# `workload_of_jobs_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.workload.workload_of_jobs_cat`
- Lean: `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_cat`
- Certificate: `workload_of_jobs_cat_correspondence`

## Official Rocq

```coq
workload_of_jobs_cat :
forall {Job : JobType} {H2 : JobCost Job} (arr_seq : arrival_sequence Job) (t t1 t2 : nat)
  (P : pred (Equality.sort Job)),
is_true (t1 <= t <= t2) ->
@workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t1 t2) =
@workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t1 t) +
@workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t t2)

workload_of_jobs_cat is not universe polymorphic
Arguments workload_of_jobs_cat {Job H2} arr_seq (t t1 t2)%nat_scope P _
workload_of_jobs_cat is opaque
Expands to: Constant prosa.analysis.facts.model.workload.workload_of_jobs_cat
Declared in library prosa.analysis.facts.model.workload, line 256, characters 8-28
@workload_of_jobs_cat
     : forall (Job : JobType) (H2 : JobCost Job) (arr_seq : arrival_sequence Job) 
         (t t1 t2 : nat) (P : pred (Equality.sort Job)),
       is_true (t1 <= t <= t2) ->
       @workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t1 t2) =
       @workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t1 t) +
       @workload_of_jobs Job H2 P (@arrivals_between Job arr_seq t t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_cat : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (t t1 t2 : ℕ) (P : Job → Bool),
  (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
    Prosa.Model.Aggregate.Workload.workload_of_jobs P (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) =
      Prosa.Model.Aggregate.Workload.workload_of_jobs P
          (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t) +
        Prosa.Model.Aggregate.Workload.workload_of_jobs P
          (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t t2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_cat
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (t t1 t2 : Nat) (P : Job -> Bool),
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LE_le_inst1 Nat instLENat t t2) (Nat_decLe t t2)))
         Bool_true ->
       @eq Nat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_3
            inst_6 P
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_3 arr_seq t1 t2))
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
               inst_3
               inst_6 P
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t1 t))
            (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
               inst_3
               inst_6 P
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_3 arr_seq t t2)))
```
