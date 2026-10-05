# `arrivals_P_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.arrivals_P_cat`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_P_cat`
- Certificate: `arrivals_P_cat_correspondence`

## Official Rocq

```coq
arrivals_P_cat :
forall {Job : JobType} (arr_seq : arrival_sequence Job) (P : Equality.sort Job -> bool) (t t1 t2 : nat),
is_true (t1 <= t < t2) ->
@arrivals_between_P Job arr_seq P t1 t2 =
@arrivals_between_P Job arr_seq P t1 t ++ @arrivals_between_P Job arr_seq P t t2

arrivals_P_cat is not universe polymorphic
Arguments arrivals_P_cat {Job} arr_seq P%function_scope (t t1 t2)%nat_scope _
arrivals_P_cat is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.arrivals_P_cat
Declared in library prosa.analysis.facts.behavior.arrivals, line 146, characters 8-22
@arrivals_P_cat
     : forall (Job : JobType) (arr_seq : arrival_sequence Job) (P : Equality.sort Job -> bool)
         (t t1 t2 : nat),
       is_true (t1 <= t < t2) ->
       @arrivals_between_P Job arr_seq P t1 t2 =
       @arrivals_between_P Job arr_seq P t1 t ++ @arrivals_between_P Job arr_seq P t t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_P_cat : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (P : Job → Bool) (t t1 t2 : ℕ),
  (decide (t1 ≤ t) && decide (t < t2)) = true →
    Prosa.Behavior.Arrival_sequence.arrivals_between_P arr_seq P t1 t2 =
      Prosa.Behavior.Arrival_sequence.arrivals_between_P arr_seq P t1 t ++
        Prosa.Behavior.Arrival_sequence.arrivals_between_P arr_seq P t t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_P_cat
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (P : Job -> Bool) (t t1 t2 : Nat),
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       @eq (List Job)
         (Prosa_Behavior_Arrival_sequence_arrivals_between_P Job
            inst_3 arr_seq P t1 t2)
         (HAppend_hAppend (List Job) (List Job) (List Job)
            (instHAppendOfAppend (List Job) (List_instAppend Job))
            (Prosa_Behavior_Arrival_sequence_arrivals_between_P Job
               inst_3 arr_seq P t1 t)
            (Prosa_Behavior_Arrival_sequence_arrivals_between_P Job
               inst_3 arr_seq P t t2))
```
