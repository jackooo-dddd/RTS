# `cumulative_interference_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.iw_auxiliary.cumulative_interference_cat`
- Lean: `Prosa.Analysis.Abstract.IwAuxiliary.cumulative_interference_cat`
- Certificate: `cumulative_interference_cat_correspondence`

## Official Rocq

```coq
cumulative_interference_cat :
forall {Job : JobType} {H3 : Interference Job} (P : Equality.sort Job -> instant -> bool)
  (j : Equality.sort Job) (t t1 t2 : nat),
is_true (t1 <= t <= t2) ->
@cumul_cond_interference Job H3 P j t1 t2 =
@cumul_cond_interference Job H3 P j t1 t + @cumul_cond_interference Job H3 P j t t2

cumulative_interference_cat is not universe polymorphic
Arguments cumulative_interference_cat {Job H3} P%function_scope j (t t1 t2)%nat_scope _
cumulative_interference_cat is opaque
Expands to: Constant prosa.analysis.abstract.iw_auxiliary.cumulative_interference_cat
Declared in library prosa.analysis.abstract.iw_auxiliary, line 98, characters 10-37
@cumulative_interference_cat
     : forall (Job : JobType) (H3 : Interference Job) (P : Equality.sort Job -> instant -> bool)
         (j : Equality.sort Job) (t t1 t2 : nat),
       is_true (t1 <= t <= t2) ->
       @cumul_cond_interference Job H3 P j t1 t2 =
       @cumul_cond_interference Job H3 P j t1 t + @cumul_cond_interference Job H3 P j t t2
```

## Lean

```lean
@Prosa.Analysis.Abstract.IwAuxiliary.cumulative_interference_cat : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  (P : Job → Prosa.Behavior.Time.instant → Bool) (j : Job) (t t1 t2 : ℕ),
  (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
    Prosa.Analysis.Abstract.Definitions.cumul_cond_interference P j t1 t2 =
      Prosa.Analysis.Abstract.Definitions.cumul_cond_interference P j t1 t +
        Prosa.Analysis.Abstract.Definitions.cumul_cond_interference P j t t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IwAuxiliary_cumulative_interference_cat
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (P : Job -> Prosa_Behavior_Time_instant -> Bool) (j : Job) (t t1 t2 : Nat),
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LE_le_inst1 Nat instLENat t t2) (Nat_decLe t t2)))
         Bool_true ->
       @eq Nat
         (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
            inst_3
            inst_6 P j t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
               inst_3
               inst_6 P j t1 t)
            (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
               inst_3
               inst_6 P j t t2))
```
