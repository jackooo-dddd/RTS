# `cumul_cond_interference_alt`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_alt`
- Lean: `Prosa.Analysis.Abstract.IwAuxiliary.cumul_cond_interference_alt`
- Certificate: `cumul_cond_interference_alt_correspondence`

## Official Rocq

```coq
cumul_cond_interference_alt :
forall {Job : JobType} {H3 : Interference Job} (P : Equality.sort Job -> instant -> bool)
  (j : Equality.sort Job) (t1 t2 : nat),
@cumul_cond_interference Job H3 P j t1 t2 =
\sum_(t1 <= t < t2 | P j t) nat_of_bool (@interference Job H3 j t)

cumul_cond_interference_alt is not universe polymorphic
Arguments cumul_cond_interference_alt {Job H3} P%function_scope j (t1 t2)%nat_scope
cumul_cond_interference_alt is opaque
Expands to: Constant prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_alt
Declared in library prosa.analysis.abstract.iw_auxiliary, line 72, characters 10-37
@cumul_cond_interference_alt
     : forall (Job : JobType) (H3 : Interference Job) (P : Equality.sort Job -> instant -> bool)
         (j : Equality.sort Job) (t1 t2 : nat),
       @cumul_cond_interference Job H3 P j t1 t2 =
       \sum_(t1 <= t < t2 | P j t) nat_of_bool (@interference Job H3 j t)
```

## Lean

```lean
@Prosa.Analysis.Abstract.IwAuxiliary.cumul_cond_interference_alt : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  (P : Job → Prosa.Behavior.Time.instant → Bool) (j : Job) (t1 t2 : ℕ),
  Prosa.Analysis.Abstract.Definitions.cumul_cond_interference P j t1 t2 =
    ∑ t ∈ Finset.Ico t1 t2, bif P j t then (Prosa.Analysis.Abstract.Definitions.interference j t).toNat else 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IwAuxiliary_cumul_cond_interference_alt
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (P : Job -> Prosa_Behavior_Time_instant -> Bool) (j : Job) (t1 t2 : Nat),
       @eq Nat
         (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
            inst_3
            inst_6 P j t1 t2)
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat
               (fun t : Nat =>
                cond Nat (P j t)
                  (Bool_toNat
                     (Prosa_Analysis_Abstract_Definitions_Interference_interference Job
                        inst_3
                        inst_6 j t))
                  (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
               (List_range' t1 (Nat_sub t2 t1) 1)))
```
