# `cumul_cond_interference_ID`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_ID`
- Lean: `Prosa.Analysis.Abstract.IwAuxiliary.cumul_cond_interference_ID`
- Certificate: `cumul_cond_interference_ID_correspondence`

## Official Rocq

```coq
cumul_cond_interference_ID :
forall {Job : JobType} {H3 : Interference Job} (P1 P2 : Equality.sort Job -> instant -> bool)
  (j : Equality.sort Job) (t1 t2 : nat),
@cumul_cond_interference Job H3 P1 j t1 t2 =
@cumul_cond_interference Job H3 (fun (j0 : Equality.sort Job) (t : instant) => P1 j0 t && P2 j0 t) j t1 t2 +
@cumul_cond_interference Job H3 (fun (j0 : Equality.sort Job) (t : instant) => P1 j0 t && ~~ P2 j0 t) j t1 t2

cumul_cond_interference_ID is not universe polymorphic
Arguments cumul_cond_interference_ID {Job H3} (P1 P2)%function_scope j (t1 t2)%nat_scope
cumul_cond_interference_ID is opaque
Expands to: Constant prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_ID
Declared in library prosa.analysis.abstract.iw_auxiliary, line 122, characters 10-36
@cumul_cond_interference_ID
     : forall (Job : JobType) (H3 : Interference Job) (P1 P2 : Equality.sort Job -> instant -> bool)
         (j : Equality.sort Job) (t1 t2 : nat),
       @cumul_cond_interference Job H3 P1 j t1 t2 =
       @cumul_cond_interference Job H3 (fun (j0 : Equality.sort Job) (t : instant) => P1 j0 t && P2 j0 t) j
         t1 t2 +
       @cumul_cond_interference Job H3 (fun (j0 : Equality.sort Job) (t : instant) => P1 j0 t && ~~ P2 j0 t)
         j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Abstract.IwAuxiliary.cumul_cond_interference_ID : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  (P1 P2 : Job → Prosa.Behavior.Time.instant → Bool) (j : Job) (t1 t2 : ℕ),
  Prosa.Analysis.Abstract.Definitions.cumul_cond_interference P1 j t1 t2 =
    Prosa.Analysis.Abstract.Definitions.cumul_cond_interference (fun j t => P1 j t && P2 j t) j t1 t2 +
      Prosa.Analysis.Abstract.Definitions.cumul_cond_interference (fun j t => P1 j t && !P2 j t) j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IwAuxiliary_cumul_cond_interference_ID
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (P1 P2 : Job -> Prosa_Behavior_Time_instant -> Bool) (j : Job) (t1 t2 : Nat),
       @eq Nat
         (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
            inst_3
            inst_6 P1 j t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
               inst_3
               inst_6
               (fun (j0 : Job) (t : Prosa_Behavior_Time_instant) => Bool_and (P1 j0 t) (P2 j0 t)) j t1 t2)
            (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
               inst_3
               inst_6
               (fun (j0 : Job) (t : Prosa_Behavior_Time_instant) => Bool_and (P1 j0 t) (Bool_not (P2 j0 t)))
               j t1 t2))
```
