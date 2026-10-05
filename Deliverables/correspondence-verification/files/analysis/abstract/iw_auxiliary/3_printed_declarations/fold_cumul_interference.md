# `fold_cumul_interference`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.iw_auxiliary.fold_cumul_interference`
- Lean: `Prosa.Analysis.Abstract.IwAuxiliary.fold_cumul_interference`
- Certificate: `fold_cumul_interference_correspondence`

## Official Rocq

```coq
fold_cumul_interference :
forall {Job : JobType} {H3 : Interference Job} (j : Equality.sort Job) (t1 t2 : nat),
@cumul_cond_interference Job H3 (fun=> xpredT) j t1 t2 = @cumulative_interference Job H3 j t1 t2

fold_cumul_interference is not universe polymorphic
Arguments fold_cumul_interference {Job H3} j (t1 t2)%nat_scope
fold_cumul_interference is opaque
Expands to: Constant prosa.analysis.abstract.iw_auxiliary.fold_cumul_interference
Declared in library prosa.analysis.abstract.iw_auxiliary, line 56, characters 8-31
@fold_cumul_interference
     : forall (Job : JobType) (H3 : Interference Job) (j : Equality.sort Job) (t1 t2 : nat),
       @cumul_cond_interference Job H3 (fun=> xpredT) j t1 t2 = @cumulative_interference Job H3 j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Abstract.IwAuxiliary.fold_cumul_interference : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Analysis.Abstract.Definitions.Interference Job] (j : Job) (t1 t2 : ℕ),
  Prosa.Analysis.Abstract.Definitions.cumul_cond_interference (fun x x_1 => true) j t1 t2 =
    Prosa.Analysis.Abstract.Definitions.cumulative_interference j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IwAuxiliary_fold_cumul_interference
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (j : Job) (t1 t2 : Nat),
       @eq Nat
         (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
            inst_3
            inst_6
            (fun (_ : Job) (_ : Prosa_Behavior_Time_instant) => Bool_true) j t1 t2)
         (Prosa_Analysis_Abstract_Definitions_cumulative_interference Job
            inst_3
            inst_6 j t1 t2)
```
