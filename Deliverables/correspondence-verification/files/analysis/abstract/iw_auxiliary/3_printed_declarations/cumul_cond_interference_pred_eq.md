# `cumul_cond_interference_pred_eq`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_pred_eq`
- Lean: `Prosa.Analysis.Abstract.IwAuxiliary.cumul_cond_interference_pred_eq`
- Certificate: `cumul_cond_interference_pred_eq_correspondence`

## Official Rocq

```coq
cumul_cond_interference_pred_eq :
forall {Job : JobType} {H3 : Interference Job} (P1 P2 : Equality.sort Job -> instant -> bool)
  (j : Equality.sort Job) (t1 t2 : instant),
(forall (j0 : Equality.sort Job) (t : instant), is_true (P1 j0 t) <-> is_true (P2 j0 t)) ->
@cumul_cond_interference Job H3 P1 j t1 t2 = @cumul_cond_interference Job H3 P2 j t1 t2

cumul_cond_interference_pred_eq is not universe polymorphic
Arguments cumul_cond_interference_pred_eq {Job H3} (P1 P2)%function_scope j t1 t2 _%function_scope
cumul_cond_interference_pred_eq is opaque
Expands to: Constant prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_pred_eq
Declared in library prosa.analysis.abstract.iw_auxiliary, line 136, characters 10-41
@cumul_cond_interference_pred_eq
     : forall (Job : JobType) (H3 : Interference Job) (P1 P2 : Equality.sort Job -> instant -> bool)
         (j : Equality.sort Job) (t1 t2 : instant),
       (forall (j0 : Equality.sort Job) (t : instant), is_true (P1 j0 t) <-> is_true (P2 j0 t)) ->
       @cumul_cond_interference Job H3 P1 j t1 t2 = @cumul_cond_interference Job H3 P2 j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Abstract.IwAuxiliary.cumul_cond_interference_pred_eq : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  (P1 P2 : Job → Prosa.Behavior.Time.instant → Bool) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
  (∀ (j : Job) (t : Prosa.Behavior.Time.instant), P1 j t = true ↔ P2 j t = true) →
    Prosa.Analysis.Abstract.Definitions.cumul_cond_interference P1 j t1 t2 =
      Prosa.Analysis.Abstract.Definitions.cumul_cond_interference P2 j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IwAuxiliary_cumul_cond_interference_pred_eq
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (P1 P2 : Job -> Prosa_Behavior_Time_instant -> Bool) (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       (forall (j0 : Job) (t : Prosa_Behavior_Time_instant),
        Iff (@eq Bool (P1 j0 t) Bool_true) (@eq Bool (P2 j0 t) Bool_true)) ->
       @eq Nat
         (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
            inst_3
            inst_6 P1 j t1 t2)
         (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
            inst_3
            inst_6 P2 j t1 t2)
```
