# `cumul_cond_interference`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.definitions.cumul_cond_interference`
- Lean: `Prosa.Analysis.Abstract.Definitions.cumul_cond_interference`
- Certificate: `cumul_cond_interference_correspondence`

## Official Rocq

```coq
cumul_cond_interference :
forall {Job : JobType},
Interference Job -> (Equality.sort Job -> instant -> bool) -> Equality.sort Job -> nat -> nat -> nat

cumul_cond_interference is not universe polymorphic
Arguments cumul_cond_interference {Job H2} P%function_scope j (t1 t2)%nat_scope
cumul_cond_interference is transparent
Expands to: Constant prosa.analysis.abstract.definitions.cumul_cond_interference
Declared in library prosa.analysis.abstract.definitions, line 94, characters 13-36
@cumul_cond_interference
     : forall Job : JobType,
       Interference Job -> (Equality.sort Job -> instant -> bool) -> Equality.sort Job -> nat -> nat -> nat
```

Body:

```coq
cumul_cond_interference =
fun (Job : JobType) (H2 : Interference Job) (P : Equality.sort Job -> instant -> bool)
  (j : Equality.sort Job) (t1 t2 : nat) =>
\sum_(t1 <= t < t2) nat_of_bool (@cond_interference Job H2 P j t)
     : forall {Job : JobType},
       Interference Job -> (Equality.sort Job -> instant -> bool) -> Equality.sort Job -> nat -> nat -> nat

Arguments cumul_cond_interference {Job H2} P%function_scope j (t1 t2)%nat_scope
```

## Lean

```lean
@Prosa.Analysis.Abstract.Definitions.cumul_cond_interference : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      (Job → Prosa.Behavior.Time.instant → Bool) → Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
def Prosa.Analysis.Abstract.Definitions.cumul_cond_interference.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      (Job → Prosa.Behavior.Time.instant → Bool) →
        Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Analysis.Abstract.Definitions.Interference Job] P j t1 t2 =>
  ∑ t ∈ Finset.Ico t1 t2, (Prosa.Analysis.Abstract.Definitions.cond_interference P j t).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_cumul_cond_interference
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       (Job -> Prosa_Behavior_Time_instant -> Bool) ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Abstract_Definitions_cumul_cond_interference@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : 
   DecidableEq Job)
  (inst_6 : 
   Prosa_Analysis_Abstract_Definitions_Interference Job
     inst_3)
  (P : Job -> Prosa_Behavior_Time_instant -> Bool) (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
List_foldr_inst3 Nat Nat Nat_add (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (List_map_inst3 Prosa_Behavior_Time_instant Nat
     (fun t : Prosa_Behavior_Time_instant =>
      Bool_toNat
        (Prosa_Analysis_Abstract_Definitions_cond_interference Job
           inst_3
           inst_6
           P j t))
     (List_range' t1
        (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
           (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1)
        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       (Job -> Prosa_Behavior_Time_instant -> Bool) ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
  inst_3
  inst_6 P%_function_scope 
  j t1 t2
```
