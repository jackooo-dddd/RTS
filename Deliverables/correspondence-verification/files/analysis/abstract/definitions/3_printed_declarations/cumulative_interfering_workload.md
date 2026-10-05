# `cumulative_interfering_workload`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.definitions.cumulative_interfering_workload`
- Lean: `Prosa.Analysis.Abstract.Definitions.cumulative_interfering_workload`
- Certificate: `cumulative_interfering_workload_correspondence`

## Official Rocq

```coq
cumulative_interfering_workload :
forall {Job : JobType}, InterferingWorkload Job -> Equality.sort Job -> nat -> nat -> nat

cumulative_interfering_workload is not universe polymorphic
Arguments cumulative_interfering_workload {Job H3} j (t1 t2)%nat_scope
cumulative_interfering_workload is transparent
Expands to: Constant prosa.analysis.abstract.definitions.cumulative_interfering_workload
Declared in library prosa.analysis.abstract.definitions, line 102, characters 13-44
@cumulative_interfering_workload
     : forall Job : JobType, InterferingWorkload Job -> Equality.sort Job -> nat -> nat -> nat
```

Body:

```coq
cumulative_interfering_workload =
fun (Job : JobType) (H3 : InterferingWorkload Job) (j : Equality.sort Job) (t1 t2 : nat) =>
\sum_(t1 <= t < t2) @interfering_workload Job H3 j t
     : forall {Job : JobType}, InterferingWorkload Job -> Equality.sort Job -> nat -> nat -> nat

Arguments cumulative_interfering_workload {Job H3} j (t1 t2)%nat_scope
```

## Lean

```lean
@Prosa.Analysis.Abstract.Definitions.cumulative_interfering_workload : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
      Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
def Prosa.Analysis.Abstract.Definitions.cumulative_interfering_workload.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
      Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] j t1 t2 =>
  ∑ t ∈ Finset.Ico t1 t2, Prosa.Analysis.Abstract.Definitions.interfering_workload j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_cumulative_interfering_workload
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Abstract_Definitions_cumulative_interfering_workload@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : 
   DecidableEq Job)
  (inst_9 : 
   Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
     inst_3)
  (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
List_foldr_inst3 Nat Nat Nat_add (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (List_map_inst3 Prosa_Behavior_Time_instant Nat
     (fun t : Prosa_Behavior_Time_instant =>
      Prosa_Analysis_Abstract_Definitions_InterferingWorkload_interfering_workload Job
        inst_3
        inst_9
        j t)
     (List_range' t1
        (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
           (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1)
        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Abstract_Definitions_cumulative_interfering_workload Job
  inst_3
  inst_9 j t1 t2
```
