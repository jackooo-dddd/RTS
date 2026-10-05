# `cumulative_interference`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.definitions.cumulative_interference`
- Lean: `Prosa.Analysis.Abstract.Definitions.cumulative_interference`
- Certificate: `cumulative_interference_correspondence`

## Official Rocq

```coq
cumulative_interference : forall {Job : JobType}, Interference Job -> Equality.sort Job -> nat -> nat -> nat

cumulative_interference is not universe polymorphic
Arguments cumulative_interference {Job H2} j (t1 t2)%nat_scope
cumulative_interference is transparent
Expands to: Constant prosa.analysis.abstract.definitions.cumulative_interference
Declared in library prosa.analysis.abstract.definitions, line 98, characters 13-36
@cumulative_interference
     : forall Job : JobType, Interference Job -> Equality.sort Job -> nat -> nat -> nat
```

Body:

```coq
cumulative_interference =
fun (Job : JobType) (H2 : Interference Job) (j : Equality.sort Job) (t1 : nat) =>
     : forall {Job : JobType}, Interference Job -> Equality.sort Job -> nat -> nat -> nat

Arguments cumulative_interference {Job H2} j (t1 t2)%nat_scope
```

## Lean

```lean
@Prosa.Analysis.Abstract.Definitions.cumulative_interference : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
def Prosa.Analysis.Abstract.Definitions.cumulative_interference.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Analysis.Abstract.Definitions.Interference Job] j t1 t2 =>
  Prosa.Analysis.Abstract.Definitions.cumul_cond_interference (fun x x_1 => true) j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_cumulative_interference
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Abstract_Definitions_cumulative_interference@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                                Job
                                                                                inst_3)
  (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
  inst_3
  inst_6
  (fun (_ : Job) (_ : Prosa_Behavior_Time_instant) => Bool_true) j t1 t2
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Abstract_Definitions_cumulative_interference Job
  inst_3
  inst_6 j t1 t2
```
