# `no_speculative_execution`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.definitions.no_speculative_execution`
- Lean: `Prosa.Analysis.Abstract.Definitions.no_speculative_execution`
- Certificate: `no_speculative_execution_correspondence`

## Official Rocq

```coq
no_speculative_execution : forall {Job : JobType}, Interference Job -> InterferingWorkload Job -> Prop

no_speculative_execution is not universe polymorphic
Arguments no_speculative_execution {Job H2 H3}
no_speculative_execution is transparent
Expands to: Constant prosa.analysis.abstract.definitions.no_speculative_execution
Declared in library prosa.analysis.abstract.definitions, line 117, characters 13-37
@no_speculative_execution
     : forall Job : JobType, Interference Job -> InterferingWorkload Job -> Prop
```

Body:

```coq
no_speculative_execution =
fun (Job : JobType) (H2 : Interference Job) (H3 : InterferingWorkload Job) =>
forall (j : Equality.sort Job) (t : nat),
is_true (@cumulative_interference Job H2 j 0 t <= @cumulative_interfering_workload Job H3 j 0 t)
     : forall {Job : JobType}, Interference Job -> InterferingWorkload Job -> Prop

Arguments no_speculative_execution {Job H2 H3}
```

## Lean

```lean
@Prosa.Analysis.Abstract.Definitions.no_speculative_execution : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] → Prop
def Prosa.Analysis.Abstract.Definitions.no_speculative_execution.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Analysis.Abstract.Definitions.Interference Job]
    [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] =>
  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Analysis.Abstract.Definitions.cumulative_interference j 0 t ≤
      Prosa.Analysis.Abstract.Definitions.cumulative_interfering_workload j 0 t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_no_speculative_execution
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Analysis_Abstract_Definitions_no_speculative_execution@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                                Job
                                                                                inst_3)
  (inst_9 : Prosa_Analysis_Abstract_Definitions_InterferingWorkload
                                                                                Job
                                                                                inst_3) =>
forall (j : Job) (t : Prosa_Behavior_Time_instant),
LE_le_inst1 Nat instLENat
  (Prosa_Analysis_Abstract_Definitions_cumulative_interference Job
     inst_3
     inst_6 j
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t)
  (Prosa_Analysis_Abstract_Definitions_cumulative_interfering_workload Job
     inst_3
     inst_9 j
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       SProp

Arguments Prosa_Analysis_Abstract_Definitions_no_speculative_execution Job
  inst_3
  inst_6
  inst_9
```
