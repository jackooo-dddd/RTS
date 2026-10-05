# `cumul_intra_interference`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.IBF.supply.cumul_intra_interference`
- Lean: `Prosa.Analysis.Abstract.IBF.Supply.cumul_intra_interference`
- Certificate: `cumul_intra_interference_correspondence`

## Official Rocq

```coq
cumul_intra_interference :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> Interference Job -> Equality.sort Job -> nat -> nat -> nat

cumul_intra_interference is not universe polymorphic
Arguments cumul_intra_interference {Job PState} sched {H2} j (t1 t2)%nat_scope
cumul_intra_interference is transparent
Expands to: Constant prosa.analysis.abstract.IBF.supply.cumul_intra_interference
Declared in library prosa.analysis.abstract.IBF.supply, line 58, characters 13-37
@cumul_intra_interference
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> Interference Job -> Equality.sort Job -> nat -> nat -> nat
```

Body:

```coq
cumul_intra_interference =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (H2 : Interference Job) (j : Equality.sort Job) (t1 : nat) =>
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> Interference Job -> Equality.sort Job -> nat -> nat -> nat

Arguments cumul_intra_interference {Job PState} sched {H2} j (t1 t2)%nat_scope
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Supply.cumul_intra_interference : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → [Prosa.Analysis.Abstract.Definitions.Interference Job] → Job → ℕ → ℕ → ℕ
```

Body:

```lean
def Prosa.Analysis.Abstract.IBF.Supply.cumul_intra_interference.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Analysis.Abstract.Definitions.Interference Job] → Job → ℕ → ℕ → ℕ :=
fun {Job} [DecidableEq Job] {PState} sched [Prosa.Analysis.Abstract.Definitions.Interference Job] j t1 t2 =>
  Prosa.Analysis.Abstract.Definitions.cumul_cond_interference
    (fun x t => Prosa.Model.Processor.Supply.has_supply sched t) j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Supply_cumul_intra_interference
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Job -> Nat -> Nat -> Nat
```

Body:

```coq
Prosa_Analysis_Abstract_IBF_Supply_cumul_intra_interference@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (inst_10 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                                Job
                                                                                inst_3)
  (j : Job) (t1 t2 : Nat) =>
Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
  inst_3
  inst_10
  (fun (_ : Job) (t : Prosa_Behavior_Time_instant) =>
   Prosa_Model_Processor_Supply_has_supply Job
     inst_3 PState sched t)
  j t1 t2
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Job -> Nat -> Nat -> Nat

Arguments Prosa_Analysis_Abstract_IBF_Supply_cumul_intra_interference Job
  inst_3 PState 
  sched inst_10 
  j (x n)%_Nat_scope
```
