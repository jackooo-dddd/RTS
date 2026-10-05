# `has_supply`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.supply.has_supply`
- Lean: `Prosa.Model.Processor.Supply.has_supply`
- Certificate: ``

## Official Rocq

```coq
has_supply : forall {Job : JobType} {PState : ProcessorState Job}, @schedule Job PState -> instant -> bool

has_supply is not universe polymorphic
Arguments has_supply {Job PState} sched t
has_supply is transparent
Expands to: Constant prosa.model.processor.supply.has_supply
Declared in library prosa.model.processor.supply, line 25, characters 13-23
@has_supply
     : forall (Job : JobType) (PState : ProcessorState Job), @schedule Job PState -> instant -> bool
```

Body:

```coq
has_supply =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (t : instant) =>
0 < @supply_at Job PState sched t
     : forall {Job : JobType} {PState : ProcessorState Job}, @schedule Job PState -> instant -> bool

Arguments has_supply {Job PState} sched t
```

## Lean

```lean
@Prosa.Model.Processor.Supply.has_supply : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Bool
def Prosa.Model.Processor.Supply.has_supply.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} sched t => decide (0 < Prosa.Model.Processor.Supply.supply_at sched t)
```

## Lean, imported into Rocq

```coq
ImportedSupply.Prosa_Model_Processor_Supply_has_supply
     : forall (Job : ImportedSupply.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedSupply.DecidableEq Job)
         (PState : ImportedSupply.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedSupply.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedSupply.Prosa_Behavior_Time_instant -> ImportedSupply.Bool
```

Body:

```coq
ImportedSupply.Prosa_Model_Processor_Supply_has_supply@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedSupply.Prosa_Behavior_Job_JobType)
  (inst_3 : 
   ImportedSupply.DecidableEq Job)
  (PState : ImportedSupply.Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : ImportedSupply.Prosa_Behavior_Schedule_schedule Job
             inst_3
             PState)
  (t : ImportedSupply.Prosa_Behavior_Time_instant) =>
ImportedSupply.Decidable_decide
  (ImportedSupply.LT_lt_inst1 ImportedSupply.Prosa_Behavior_Job_work ImportedSupply.instLTNat
     (ImportedSupply.OfNat_ofNat_inst1 ImportedSupply.Prosa_Behavior_Job_work 0
        (ImportedSupply.instOfNatNat 0))
     (ImportedSupply.Prosa_Validation_SupplyInterface_supplyAtProjection Job
        inst_3
        PState sched t))
  (ImportedSupply.Nat_decLt
     (ImportedSupply.OfNat_ofNat_inst1 ImportedSupply.Prosa_Behavior_Job_work 0
        (ImportedSupply.instOfNatNat 0))
     (ImportedSupply.Prosa_Validation_SupplyInterface_supplyAtProjection Job
        inst_3
        PState sched t))
     : forall (Job : ImportedSupply.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedSupply.DecidableEq Job)
         (PState : ImportedSupply.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedSupply.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedSupply.Prosa_Behavior_Time_instant -> ImportedSupply.Bool

Arguments ImportedSupply.Prosa_Model_Processor_Supply_has_supply Job
  inst_3 PState sched 
  t
```
