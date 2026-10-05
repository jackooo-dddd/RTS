# `is_blackout`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.supply.is_blackout`
- Lean: `Prosa.Model.Processor.Supply.is_blackout`
- Certificate: ``

## Official Rocq

```coq
is_blackout : forall {Job : JobType} {PState : ProcessorState Job}, @schedule Job PState -> instant -> bool

is_blackout is not universe polymorphic
Arguments is_blackout {Job PState} sched t
is_blackout is transparent
Expands to: Constant prosa.model.processor.supply.is_blackout
Declared in library prosa.model.processor.supply, line 29, characters 13-24
@is_blackout
     : forall (Job : JobType) (PState : ProcessorState Job), @schedule Job PState -> instant -> bool
```

Body:

```coq
is_blackout =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (t : instant) =>
~~ @has_supply Job PState sched t
     : forall {Job : JobType} {PState : ProcessorState Job}, @schedule Job PState -> instant -> bool

Arguments is_blackout {Job PState} sched t
```

## Lean

```lean
@Prosa.Model.Processor.Supply.is_blackout : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Bool
def Prosa.Model.Processor.Supply.is_blackout.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} sched t => !Prosa.Model.Processor.Supply.has_supply sched t
```

## Lean, imported into Rocq

```coq
ImportedSupply.Prosa_Model_Processor_Supply_is_blackout
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
ImportedSupply.Prosa_Model_Processor_Supply_is_blackout@{u_1 u_2 u_3 Lean.u_1+1.0
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
ImportedSupply.Bool_not
  (ImportedSupply.Prosa_Validation_SupplyInterface_hasSupplyProjection Job
     inst_3
     PState sched t)
     : forall (Job : ImportedSupply.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedSupply.DecidableEq Job)
         (PState : ImportedSupply.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedSupply.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedSupply.Prosa_Behavior_Time_instant -> ImportedSupply.Bool

Arguments ImportedSupply.Prosa_Model_Processor_Supply_is_blackout Job
  inst_3 PState sched 
  t
```
