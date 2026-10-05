# `supply_at`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.supply.supply_at`
- Lean: `Prosa.Model.Processor.Supply.supply_at`
- Certificate: ``

## Official Rocq

```coq
supply_at : forall {Job : JobType} {PState : ProcessorState Job}, @schedule Job PState -> instant -> work

supply_at is not universe polymorphic
Arguments supply_at {Job PState} sched t
supply_at is transparent
Expands to: Constant prosa.model.processor.supply.supply_at
Declared in library prosa.model.processor.supply, line 15, characters 13-22
@supply_at
     : forall (Job : JobType) (PState : ProcessorState Job), @schedule Job PState -> instant -> work
```

Body:

```coq
supply_at =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (t : instant) =>
@supply_in Job PState (sched t)
     : forall {Job : JobType} {PState : ProcessorState Job}, @schedule Job PState -> instant -> work

Arguments supply_at {Job PState} sched t
```

## Lean

```lean
@Prosa.Model.Processor.Supply.supply_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work
def Prosa.Model.Processor.Supply.supply_at.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] {PState} sched t => PState.supply_in (sched t)
```

## Lean, imported into Rocq

```coq
ImportedSupply.Prosa_Model_Processor_Supply_supply_at
     : forall (Job : ImportedSupply.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedSupply.DecidableEq Job)
         (PState : ImportedSupply.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedSupply.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedSupply.Prosa_Behavior_Time_instant -> ImportedSupply.Prosa_Behavior_Job_work
```

Body:

```coq
ImportedSupply.Prosa_Model_Processor_Supply_supply_at@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedSupply.Prosa_Behavior_Job_JobType)
  (inst_3 : 
   ImportedSupply.DecidableEq Job)
  (PState : ImportedSupply.Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : ImportedSupply.Prosa_Behavior_Schedule_schedule Job
             inst_3
             PState)
  (t : ImportedSupply.Prosa_Behavior_Time_instant) =>
ImportedSupply.Prosa_Behavior_Schedule_ProcessorState_supply_in Job
  inst_3
  PState (sched t)
     : forall (Job : ImportedSupply.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedSupply.DecidableEq Job)
         (PState : ImportedSupply.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedSupply.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedSupply.Prosa_Behavior_Time_instant -> ImportedSupply.Prosa_Behavior_Job_work

Arguments ImportedSupply.Prosa_Model_Processor_Supply_supply_at Job
  inst_3 PState sched 
  t
```
