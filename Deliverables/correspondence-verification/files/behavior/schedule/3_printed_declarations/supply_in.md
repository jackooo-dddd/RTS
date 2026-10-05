# `supply_in`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.schedule.supply_in`
- Lean: `Prosa.Behavior.Schedule.ProcessorState.supply_in`
- Certificate: ``

## Official Rocq

```coq
supply_in : forall {Job : JobType} {State0 : ProcessorState Job}, @State Job State0 -> work

supply_in is not universe polymorphic
Arguments supply_in {Job State} s
supply_in is transparent
Expands to: Constant prosa.behavior.schedule.supply_in
Declared in library prosa.behavior.schedule, line 82, characters 13-22
@supply_in
     : forall (Job : JobType) (State0 : ProcessorState Job), @State Job State0 -> work
```

Body:

```coq
supply_in =
fun (Job : JobType) (State0 : ProcessorState Job) (s : @State Job State0) => \sum_r @supply_on Job State0 s r
     : forall {Job : JobType} {State0 : ProcessorState Job}, @State Job State0 -> work

Arguments supply_in {Job State} s
```

## Lean

```lean
@Prosa.Behavior.Schedule.ProcessorState.supply_in : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    (PState : Prosa.Behavior.Schedule.ProcessorState Job) →
      Prosa.Behavior.Schedule.ProcessorState.State Job → Prosa.Behavior.Job.work
def Prosa.Behavior.Schedule.ProcessorState.supply_in.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    (PState : Prosa.Behavior.Schedule.ProcessorState Job) →
      Prosa.Behavior.Schedule.ProcessorState.State Job → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] PState s => ∑ c, Prosa.Behavior.Schedule.supply_on s c
```

## Lean, imported into Rocq

```coq
ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_supply_in
     : forall (Job : ImportedSchedule.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedSchedule.DecidableEq Job)
         (PState : ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState ->
       ImportedSchedule.Prosa_Behavior_Job_work
```

Body:

```coq
ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_supply_in@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedSchedule.Prosa_Behavior_Job_JobType)
  (inst_3 : ImportedSchedule.DecidableEq Job)
  (PState : ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (s : ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState) =>
ImportedSchedule.Finset_sum_inst2
  (ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_Core Job
     inst_3 PState)
  ImportedSchedule.Prosa_Behavior_Job_work ImportedSchedule.Nat_instAddCommMonoid
  (ImportedSchedule.Finset_univ
     (ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_Core Job
        inst_3 PState)
     (ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_instFintypeCore Job
        inst_3 PState))
  (fun
     c : ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_Core Job
           inst_3 PState =>
   ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_supply_on Job
     inst_3 PState s c)
     : forall (Job : ImportedSchedule.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedSchedule.DecidableEq Job)
         (PState : ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState ->
       ImportedSchedule.Prosa_Behavior_Job_work

Arguments ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_supply_in Job
  inst_3 PState s
```
