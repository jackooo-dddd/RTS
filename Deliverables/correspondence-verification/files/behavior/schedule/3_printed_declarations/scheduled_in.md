# `scheduled_in`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.schedule.scheduled_in`
- Lean: `Prosa.Behavior.Schedule.ProcessorState.scheduled_in`
- Certificate: ``

## Official Rocq

```coq
scheduled_in :
forall {Job : JobType} {State0 : ProcessorState Job}, Equality.sort Job -> @State Job State0 -> bool

scheduled_in is not universe polymorphic
Arguments scheduled_in {Job State} j s
scheduled_in is transparent
Expands to: Constant prosa.behavior.schedule.scheduled_in
Declared in library prosa.behavior.schedule, line 77, characters 13-25
@scheduled_in
     : forall (Job : JobType) (State0 : ProcessorState Job), Equality.sort Job -> @State Job State0 -> bool
```

Body:

```coq
scheduled_in =
fun (Job : JobType) (State0 : ProcessorState Job) (j : Equality.sort Job) (s : @State Job State0) =>
     : forall {Job : JobType} {State0 : ProcessorState Job}, Equality.sort Job -> @State Job State0 -> bool

Arguments scheduled_in {Job State} j s
```

## Lean

```lean
@Prosa.Behavior.Schedule.ProcessorState.scheduled_in : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    (PState : Prosa.Behavior.Schedule.ProcessorState Job) →
      Job → Prosa.Behavior.Schedule.ProcessorState.State Job → Bool
def Prosa.Behavior.Schedule.ProcessorState.scheduled_in.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    (PState : Prosa.Behavior.Schedule.ProcessorState Job) →
      Job → Prosa.Behavior.Schedule.ProcessorState.State Job → Bool :=
fun {Job} [DecidableEq Job] PState j s =>
  Finset.fold or false (fun c => Prosa.Behavior.Schedule.scheduled_on j s c) Finset.univ
```

## Lean, imported into Rocq

```coq
ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_scheduled_in
     : forall (Job : ImportedSchedule.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedSchedule.DecidableEq Job)
         (PState : ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Job ->
       ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState ->
       ImportedSchedule.Bool
```

Body:

```coq
ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_scheduled_in@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedSchedule.Prosa_Behavior_Job_JobType)
  (inst_3 : ImportedSchedule.DecidableEq Job)
  (PState : ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (j : Job)
  (s : ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState) =>
ImportedSchedule.Finset_fold_inst2
  (ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_Core Job
     inst_3 PState)
  ImportedSchedule.Bool ImportedSchedule.Bool_or
  ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_instCommutativeBoolOr
  ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_instAssociativeBoolOr ImportedSchedule.Bool_false
  (fun
     c : ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_Core Job
           inst_3 PState =>
   ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_scheduled_on Job
     inst_3 PState j s c)
  (ImportedSchedule.Finset_univ
     (ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_Core Job
        inst_3 PState)
     (ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_instFintypeCore Job
        inst_3 PState))
     : forall (Job : ImportedSchedule.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedSchedule.DecidableEq Job)
         (PState : ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Job ->
       ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_State Job
         inst_3 PState ->
       ImportedSchedule.Bool

Arguments ImportedSchedule.Prosa_Behavior_Schedule_ProcessorState_scheduled_in Job
  inst_3 PState j s
```
