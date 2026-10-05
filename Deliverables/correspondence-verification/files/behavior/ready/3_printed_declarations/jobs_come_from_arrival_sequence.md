# `jobs_come_from_arrival_sequence`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.ready.jobs_come_from_arrival_sequence`
- Lean: `Prosa.Behavior.Ready.jobs_come_from_arrival_sequence`
- Certificate: ``

## Official Rocq

```coq
jobs_come_from_arrival_sequence :
forall {Job : JobType} {PState : ProcessorState Job}, @schedule Job PState -> arrival_sequence Job -> Prop

jobs_come_from_arrival_sequence is not universe polymorphic
Arguments jobs_come_from_arrival_sequence {Job PState} sched arr_seq
jobs_come_from_arrival_sequence is transparent
Expands to: Constant prosa.behavior.ready.jobs_come_from_arrival_sequence
Declared in library prosa.behavior.ready, line 51, characters 13-44
@jobs_come_from_arrival_sequence
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> arrival_sequence Job -> Prop
```

Body:

```coq
jobs_come_from_arrival_sequence =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
  (arr_seq : arrival_sequence Job) =>
forall (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) -> @arrives_in Job arr_seq j
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> arrival_sequence Job -> Prop

Arguments jobs_come_from_arrival_sequence {Job PState} sched arr_seq
```

## Lean

```lean
@Prosa.Behavior.Ready.jobs_come_from_arrival_sequence : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
def Prosa.Behavior.Ready.jobs_come_from_arrival_sequence.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Job} [DecidableEq Job] {PState} sched arrSeq =>
  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Service.scheduled_at sched j t = true → Prosa.Behavior.Arrival_sequence.arrives_in arrSeq j
```

## Lean, imported into Rocq

```coq
ImportedReady.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence
     : forall (Job : ImportedReady.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedReady.DecidableEq Job)
         (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedReady.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedReady.Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp
```

Body:

```coq
ImportedReady.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedReady.Prosa_Behavior_Job_JobType)
  (inst_3 : 
   ImportedReady.DecidableEq Job)
  (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : ImportedReady.Prosa_Behavior_Schedule_schedule Job
             inst_3
             PState)
  (arrSeq : ImportedReady.Prosa_Behavior_Arrival_sequence_arrival_sequence Job
              inst_3) =>
forall (j : Job) (t : ImportedReady.Prosa_Behavior_Time_instant),
@eq ImportedReady.Bool
  (ImportedReady.Prosa_Behavior_Service_scheduled_at Job
     inst_3
     PState sched j t)
  ImportedReady.Bool_true ->
ImportedReady.Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arrSeq j
     : forall (Job : ImportedReady.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedReady.DecidableEq Job)
         (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedReady.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedReady.Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp

Arguments ImportedReady.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
  inst_3 PState sched arrSeq
```
