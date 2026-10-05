# `valid_schedule`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.ready.valid_schedule`
- Lean: `Prosa.Behavior.Ready.valid_schedule`
- Certificate: ``

## Official Rocq

```coq
valid_schedule :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job},
@schedule Job PState -> forall {H0 : JobCost Job}, @JobReady Job PState H0 H -> arrival_sequence Job -> Prop

valid_schedule is not universe polymorphic
Arguments valid_schedule {Job H PState} sched {H0 JobReady0} arr_seq
valid_schedule is transparent
Expands to: Constant prosa.behavior.ready.valid_schedule
Declared in library prosa.behavior.ready, line 73, characters 13-27
@valid_schedule
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job),
       @schedule Job PState ->
       forall H0 : JobCost Job, @JobReady Job PState H0 H -> arrival_sequence Job -> Prop
```

Body:

```coq
valid_schedule =
fun (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
  (H0 : JobCost Job) (JobReady0 : @JobReady Job PState H0 H) (arr_seq : arrival_sequence Job) =>
@jobs_come_from_arrival_sequence Job PState sched arr_seq /\
@jobs_must_be_ready_to_execute Job H PState sched H0 JobReady0
     : forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job},
       @schedule Job PState ->
       forall {H0 : JobCost Job}, @JobReady Job PState H0 H -> arrival_sequence Job -> Prop

Arguments valid_schedule {Job H PState} sched {H0 JobReady0} arr_seq
```

## Lean

```lean
@Prosa.Behavior.Ready.valid_schedule : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
        Prosa.Behavior.Schedule.schedule PState →
          [inst_2 : Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Behavior.Ready.JobReady Job PState] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
def Prosa.Behavior.Ready.valid_schedule.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
        Prosa.Behavior.Schedule.schedule PState →
          [inst_2 : Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Behavior.Ready.JobReady Job PState] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] {PState} sched [Prosa.Behavior.Job.JobCost Job]
    [Prosa.Behavior.Ready.JobReady Job PState] arrSeq =>
  Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arrSeq ∧
    Prosa.Behavior.Ready.jobs_must_be_ready_to_execute sched
```

## Lean, imported into Rocq

```coq
ImportedReady.Prosa_Behavior_Ready_valid_schedule
     : forall (Job : ImportedReady.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedReady.DecidableEq Job)
         (inst_6 : ImportedReady.Prosa_Behavior_Job_JobArrival
                                                                       Job
                                                                       inst_3)
         (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedReady.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       forall
         inst_13 : ImportedReady.Prosa_Behavior_Job_JobCost
                                                                       Job
                                                                       inst_3,
       ImportedReady.Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_13
         inst_6 ->
       ImportedReady.Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp
```

Body:

```coq
ImportedReady.Prosa_Behavior_Ready_valid_schedule@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedReady.Prosa_Behavior_Job_JobType)
  (inst_3 : 
   ImportedReady.DecidableEq Job)
  (inst_6 : 
   ImportedReady.Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : ImportedReady.Prosa_Behavior_Schedule_schedule Job
             inst_3
             PState)
  (inst_13 : 
   ImportedReady.Prosa_Behavior_Job_JobCost Job
     inst_3)
  (inst_16 : 
   ImportedReady.Prosa_Behavior_Ready_JobReady Job
     inst_3
     PState
     inst_13
     inst_6)
  (arrSeq : ImportedReady.Prosa_Behavior_Arrival_sequence_arrival_sequence Job
              inst_3) =>
And
  (ImportedReady.Prosa_Validation_ReadyInterface_jobsComeFromArrivalSequenceProjection Job
     inst_3
     PState sched arrSeq)
  (ImportedReady.Prosa_Validation_ReadyInterface_jobsMustBeReadyToExecuteProjection Job
     inst_3
     inst_6
     PState sched
     inst_13
     inst_16)
     : forall (Job : ImportedReady.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedReady.DecidableEq Job)
         (inst_6 : ImportedReady.Prosa_Behavior_Job_JobArrival
                                                                       Job
                                                                       inst_3)
         (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedReady.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       forall
         inst_13 : ImportedReady.Prosa_Behavior_Job_JobCost
                                                                       Job
                                                                       inst_3,
       ImportedReady.Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_13
         inst_6 ->
       ImportedReady.Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp

Arguments ImportedReady.Prosa_Behavior_Ready_valid_schedule Job
  inst_3
  inst_6 PState sched
  inst_13
  inst_16 arrSeq
```
