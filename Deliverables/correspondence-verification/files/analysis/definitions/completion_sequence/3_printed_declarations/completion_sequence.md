# `completion_sequence`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.completion_sequence.completion_sequence`
- Lean: `Prosa.Analysis.Definitions.CompletionSequence.completion_sequence`
- Certificate: `completion_sequence_correspondence`

## Official Rocq

```coq
completion_sequence :
forall {Job : job.JobType},
job.JobCost Job ->
forall {PState : schedule.ProcessorState Job},
arrival_sequence.arrival_sequence Job ->
@schedule.schedule Job PState -> arrival_sequence.arrival_sequence Job

completion_sequence is not universe polymorphic
Arguments completion_sequence {Job H PState} arr_seq sched _
completion_sequence is transparent
Expands to: Constant prosa.analysis.definitions.completion_sequence.completion_sequence
Declared in library prosa.analysis.definitions.completion_sequence, line 23, characters 13-32
@completion_sequence
     : forall Job : job.JobType,
       job.JobCost Job ->
       forall PState : schedule.ProcessorState Job,
       arrival_sequence.arrival_sequence Job ->
       @schedule.schedule Job PState -> arrival_sequence.arrival_sequence Job
```

Body:

```coq
completion_sequence =
fun (Job : job.JobType) (H : job.JobCost Job) (PState : schedule.ProcessorState Job)
  (arr_seq : arrival_sequence.arrival_sequence Job) (sched : @schedule.schedule Job PState)
  (t : time.instant) =>
     : forall {Job : job.JobType},
       job.JobCost Job ->
       forall {PState : schedule.ProcessorState Job},
       arrival_sequence.arrival_sequence Job ->
       @schedule.schedule Job PState -> arrival_sequence.arrival_sequence Job

Arguments completion_sequence {Job H PState} arr_seq sched _
```

## Lean

```lean
@Prosa.Analysis.Definitions.CompletionSequence.completion_sequence : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Arrival_sequence.arrival_sequence Job
def Prosa.Analysis.Definitions.CompletionSequence.completion_sequence.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Arrival_sequence.arrival_sequence Job :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched t =>
  List.filter (fun j => Prosa.Behavior.Service.completes_at sched j t)
    (Prosa.Behavior.Arrival_sequence.arrivals_up_to arr_seq t)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_CompletionSequence_completion_sequence
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3
```

Body:

```coq
Prosa_Analysis_Definitions_CompletionSequence_completion_sequence@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobCost Job
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (t : Prosa_Behavior_Time_instant) =>
List_filter Job
  (fun j : Job =>
   Prosa_Behavior_Service_completes_at Job
     inst_3 PState sched
     inst_6 j t)
  (Prosa_Behavior_Arrival_sequence_arrivals_up_to Job
     inst_3 arr_seq t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3

Arguments Prosa_Analysis_Definitions_CompletionSequence_completion_sequence Job
  inst_3
  inst_6 
  PState arr_seq sched a____at____internal__hyg0
```
