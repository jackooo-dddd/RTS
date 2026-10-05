# `scheduled_jobs_at`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.scheduled.scheduled_jobs_at`
- Lean: `Prosa.Model.Schedule.Scheduled.scheduled_jobs_at`
- Certificate: `scheduled_jobs_at_correspondence`

## Official Rocq

```coq
scheduled_jobs_at :
forall {Job : JobType} {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> instant -> seq (Equality.sort Job)

scheduled_jobs_at is not universe polymorphic
Arguments scheduled_jobs_at {Job PState} arr_seq sched t
scheduled_jobs_at is transparent
Expands to: Constant prosa.model.schedule.scheduled.scheduled_jobs_at
Declared in library prosa.model.schedule.scheduled, line 27, characters 13-30
@scheduled_jobs_at
     : forall (Job : JobType) (PState : ProcessorState Job),
       arrival_sequence Job -> @schedule Job PState -> instant -> seq (Equality.sort Job)
```

Body:

```coq
scheduled_jobs_at =
fun (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (t : instant) =>
     : forall {Job : JobType} {PState : ProcessorState Job},
       arrival_sequence Job -> @schedule Job PState -> instant -> seq (Equality.sort Job)

Arguments scheduled_jobs_at {Job PState} arr_seq sched t
```

## Lean

```lean
@Prosa.Model.Schedule.Scheduled.scheduled_jobs_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → List Job
def Prosa.Model.Schedule.Scheduled.scheduled_jobs_at.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → List Job :=
fun {Job} [DecidableEq Job] {PState} arr_seq sched t =>
  List.filter (fun j => Prosa.Behavior.Service.scheduled_at sched j t)
    (Prosa.Behavior.Arrival_sequence.arrivals_up_to arr_seq t)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Scheduled_scheduled_jobs_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> List Job
```

Body:

```coq
Prosa_Model_Schedule_Scheduled_scheduled_jobs_at@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (t : Prosa_Behavior_Time_instant) =>
List_filter Job
  (fun j : Job =>
   Prosa_Behavior_Service_scheduled_at Job
     inst_3 PState sched j t)
  (Prosa_Behavior_Arrival_sequence_arrivals_up_to Job
     inst_3 arr_seq t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> List Job

Arguments Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job
  inst_3 PState arr_seq 
  sched t
```
