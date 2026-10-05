# `is_idle`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.scheduled.is_idle`
- Lean: `Prosa.Model.Schedule.Scheduled.is_idle`
- Certificate: `is_idle_correspondence`

## Official Rocq

```coq
is_idle :
forall {Job : JobType} {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> instant -> bool

is_idle is not universe polymorphic
Arguments is_idle {Job PState} arr_seq sched t
is_idle is transparent
Expands to: Constant prosa.model.schedule.scheduled.is_idle
Declared in library prosa.model.schedule.scheduled, line 36, characters 13-20
@is_idle
     : forall (Job : JobType) (PState : ProcessorState Job),
       arrival_sequence Job -> @schedule Job PState -> instant -> bool
```

Body:

```coq
is_idle =
fun (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (t : instant) =>
@scheduled_jobs_at Job PState arr_seq sched t == [::]
     : forall {Job : JobType} {PState : ProcessorState Job},
       arrival_sequence Job -> @schedule Job PState -> instant -> bool

Arguments is_idle {Job PState} arr_seq sched t
```

## Lean

```lean
@Prosa.Model.Schedule.Scheduled.is_idle : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Bool
def Prosa.Model.Schedule.Scheduled.is_idle.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} arr_seq sched t =>
  (Prosa.Model.Schedule.Scheduled.scheduled_jobs_at arr_seq sched t).isEmpty
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Scheduled_is_idle
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Model_Schedule_Scheduled_is_idle@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0
Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (t : Prosa_Behavior_Time_instant) =>
List_isEmpty Job
  (Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job
     inst_3 PState arr_seq sched t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Model_Schedule_Scheduled_is_idle Job
  inst_3 PState arr_seq 
  sched t
```
