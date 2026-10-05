# `jobs_backlogged_at`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.work_conserving.jobs_backlogged_at`
- Lean: `Prosa.Model.Schedule.WorkConserving.jobs_backlogged_at`
- Certificate: `jobs_backlogged_at_correspondence`

## Official Rocq

```coq
jobs_backlogged_at :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
@JobReady Job PState H0 H ->
arrival_sequence Job -> @schedule Job PState -> instant -> seq (Equality.sort Job)

jobs_backlogged_at is not universe polymorphic
Arguments jobs_backlogged_at {Job H H0 PState jr} arr_seq sched t
jobs_backlogged_at is transparent
Expands to: Constant prosa.model.schedule.work_conserving.jobs_backlogged_at
Declared in library prosa.model.schedule.work_conserving, line 45, characters 13-31
@jobs_backlogged_at
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job),
       @JobReady Job PState H0 H ->
       arrival_sequence Job -> @schedule Job PState -> instant -> seq (Equality.sort Job)
```

Body:

```coq
jobs_backlogged_at =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
  (jr : @JobReady Job PState H0 H) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  (t : instant) =>
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
       @JobReady Job PState H0 H ->
       arrival_sequence Job -> @schedule Job PState -> instant -> seq (Equality.sort Job)

Arguments jobs_backlogged_at {Job H H0 PState jr} arr_seq sched t
```

## Lean

```lean
@Prosa.Model.Schedule.WorkConserving.jobs_backlogged_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → List Job
def Prosa.Model.Schedule.WorkConserving.jobs_backlogged_at.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → List Job :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState}
    [Prosa.Behavior.Ready.JobReady Job PState] arrSeq sched t =>
  List.filter (fun j => Prosa.Behavior.Ready.backlogged sched j t)
    (Prosa.Behavior.Arrival_sequence.arrivals_up_to arrSeq t)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_9
         inst_6 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> List Job
```

Body:

```coq
Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (inst_9 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (inst_14 : Prosa_Behavior_Ready_JobReady
                                                                                Job
                                                                                inst_3
                                                                                PState
                                                                                inst_9
                                                                                inst_6)
  (arrSeq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (t : Prosa_Behavior_Time_instant) =>
List_filter Job
  (fun j : Job =>
   Prosa_Behavior_Ready_backlogged Job
     inst_3 PState
     inst_9
     inst_6
     inst_14 sched j t)
  (Prosa_Behavior_Arrival_sequence_arrivals_up_to Job
     inst_3 arrSeq t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_9
         inst_6 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> List Job

Arguments Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at Job
  inst_3
  inst_6
  inst_9 PState
  inst_14 arrSeq 
  sched t
```
