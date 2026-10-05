# `served_job_at`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.service.served_job_at`
- Lean: `Prosa.Analysis.Definitions.Service.served_job_at`
- Certificate: `served_job_at_correspondence`

## Official Rocq

```coq
served_job_at :
forall {Job : JobType} {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> instant -> option (Equality.sort Job)

served_job_at is not universe polymorphic
Arguments served_job_at {Job PState} arr_seq sched t
served_job_at is transparent
Expands to: Constant prosa.analysis.definitions.service.served_job_at
Declared in library prosa.analysis.definitions.service, line 26, characters 13-26
@served_job_at
     : forall (Job : JobType) (PState : ProcessorState Job),
       arrival_sequence Job -> @schedule Job PState -> instant -> option (Equality.sort Job)
```

Body:

```coq
served_job_at =
fun (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (t : instant) =>
@ohead (Equality.sort Job) (@served_jobs_at Job PState arr_seq sched t)
     : forall {Job : JobType} {PState : ProcessorState Job},
       arrival_sequence Job -> @schedule Job PState -> instant -> option (Equality.sort Job)

Arguments served_job_at {Job PState} arr_seq sched t
```

## Lean

```lean
@Prosa.Analysis.Definitions.Service.served_job_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Option Job
def Prosa.Analysis.Definitions.Service.served_job_at.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Option Job :=
fun {Job} [DecidableEq Job] {PState} arr_seq sched t =>
  (Prosa.Analysis.Definitions.Service.served_jobs_at arr_seq sched t).head?
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Service_served_job_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> Option Job
```

Body:

```coq
Prosa_Analysis_Definitions_Service_served_job_at@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
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
List_head__q Job
  (Prosa_Analysis_Definitions_Service_served_jobs_at Job
     inst_3 PState arr_seq sched t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> Option Job

Arguments Prosa_Analysis_Definitions_Service_served_job_at Job
  inst_3 PState arr_seq 
  sched t
```
