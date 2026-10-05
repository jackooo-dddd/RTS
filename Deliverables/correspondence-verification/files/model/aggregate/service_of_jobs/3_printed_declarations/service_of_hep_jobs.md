# `service_of_hep_jobs`

- Kind (Rocq): Definition
- Rocq: `prosa.model.aggregate.service_of_jobs.service_of_hep_jobs`
- Lean: `Prosa.Model.Aggregate.ServiceOfJobs.service_of_hep_jobs`
- Certificate: `service_of_hep_jobs_correspondence`

## Official Rocq

```coq
service_of_hep_jobs :
forall {Job : JobType} {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> nat

service_of_hep_jobs is not universe polymorphic
Arguments service_of_hep_jobs {Job PState} arr_seq sched {H0} j t1 t2
service_of_hep_jobs is transparent
Expands to: Constant prosa.model.aggregate.service_of_jobs.service_of_hep_jobs
Declared in library prosa.model.aggregate.service_of_jobs, line 86, characters 15-34
@service_of_hep_jobs
     : forall (Job : JobType) (PState : ProcessorState Job),
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> nat
```

Body:

```coq
service_of_hep_jobs =
fun (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (H0 : JLFP_policy Job) (j : Equality.sort Job) (t1 t2 : instant) =>
@service_of_jobs Job PState sched ((@hep_job Job H0)^~ j) (@arrivals_between Job arr_seq t1 t2) t1 t2
     : forall {Job : JobType} {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> nat

Arguments service_of_hep_jobs {Job PState} arr_seq sched {H0} j t1 t2
```

## Lean

```lean
@Prosa.Model.Aggregate.ServiceOfJobs.service_of_hep_jobs : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
            Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Model.Aggregate.ServiceOfJobs.service_of_hep_jobs.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
            Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] {PState} arr_seq sched [Prosa.Model.Priority.Definitions.JLFP_policy Job] j t1 t2 =>
  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched (fun jhp => Prosa.Model.Priority.Definitions.hep_job jhp j)
    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Model_Aggregate_ServiceOfJobs_service_of_hep_jobs
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Model_Aggregate_ServiceOfJobs_service_of_hep_jobs@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (inst_12 : Prosa_Model_Priority_Definitions_JLFP_policy
                                                                                Job
                                                                                inst_3)
  (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
  inst_3 PState sched
  (fun jhp : Job =>
   Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
     inst_3
     inst_12 jhp j)
  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
     inst_3 arr_seq t1 t2)
  t1 t2
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Model_Aggregate_ServiceOfJobs_service_of_hep_jobs Job
  inst_3 PState 
  arr_seq sched inst_12 
  j t1 t
```
