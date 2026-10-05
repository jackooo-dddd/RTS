# `service_of_higher_or_equal_priority_jobs`

- Kind (Rocq): Definition
- Rocq: `prosa.model.aggregate.service_of_jobs.service_of_higher_or_equal_priority_jobs`
- Lean: `Prosa.Model.Aggregate.ServiceOfJobs.service_of_higher_or_equal_priority_jobs`
- Certificate: `service_of_higher_or_equal_priority_jobs_correspondence`

## Official Rocq

```coq
service_of_higher_or_equal_priority_jobs :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState ->
JLFP_policy Job -> seq (Equality.sort Job) -> Equality.sort Job -> instant -> instant -> nat

service_of_higher_or_equal_priority_jobs is not universe polymorphic
Arguments service_of_higher_or_equal_priority_jobs {Job PState} sched {H0} jobs%seq_scope j t1 t2
service_of_higher_or_equal_priority_jobs is transparent
Expands to: Constant prosa.model.aggregate.service_of_jobs.service_of_higher_or_equal_priority_jobs
Declared in library prosa.model.aggregate.service_of_jobs, line 64, characters 15-55
@service_of_higher_or_equal_priority_jobs
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState ->
       JLFP_policy Job -> seq (Equality.sort Job) -> Equality.sort Job -> instant -> instant -> nat
```

Body:

```coq
service_of_higher_or_equal_priority_jobs =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (H0 : JLFP_policy Job) (jobs : seq (Equality.sort Job)) (j : Equality.sort Job) =>
let of_higher_or_equal_priority := (@hep_job Job H0)^~ j in
fun t1 : instant => [eta @service_of_jobs Job PState sched of_higher_or_equal_priority jobs t1]
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState ->
       JLFP_policy Job -> seq (Equality.sort Job) -> Equality.sort Job -> instant -> instant -> nat

Arguments service_of_higher_or_equal_priority_jobs {Job PState} sched {H0} jobs%seq_scope j t1 t2
```

## Lean

```lean
@Prosa.Model.Aggregate.ServiceOfJobs.service_of_higher_or_equal_priority_jobs : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
          List Job → Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Model.Aggregate.ServiceOfJobs.service_of_higher_or_equal_priority_jobs.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
          List Job → Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] {PState} sched [Prosa.Model.Priority.Definitions.JLFP_policy Job] jobs j t1 t2 =>
  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched
    (fun j_hp => Prosa.Model.Priority.Definitions.hep_job j_hp j) jobs t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Model_Aggregate_ServiceOfJobs_service_of_higher_or_equal_priority_jobs
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       List Job -> Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Model_Aggregate_ServiceOfJobs_service_of_higher_or_equal_priority_jobs@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (inst_10 : Prosa_Model_Priority_Definitions_JLFP_policy
                                                                                Job
                                                                                inst_3)
  (jobs : List Job) (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
  inst_3 PState sched
  (fun j_hp : Job =>
   Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
     inst_3
     inst_10 j_hp j)
  jobs t1 t2
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       List Job -> Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Model_Aggregate_ServiceOfJobs_service_of_higher_or_equal_priority_jobs 
  Job inst_3 PState 
  sched inst_10 
  jobs j t1 t
```
