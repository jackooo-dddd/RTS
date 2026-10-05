# `workload_of_hep_jobs`

- Kind (Rocq): Definition
- Rocq: `prosa.model.aggregate.workload.workload_of_hep_jobs`
- Lean: `Prosa.Model.Aggregate.Workload.workload_of_hep_jobs`
- Certificate: `workload_of_hep_jobs_correspondence`

## Official Rocq

```coq
workload_of_hep_jobs :
forall {Job : JobType},
JobCost Job -> arrival_sequence Job -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> nat

workload_of_hep_jobs is not universe polymorphic
Arguments workload_of_hep_jobs {Job H1} arr_seq {H2} j t1 t2
workload_of_hep_jobs is transparent
Expands to: Constant prosa.model.aggregate.workload.workload_of_hep_jobs
Declared in library prosa.model.aggregate.workload, line 59, characters 15-35
@workload_of_hep_jobs
     : forall Job : JobType,
       JobCost Job ->
       arrival_sequence Job -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> nat
```

Body:

```coq
workload_of_hep_jobs =
fun (Job : JobType) (H1 : JobCost Job) (arr_seq : arrival_sequence Job) (H2 : JLFP_policy Job)
  (j : Equality.sort Job) (t1 t2 : instant) =>
let is_hep := (@hep_job Job H2)^~ j in @workload_of_jobs Job H1 is_hep (@arrivals_between Job arr_seq t1 t2)
     : forall {Job : JobType},
       JobCost Job ->
       arrival_sequence Job -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> nat

Arguments workload_of_hep_jobs {Job H1} arr_seq {H2} j t1 t2
```

## Lean

```lean
@Prosa.Model.Aggregate.Workload.workload_of_hep_jobs : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
          Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Model.Aggregate.Workload.workload_of_hep_jobs.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
          Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] arr_seq [Prosa.Model.Priority.Definitions.JLFP_policy Job]
    j t1 t2 =>
  have is_hep := fun j' => Prosa.Model.Priority.Definitions.hep_job j' j;
  Prosa.Model.Aggregate.Workload.workload_of_jobs is_hep
    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Aggregate_Workload_workload_of_hep_jobs
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Model_Aggregate_Workload_workload_of_hep_jobs@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                           inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (inst_11 : Prosa_Model_Priority_Definitions_JLFP_policy
                                                                            Job
                                                                            inst_3)
  (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
let is_hep :=
  fun j' : Job =>
  Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
    inst_3
    inst_11 j' j
  in
Prosa_Model_Aggregate_Workload_workload_of_jobs Job
  inst_3
  inst_6 is_hep
  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
     inst_3 arr_seq t1 t2)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Model_Aggregate_Workload_workload_of_hep_jobs Job
  inst_3
  inst_6 arr_seq
  inst_11 j t1 t2
```
