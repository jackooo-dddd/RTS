# `other_hep_jobs_interfering_workload`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.interference.other_hep_jobs_interfering_workload`
- Lean: `Prosa.Analysis.Definitions.Interference.other_hep_jobs_interfering_workload`
- Certificate: `other_hep_jobs_interfering_workload_correspondence`

## Official Rocq

```coq
other_hep_jobs_interfering_workload :
forall {Job : JobType},
JobCost Job -> arrival_sequence Job -> JLFP_policy Job -> Equality.sort Job -> instant -> nat

other_hep_jobs_interfering_workload is not universe polymorphic
Arguments other_hep_jobs_interfering_workload {Job jc} arr_seq {JLFP} j t
other_hep_jobs_interfering_workload is transparent
Expands to: Constant prosa.analysis.definitions.interference.other_hep_jobs_interfering_workload
Declared in library prosa.analysis.definitions.interference, line 108, characters 15-50
@other_hep_jobs_interfering_workload
     : forall Job : JobType,
       JobCost Job -> arrival_sequence Job -> JLFP_policy Job -> Equality.sort Job -> instant -> nat
```

Body:

```coq
other_hep_jobs_interfering_workload =
fun (Job : JobType) (jc : JobCost Job) (arr_seq : arrival_sequence Job) (JLFP : JLFP_policy Job)
  (j : Equality.sort Job) (t : instant) =>
\sum_(jhp <- @arrivals_at Job arr_seq t | @another_hep_job Job JLFP jhp j) @job_cost Job jc jhp
     : forall {Job : JobType},
       JobCost Job -> arrival_sequence Job -> JLFP_policy Job -> Equality.sort Job -> instant -> nat

Arguments other_hep_jobs_interfering_workload {Job jc} arr_seq {JLFP} j t
```

## Lean

```lean
@Prosa.Analysis.Definitions.Interference.other_hep_jobs_interfering_workload : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.Interference.other_hep_jobs_interfering_workload.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] arr_seq [Prosa.Model.Priority.Definitions.JLFP_policy Job]
    j t =>
  Prosa.Util.Sum.sumFiltered (Prosa.Behavior.Arrival_sequence.arrivals_at arr_seq t)
    (fun jhp => Prosa.Model.Priority.Definitions.another_hep_job jhp j) fun jhp => Prosa.Behavior.Job.job_cost jhp
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Interference_other_hep_jobs_interfering_workload
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_Interference_other_hep_jobs_interfering_workload@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobCost Job inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (inst_11 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Prosa_Util_Sum_sumFiltered Job
  (Prosa_Behavior_Arrival_sequence_arrivals_at Job
     inst_3 arr_seq t)
  (fun jhp : Job =>
   Prosa_Model_Priority_Definitions_another_hep_job Job
     inst_3
     inst_11 jhp j)
  (fun jhp : Job =>
   Prosa_Behavior_Job_JobCost_job_cost Job
     inst_3
     inst_6 jhp)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Definitions_Interference_other_hep_jobs_interfering_workload 
  Job inst_3
  inst_6 arr_seq
  inst_11 j 
  t2
```
