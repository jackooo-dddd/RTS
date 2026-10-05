# `max_deadline_for_jobs_arrived_before`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.wc_trans.max_deadline_for_jobs_arrived_before`
- Lean: `Prosa.Analysis.Transform.WcTrans.max_deadline_for_jobs_arrived_before`
- Certificate: `max_deadline_for_jobs_arrived_before_correspondence`

## Official Rocq

```coq
max_deadline_for_jobs_arrived_before :
forall {Job : JobType}, JobDeadline Job -> arrival_sequence Job -> instant -> nat

max_deadline_for_jobs_arrived_before is not universe polymorphic
Arguments max_deadline_for_jobs_arrived_before {Job H1} arr_seq arrived_before
max_deadline_for_jobs_arrived_before is transparent
Expands to: Constant prosa.analysis.transform.wc_trans.max_deadline_for_jobs_arrived_before
Declared in library prosa.analysis.transform.wc_trans, line 42, characters 13-49
@max_deadline_for_jobs_arrived_before
     : forall Job : JobType, JobDeadline Job -> arrival_sequence Job -> instant -> nat
```

Body:

```coq
max_deadline_for_jobs_arrived_before =
fun (Job : JobType) (H1 : JobDeadline Job) (arr_seq : arrival_sequence Job) (arrived_before : instant) =>
let deadlines := [seq @job_deadline Job H1 i | i <- @arrivals_up_to Job arr_seq arrived_before] in
max0 deadlines
     : forall {Job : JobType}, JobDeadline Job -> arrival_sequence Job -> instant -> nat

Arguments max_deadline_for_jobs_arrived_before {Job H1} arr_seq arrived_before
```

## Lean

```lean
@Prosa.Analysis.Transform.WcTrans.max_deadline_for_jobs_arrived_before : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Analysis.Transform.WcTrans.max_deadline_for_jobs_arrived_before.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobDeadline Job] arr_seq arrived_before =>
  have deadlines :=
    List.map Prosa.Behavior.Job.job_deadline (Prosa.Behavior.Arrival_sequence.arrivals_up_to arr_seq arrived_before);
  Prosa.Util.List.max0 deadlines
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_WcTrans_max_deadline_for_jobs_arrived_before
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Transform_WcTrans_max_deadline_for_jobs_arrived_before@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobDeadline Job
                                                                             inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (arrived_before : Prosa_Behavior_Time_instant) =>
let deadlines :=
  List_map_inst2 Job Prosa_Behavior_Time_instant
    (Prosa_Behavior_Job_JobDeadline_job_deadline Job
       inst_3
       inst_6)
    (Prosa_Behavior_Arrival_sequence_arrivals_up_to Job
       inst_3 arr_seq arrived_before)
  in
Prosa_Util_List_max0 deadlines
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Transform_WcTrans_max_deadline_for_jobs_arrived_before Job
  inst_3
  inst_6 arr_seq arrived_before
```
