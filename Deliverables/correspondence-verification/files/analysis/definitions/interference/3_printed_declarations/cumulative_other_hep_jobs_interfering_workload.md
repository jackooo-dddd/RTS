# `cumulative_other_hep_jobs_interfering_workload`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.interference.cumulative_other_hep_jobs_interfering_workload`
- Lean: `Prosa.Analysis.Definitions.Interference.cumulative_other_hep_jobs_interfering_workload`
- Certificate: `cumulative_other_hep_jobs_interfering_workload_correspondence`

## Official Rocq

```coq
cumulative_other_hep_jobs_interfering_workload :
forall {Job : JobType},
JobCost Job -> arrival_sequence Job -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> nat

cumulative_other_hep_jobs_interfering_workload is not universe polymorphic
Arguments cumulative_other_hep_jobs_interfering_workload {Job jc} arr_seq {JLFP} j t1 t2
cumulative_other_hep_jobs_interfering_workload is transparent
Expands to: Constant prosa.analysis.definitions.interference.cumulative_other_hep_jobs_interfering_workload
Declared in library prosa.analysis.definitions.interference, line 124, characters 15-61
@cumulative_other_hep_jobs_interfering_workload
     : forall Job : JobType,
       JobCost Job ->
       arrival_sequence Job -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> nat
```

Body:

```coq
cumulative_other_hep_jobs_interfering_workload =
fun (Job : JobType) (jc : JobCost Job) (arr_seq : arrival_sequence Job) (JLFP : JLFP_policy Job)
  (j : Equality.sort Job) (t1 t2 : instant) =>
\sum_(t1 <= t < t2) @other_hep_jobs_interfering_workload Job jc arr_seq JLFP j t
     : forall {Job : JobType},
       JobCost Job ->
       arrival_sequence Job -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> nat

Arguments cumulative_other_hep_jobs_interfering_workload {Job jc} arr_seq {JLFP} j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Definitions.Interference.cumulative_other_hep_jobs_interfering_workload : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
          Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.Interference.cumulative_other_hep_jobs_interfering_workload.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
          Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] arr_seq [Prosa.Model.Priority.Definitions.JLFP_policy Job]
    j t1 t2 =>
  Prosa.Util.Sum.sumSeq (List.range' t1 (t2 - t1)) fun t =>
    Prosa.Analysis.Definitions.Interference.other_hep_jobs_interfering_workload arr_seq j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Interference_cumulative_other_hep_jobs_interfering_workload
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_Interference_cumulative_other_hep_jobs_interfering_workload@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobCost Job
     inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (inst_11 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_3)
  (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
Prosa_Util_Sum_sumSeq_inst1 Nat
  (List_range' t1
     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
  (fun t : Nat =>
   Prosa_Analysis_Definitions_Interference_other_hep_jobs_interfering_workload Job
     inst_3
     inst_6 arr_seq
     inst_11 j t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Definitions_Interference_cumulative_other_hep_jobs_interfering_workload 
  Job inst_3
  inst_6 arr_seq
  inst_11 j 
  t1 t2
```
