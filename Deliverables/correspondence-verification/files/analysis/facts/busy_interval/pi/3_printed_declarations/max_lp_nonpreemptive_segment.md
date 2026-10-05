# `max_lp_nonpreemptive_segment`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.busy_interval.pi.max_lp_nonpreemptive_segment`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Pi.max_lp_nonpreemptive_segment`
- Certificate: `max_lp_nonpreemptive_segment_correspondence`

## Official Rocq

```coq
max_lp_nonpreemptive_segment :
forall {Job : JobType},
JobCost Job ->
arrival_sequence Job -> JLFP_policy Job -> JobPreemptable Job -> Equality.sort Job -> instant -> nat

max_lp_nonpreemptive_segment is not universe polymorphic
Arguments max_lp_nonpreemptive_segment {Job H2} arr_seq {JLFP H4} j t
max_lp_nonpreemptive_segment is transparent
Expands to: Constant prosa.analysis.facts.busy_interval.pi.max_lp_nonpreemptive_segment
Declared in library prosa.analysis.facts.busy_interval.pi, line 321, characters 13-41
@max_lp_nonpreemptive_segment
     : forall Job : JobType,
       JobCost Job ->
       arrival_sequence Job -> JLFP_policy Job -> JobPreemptable Job -> Equality.sort Job -> instant -> nat
```

Body:

```coq
max_lp_nonpreemptive_segment =
fun (Job : JobType) (H2 : JobCost Job) (arr_seq : arrival_sequence Job) (JLFP : JLFP_policy Job)
  (H4 : JobPreemptable Job) (j : Equality.sort Job) (t : instant) =>
\max_(j_lp <- @arrivals_before Job arr_seq t | ~~ @hep_job Job JLFP j_lp j && (0 < @job_cost Job H2 j_lp))
   (@job_max_nonpreemptive_segment Job H2 H4 j_lp - 1)
     : forall {Job : JobType},
       JobCost Job ->
       arrival_sequence Job -> JLFP_policy Job -> JobPreemptable Job -> Equality.sort Job -> instant -> nat

Arguments max_lp_nonpreemptive_segment {Job H2} arr_seq {JLFP H4} j t
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Pi.max_lp_nonpreemptive_segment : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
          [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Analysis.Facts.BusyInterval.Pi.max_lp_nonpreemptive_segment.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
          [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] arr_seq [Prosa.Model.Priority.Definitions.JLFP_policy Job]
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] j t =>
  Prosa.Util.Minmax.bigMaxListCond (Prosa.Behavior.Arrival_sequence.arrivals_before arr_seq t)
    (fun j_lp => !Prosa.Model.Priority.Definitions.hep_job j_lp j && decide (Prosa.Behavior.Job.job_cost j_lp > 0))
    fun j_lp => Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment j_lp - 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (inst_11 : Prosa_Model_Priority_Definitions_JLFP_policy
                                                                                Job
                                                                                inst_3)
  (inst_14 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                                Job
                                                                                inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Prosa_Util_Minmax_bigMaxListCond Job
  (Prosa_Behavior_Arrival_sequence_arrivals_before Job
     inst_3 arr_seq t)
  (fun j_lp : Job =>
   Bool_and
     (Bool_not
        (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
           inst_3
           inst_11 j_lp j))
     (Decidable_decide
        (GT_gt_inst1 Prosa_Behavior_Job_work instLTNat
           (Prosa_Behavior_Job_JobCost_job_cost Job
              inst_3
              inst_6 j_lp)
           (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)))
        (Nat_decLt (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
           (Prosa_Behavior_Job_JobCost_job_cost Job
              inst_3
              inst_6 j_lp))))
  (fun j_lp : Job =>
   HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
     (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
        inst_3
        inst_6
        inst_14 j_lp)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment Job
  inst_3
  inst_6 arr_seq
  inst_11
  inst_14 j t2
```
