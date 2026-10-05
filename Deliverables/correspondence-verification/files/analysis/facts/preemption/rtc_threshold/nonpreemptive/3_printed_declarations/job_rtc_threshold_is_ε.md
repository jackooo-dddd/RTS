# `job_rtc_threshold_is_ε`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_ε`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive.job_rtc_threshold_is_ε`
- Certificate: `job_rtc_threshold_is_ε_correspondence`

## Official Rocq

```coq
job_rtc_threshold_is_ε :
forall {Job : JobType} {H2 : JobCost Job} (arr_seq : arrival_sequence Job) (j : Equality.sort Job),
is_true (0 < @job_cost Job H2 j) ->
@arrives_in Job arr_seq j -> @job_rtct Job H2 (@fully_nonpreemptive_job_model Job H2) j = 1

job_rtc_threshold_is_ε is not universe polymorphic
Arguments job_rtc_threshold_is_ε {Job H2} arr_seq j _ _
job_rtc_threshold_is_ε is opaque
Expands to: Constant prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_ε
Declared in library prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive, line 51, characters 7-30
@job_rtc_threshold_is_ε
     : forall (Job : JobType) (H2 : JobCost Job) (arr_seq : arrival_sequence Job) (j : Equality.sort Job),
       is_true (0 < @job_cost Job H2 j) ->
       @arrives_in Job arr_seq j -> @job_rtct Job H2 (@fully_nonpreemptive_job_model Job H2) j = 1
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive.job_rtc_threshold_is_ε : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (j : Job),
  0 < Prosa.Behavior.Job.job_cost j →
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j → Prosa.Model.Preemption.Parameter.job_rtct j = 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_Nonpreemptive_job_rtc_threshold_is__UU03b5_
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (j : Job),
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6 j) ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3
         arr_seq j ->
       @eq Nat
         (Prosa_Model_Preemption_Parameter_job_rtct Job
            inst_3
            inst_6
            (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job
               inst_3
               inst_6)
            j)
         (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
```
