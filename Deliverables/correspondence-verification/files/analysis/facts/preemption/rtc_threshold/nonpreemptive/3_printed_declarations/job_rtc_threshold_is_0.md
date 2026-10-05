# `job_rtc_threshold_is_0`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_0`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive.job_rtc_threshold_is_0`
- Certificate: `job_rtc_threshold_is_0_correspondence`

## Official Rocq

```coq
job_rtc_threshold_is_0 :
forall {Job : JobType} {H2 : JobCost Job} (j : Equality.sort Job),
@job_cost Job H2 j = 0 -> @job_rtct Job H2 (@fully_nonpreemptive_job_model Job H2) j = 0

job_rtc_threshold_is_0 is not universe polymorphic
Arguments job_rtc_threshold_is_0 {Job H2} j _
job_rtc_threshold_is_0 is opaque
Expands to: Constant prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_0
Declared in library prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive, line 40, characters 7-29
@job_rtc_threshold_is_0
     : forall (Job : JobType) (H2 : JobCost Job) (j : Equality.sort Job),
       @job_cost Job H2 j = 0 -> @job_rtct Job H2 (@fully_nonpreemptive_job_model Job H2) j = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive.job_rtc_threshold_is_0 : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] (j : Job),
  Prosa.Behavior.Job.job_cost j = 0 → Prosa.Model.Preemption.Parameter.job_rtct j = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_Nonpreemptive_job_rtc_threshold_is_0
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (j : Job),
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6 j)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)) ->
       @eq Nat
         (Prosa_Model_Preemption_Parameter_job_rtct Job
            inst_3
            inst_6
            (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job
               inst_3
               inst_6)
            j)
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
