# `job_run_to_completion_threshold_le_job_cost`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_run_to_completion_threshold_le_job_cost`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_run_to_completion_threshold_le_job_cost`
- Certificate: `job_run_to_completion_threshold_le_job_cost_correspondence`

## Official Rocq

```coq
job_run_to_completion_threshold_le_job_cost :
forall {Job : JobType} {H0 : JobCost Job} {H1 : JobPreemptable Job} (j : Equality.sort Job),
is_true (@job_rtct Job H0 H1 j <= @job_cost Job H0 j)

job_run_to_completion_threshold_le_job_cost is not universe polymorphic
Arguments job_run_to_completion_threshold_le_job_cost {Job H0 H1} j
job_run_to_completion_threshold_le_job_cost is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_run_to_completion_threshold_le_job_cost
Declared in library prosa.analysis.facts.preemption.rtc_threshold.job_preemptable, line 203, characters 8-51
@job_run_to_completion_threshold_le_job_cost
     : forall (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptable Job) (j : Equality.sort Job),
       is_true (@job_rtct Job H0 H1 j <= @job_cost Job H0 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_run_to_completion_threshold_le_job_cost : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] (j : Job),
  Prosa.Model.Preemption.Parameter.job_rtct j ≤ Prosa.Behavior.Job.job_cost j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_run_to_completion_threshold_le_job_cost
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (j : Job),
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Preemption_Parameter_job_rtct Job
            inst_3
            inst_6
            inst_9
            j)
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6
            j)
```
