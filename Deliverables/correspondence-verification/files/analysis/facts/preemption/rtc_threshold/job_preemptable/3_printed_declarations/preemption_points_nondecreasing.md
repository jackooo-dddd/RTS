# `preemption_points_nondecreasing`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.preemption_points_nondecreasing`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.preemption_points_nondecreasing`
- Certificate: `preemption_points_nondecreasing_correspondence`

## Official Rocq

```coq
preemption_points_nondecreasing :
forall {Job : JobType} {H0 : JobCost Job} {H1 : JobPreemptable Job} (j : Equality.sort Job),
nondecreasing_sequence (@job_preemption_points Job H0 H1 j)

preemption_points_nondecreasing is not universe polymorphic
Arguments preemption_points_nondecreasing {Job H0 H1} j n1 n2 _
preemption_points_nondecreasing is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.preemption_points_nondecreasing
Declared in library prosa.analysis.facts.preemption.rtc_threshold.job_preemptable, line 98, characters 8-39
@preemption_points_nondecreasing
     : forall (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptable Job) (j : Equality.sort Job),
       nondecreasing_sequence (@job_preemption_points Job H0 H1 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.preemption_points_nondecreasing : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] (j : Job),
  Prosa.Util.Nondecreasing.nondecreasing_sequence (Prosa.Model.Preemption.Parameter.job_preemption_points j)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_preemption_points_nondecreasing
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
       Prosa_Util_Nondecreasing_nondecreasing_sequence
         (Prosa_Model_Preemption_Parameter_job_preemption_points Job
            inst_3
            inst_6
            inst_9
            j)
```
