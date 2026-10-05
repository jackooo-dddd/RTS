# `valid_fixed_preemption_points_model_lemma`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.job.limited.valid_fixed_preemption_points_model_lemma`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Limited.valid_fixed_preemption_points_model_lemma`
- Certificate: `valid_fixed_preemption_points_model_lemma_correspondence`

## Official Rocq

```coq
valid_fixed_preemption_points_model_lemma :
forall {Job : JobType} {H2 : JobCost Job} {H3 : JobPreemptionPoints Job} (arr_seq : arrival_sequence Job)
  {PState : ProcessorState Job} (sched : @schedule Job PState),
@schedule_respects_preemption_model Job PState (@limited_preemptive_job_model Job H3) arr_seq sched ->
@valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
@valid_preemption_model Job H2 (@limited_preemptive_job_model Job H3) PState arr_seq sched

valid_fixed_preemption_points_model_lemma is not universe polymorphic
Arguments valid_fixed_preemption_points_model_lemma {Job H2 H3} arr_seq {PState} 
  sched H_schedule_respects_preemption_model H_valid_limited_preemptions_job_model 
  j _
valid_fixed_preemption_points_model_lemma is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.limited.valid_fixed_preemption_points_model_lemma
Declared in library prosa.analysis.facts.preemption.job.limited, line 200, characters 8-49
@valid_fixed_preemption_points_model_lemma
     : forall (Job : JobType) (H2 : JobCost Job) (H3 : JobPreemptionPoints Job)
         (arr_seq : arrival_sequence Job) (PState : ProcessorState Job) (sched : @schedule Job PState),
       @schedule_respects_preemption_model Job PState (@limited_preemptive_job_model Job H3) arr_seq sched ->
       @valid_limited_preemptions_job_model Job H2 H3 arr_seq ->
       @valid_preemption_model Job H2 (@limited_preemptive_job_model Job H3) PState arr_seq sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Limited.valid_fixed_preemption_points_model_lemma : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model arr_seq sched →
    Prosa.Model.Preemption.LimitedPreemptive.valid_limited_preemptions_job_model arr_seq →
      Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Limited_valid_fixed_preemption_points_model_lemma
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model Job
         inst_3 PState
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_3
            inst_9)
         arr_seq sched ->
       Prosa_Model_Preemption_LimitedPreemptive_valid_limited_preemptions_job_model Job
         inst_3
         inst_6
         inst_9 arr_seq ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_6
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_3
            inst_9)
         PState arr_seq sched
```
