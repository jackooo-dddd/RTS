# `mea_guarantee_dl_orig`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.transform.edf_opt.mea_guarantee_dl_orig`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_dl_orig`
- Certificate: `mea_guarantee_dl_orig_correspondence`

## Official Rocq

```coq
mea_guarantee_dl_orig :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job}
  (sched : @schedule Job (ideal.processor_state Job)),
@completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
@all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
forall (t_edf : instant) (j_orig : Equality.sort Job),
is_true (@scheduled_at Job (ideal.processor_state Job) sched j_orig t_edf) ->
is_true (t_edf < @job_deadline Job H0 j_orig)

mea_guarantee_dl_orig is not universe polymorphic
Arguments mea_guarantee_dl_orig {Job H H0} sched H_completed_jobs_dont_execute H_no_deadline_misses 
  t_edf j_orig H_sched_orig
mea_guarantee_dl_orig is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.mea_guarantee_dl_orig
Declared in library prosa.analysis.facts.transform.edf_opt, line 303, characters 9-30
@mea_guarantee_dl_orig
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job)
         (sched : @schedule Job (ideal.processor_state Job)),
       @completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
       @all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
       forall (t_edf : instant) (j_orig : Equality.sort Job),
       is_true (@scheduled_at Job (ideal.processor_state Job) sched j_orig t_edf) ->
       is_true (t_edf < @job_deadline Job H0 j_orig)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_dl_orig : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
    Prosa.Analysis.Definitions.Schedulability.all_deadlines_met sched →
      ∀ (t_edf : Prosa.Behavior.Time.instant) (j_orig : Job),
        Prosa.Behavior.Service.scheduled_at sched j_orig t_edf = true → t_edf < Prosa.Behavior.Job.job_deadline j_orig
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_mea_guarantee_dl_orig
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3)),
       Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched inst_6 ->
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_met_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched ->
       forall (t_edf : Prosa_Behavior_Time_instant) (j_orig : Job),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j_orig t_edf)
         Bool_true ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t_edf
         (Prosa_Behavior_Job_JobDeadline_job_deadline Job
            inst_3
            inst_9 j_orig)
```
