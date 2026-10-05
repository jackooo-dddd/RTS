# `mea_guarantee_case_t'_past_deadline`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_opt.mea_guarantee_case_t'_past_deadline`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_case_t'_past_deadline`
- Certificate: `mea_guarantee_case_t'_past_deadline_correspondence`

## Official Rocq

```coq
mea_guarantee_case_t'_past_deadline :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (sched : @schedule Job (ideal.processor_state Job)),
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
@all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
forall (t_edf : instant) (j_orig : Equality.sort Job),
is_true (@scheduled_at Job (ideal.processor_state Job) sched j_orig t_edf) ->
forall j_edf : Equality.sort Job,
is_true (@scheduled_at Job (ideal.processor_state Job) (@make_edf_at Job H0 H1 sched t_edf) j_edf t_edf) ->
forall (j' : Equality.sort Job) (t' : instant),
is_true (@scheduled_at Job (ideal.processor_state Job) (@make_edf_at Job H0 H1 sched t_edf) j' t') ->
is_true (@job_deadline Job H0 j_orig <= t') ->
is_true (@job_deadline Job H0 j_edf <= @job_deadline Job H0 j')

mea_guarantee_case_t'_past_deadline is not universe polymorphic
Arguments mea_guarantee_case_t'_past_deadline {Job H H0 H1} sched H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_no_deadline_misses t_edf j_orig H_sched_orig j_edf 
  H_sched_edf j' t' H_sched' _
mea_guarantee_case_t'_past_deadline is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.mea_guarantee_case_t'_past_deadline
Declared in library prosa.analysis.facts.transform.edf_opt, line 335, characters 10-45
@mea_guarantee_case_t'_past_deadline
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (sched : @schedule Job (ideal.processor_state Job)),
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
       @all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
       forall (t_edf : instant) (j_orig : Equality.sort Job),
       is_true (@scheduled_at Job (ideal.processor_state Job) sched j_orig t_edf) ->
       forall j_edf : Equality.sort Job,
       is_true
         (@scheduled_at Job (ideal.processor_state Job) (@make_edf_at Job H0 H1 sched t_edf) j_edf t_edf) ->
       forall (j' : Equality.sort Job) (t' : instant),
       is_true (@scheduled_at Job (ideal.processor_state Job) (@make_edf_at Job H0 H1 sched t_edf) j' t') ->
       is_true (@job_deadline Job H0 j_orig <= t') ->
       is_true (@job_deadline Job H0 j_edf <= @job_deadline Job H0 j')
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_case_t'_past_deadline : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
      Prosa.Analysis.Definitions.Schedulability.all_deadlines_met sched →
        ∀ (t_edf : Prosa.Behavior.Time.instant) (j_orig : Job),
          Prosa.Behavior.Service.scheduled_at sched j_orig t_edf = true →
            ∀ (j_edf : Job),
              Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.EdfTrans.make_edf_at sched t_edf) j_edf
                    t_edf =
                  true →
                ∀ (j' : Job) (t' : Prosa.Behavior.Time.instant),
                  Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.EdfTrans.make_edf_at sched t_edf) j'
                        t' =
                      true →
                    Prosa.Behavior.Job.job_deadline j_orig ≤ t' →
                      Prosa.Behavior.Job.job_deadline j_edf ≤ Prosa.Behavior.Job.job_deadline j'
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_mea_guarantee_case_t'_past_deadline
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (inst_12 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3)),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_3
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched ->
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
       forall j_edf : Job,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Analysis_Transform_EdfTrans_make_edf_at Job
               inst_3
               inst_9
               inst_12 sched t_edf)
            j_edf t_edf)
         Bool_true ->
       forall (j' : Job) (t' : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Analysis_Transform_EdfTrans_make_edf_at Job
               inst_3
               inst_9
               inst_12 sched t_edf)
            j' t')
         Bool_true ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (Prosa_Behavior_Job_JobDeadline_job_deadline Job
            inst_3
            inst_9 j_orig)
         t' ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (Prosa_Behavior_Job_JobDeadline_job_deadline Job
            inst_3
            inst_9 j_edf)
         (Prosa_Behavior_Job_JobDeadline_job_deadline Job
            inst_3
            inst_9 j')
```
