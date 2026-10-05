# `edf_prefix_scheduled_job_has_later_deadline`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.transform.edf_opt.edf_prefix_scheduled_job_has_later_deadline`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_scheduled_job_has_later_deadline`
- Certificate: `edf_prefix_scheduled_job_has_later_deadline_correspondence`

## Official Rocq

```coq
edf_prefix_scheduled_job_has_later_deadline :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (sched : @schedule Job (ideal.processor_state Job)),
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
@all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
forall (horizon : instant) (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job (ideal.processor_state Job) (@edf_transform_prefix Job H0 H1 sched horizon) j t) ->
is_true (t < @job_deadline Job H0 j)

edf_prefix_scheduled_job_has_later_deadline is not universe polymorphic
Arguments edf_prefix_scheduled_job_has_later_deadline {Job H H0 H1} sched H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_no_deadline_misses horizon j t _
edf_prefix_scheduled_job_has_later_deadline is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.edf_prefix_scheduled_job_has_later_deadline
Declared in library prosa.analysis.facts.transform.edf_opt, line 565, characters 12-55
@edf_prefix_scheduled_job_has_later_deadline
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (sched : @schedule Job (ideal.processor_state Job)),
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
       @all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
       forall (horizon : instant) (j : Equality.sort Job) (t : instant),
       is_true
         (@scheduled_at Job (ideal.processor_state Job) (@edf_transform_prefix Job H0 H1 sched horizon) j t) ->
       is_true (t < @job_deadline Job H0 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_scheduled_job_has_later_deadline : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobDeadline Job] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
      Prosa.Analysis.Definitions.Schedulability.all_deadlines_met sched →
        ∀ (horizon : Prosa.Behavior.Time.instant) (j : Job) (t : Prosa.Behavior.Time.instant),
          Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.EdfTrans.edf_transform_prefix sched horizon) j
                t =
              true →
            t < Prosa.Behavior.Job.job_deadline j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_edf_prefix_scheduled_job_has_later_deadline
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
       forall (horizon : Prosa_Behavior_Time_instant) (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix Job
               inst_3
               inst_9
               inst_12 sched horizon)
            j t)
         Bool_true ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t
         (Prosa_Behavior_Job_JobDeadline_job_deadline Job
            inst_3
            inst_9 j)
```
