# `scheduled_job_in_sched_has_later_deadline`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.transform.edf_opt.scheduled_job_in_sched_has_later_deadline`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.scheduled_job_in_sched_has_later_deadline`
- Certificate: `scheduled_job_in_sched_has_later_deadline_correspondence`

## Official Rocq

```coq
scheduled_job_in_sched_has_later_deadline :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job}
  (sched : @schedule Job (ideal.processor_state Job)),
@completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
@all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
forall (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job (ideal.processor_state Job) sched j t) -> is_true (t < @job_deadline Job H0 j)

scheduled_job_in_sched_has_later_deadline is not universe polymorphic
Arguments scheduled_job_in_sched_has_later_deadline {Job H H0} sched H_completed_jobs_dont_execute
  H_no_deadline_misses j t _
scheduled_job_in_sched_has_later_deadline is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.scheduled_job_in_sched_has_later_deadline
Declared in library prosa.analysis.facts.transform.edf_opt, line 192, characters 7-48
@scheduled_job_in_sched_has_later_deadline
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job)
         (sched : @schedule Job (ideal.processor_state Job)),
       @completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
       @all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job (ideal.processor_state Job) sched j t) ->
       is_true (t < @job_deadline Job H0 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.scheduled_job_in_sched_has_later_deadline : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
    Prosa.Analysis.Definitions.Schedulability.all_deadlines_met sched →
      ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
        Prosa.Behavior.Service.scheduled_at sched j t = true → t < Prosa.Behavior.Job.job_deadline j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_scheduled_job_in_sched_has_later_deadline
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
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j t)
         Bool_true ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t
         (Prosa_Behavior_Job_JobDeadline_job_deadline Job
            inst_3
            inst_9 j)
```
