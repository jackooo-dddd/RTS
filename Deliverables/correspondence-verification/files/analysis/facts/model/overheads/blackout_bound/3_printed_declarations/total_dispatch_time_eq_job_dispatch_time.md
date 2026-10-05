# `total_dispatch_time_eq_job_dispatch_time`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.blackout_bound.total_dispatch_time_eq_job_dispatch_time`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.total_dispatch_time_eq_job_dispatch_time`
- Certificate: `total_dispatch_time_eq_job_dispatch_time_correspondence`

## Official Rocq

```coq
total_dispatch_time_eq_job_dispatch_time :
forall {Job : JobType} (sched : @schedule Job (processor_state Job)) (t1 t2 : instant),
is_true (@no_schedule_changes_during Job sched t1 t2) ->
exists oj : option (Equality.sort Job),
  @total_time_in_dispatch Job sched t1 t2 = @time_spent_in_dispatch Job sched oj t1 t2

total_dispatch_time_eq_job_dispatch_time is not universe polymorphic
Arguments total_dispatch_time_eq_job_dispatch_time {Job} sched t1 t2 _
total_dispatch_time_eq_job_dispatch_time is opaque
Expands to: Constant
            prosa.analysis.facts.model.overheads.blackout_bound.total_dispatch_time_eq_job_dispatch_time
Declared in library prosa.analysis.facts.model.overheads.blackout_bound, line 60, characters 8-48
@total_dispatch_time_eq_job_dispatch_time
     : forall (Job : JobType) (sched : @schedule Job (processor_state Job)) (t1 t2 : instant),
       is_true (@no_schedule_changes_during Job sched t1 t2) ->
       exists oj : option (Equality.sort Job),
         @total_time_in_dispatch Job sched t1 t2 = @time_spent_in_dispatch Job sched oj t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.total_dispatch_time_eq_job_dispatch_time : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job))
  (t1 t2 : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Definitions.Overheads.ScheduleChange.no_schedule_changes_during sched t1 t2 = true →
    ∃ oj,
      Prosa.Model.Processor.Overheads.total_time_in_dispatch sched t1 t2 =
        Prosa.Model.Processor.OverheadResourceModel.time_spent_in_dispatch sched oj t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_total_dispatch_time_eq_job_dispatch_time
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Overheads_processor_state Job
                       inst_3))
         (t1 t2 : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Analysis_Definitions_Overheads_ScheduleChange_no_schedule_changes_during Job
            inst_3 sched t1
            t2)
         Bool_true ->
       Exists (Option Job)
         (fun oj : Option Job =>
          Prosa_Model_Processor_Overheads_total_time_in_dispatch Job
            inst_3 sched t1
            t2 =
          Prosa_Model_Processor_OverheadResourceModel_time_spent_in_dispatch Job
            inst_3 sched oj
            t1 t2)
```
