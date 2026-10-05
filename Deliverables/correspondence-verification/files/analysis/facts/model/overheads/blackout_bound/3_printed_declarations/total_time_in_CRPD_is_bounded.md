# `total_time_in_CRPD_is_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_CRPD_is_bounded`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.total_time_in_CRPD_is_bounded`
- Certificate: `total_time_in_CRPD_is_bounded_correspondence`

## Official Rocq

```coq
total_time_in_CRPD_is_bounded :
forall {Job : JobType} (sched : @schedule Job (processor_state Job)) (DB CSB CRPDB : duration),
@overhead_resource_model Job sched DB CSB CRPDB ->
forall t1 t2 : instant,
is_true (@no_schedule_changes_during Job sched t1 t2) ->
is_true (@total_time_in_CRPD Job sched t1 t2 <= CRPDB)

total_time_in_CRPD_is_bounded is not universe polymorphic
Arguments total_time_in_CRPD_is_bounded {Job} sched DB CSB CRPDB H_valid_overheads_model t1 t2 _
total_time_in_CRPD_is_bounded is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_CRPD_is_bounded
Declared in library prosa.analysis.facts.model.overheads.blackout_bound, line 164, characters 8-37
@total_time_in_CRPD_is_bounded
     : forall (Job : JobType) (sched : @schedule Job (processor_state Job)) (DB CSB CRPDB : duration),
       @overhead_resource_model Job sched DB CSB CRPDB ->
       forall t1 t2 : instant,
       is_true (@no_schedule_changes_during Job sched t1 t2) ->
       is_true (@total_time_in_CRPD Job sched t1 t2 <= CRPDB)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.total_time_in_CRPD_is_bounded : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job))
  (DB CSB CRPDB : Prosa.Behavior.Time.duration),
  Prosa.Model.Processor.OverheadResourceModel.overhead_resource_model sched DB CSB CRPDB →
    ∀ (t1 t2 : Prosa.Behavior.Time.instant),
      Prosa.Analysis.Definitions.Overheads.ScheduleChange.no_schedule_changes_during sched t1 t2 = true →
        Prosa.Model.Processor.Overheads.total_time_in_CRPD sched t1 t2 ≤ CRPDB
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_total_time_in_CRPD_is_bounded
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Overheads_processor_state Job
                       inst_3))
         (DB CSB CRPDB : Prosa_Behavior_Time_duration),
       Prosa_Model_Processor_OverheadResourceModel_overhead_resource_model Job
         inst_3 sched DB CSB
         CRPDB ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Analysis_Definitions_Overheads_ScheduleChange_no_schedule_changes_during Job
            inst_3 sched t1
            t2)
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Processor_Overheads_total_time_in_CRPD Job
            inst_3 sched t1
            t2)
         CRPDB
```
