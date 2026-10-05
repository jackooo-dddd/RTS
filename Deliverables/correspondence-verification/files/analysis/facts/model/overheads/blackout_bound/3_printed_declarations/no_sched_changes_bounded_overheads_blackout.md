# `no_sched_changes_bounded_overheads_blackout`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.blackout_bound.no_sched_changes_bounded_overheads_blackout`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.no_sched_changes_bounded_overheads_blackout`
- Certificate: `no_sched_changes_bounded_overheads_blackout_correspondence`

## Official Rocq

```coq
no_sched_changes_bounded_overheads_blackout :
forall {Job : JobType} (sched : @schedule Job (processor_state Job)) (DB CSB CRPDB : duration),
@overhead_resource_model Job sched DB CSB CRPDB ->
forall t1 t2 : instant,
is_true (@no_schedule_changes_during Job sched t1 t2) ->
is_true (@blackout_during Job (processor_state Job) sched t1 t2 <= DB + CSB + CRPDB)

no_sched_changes_bounded_overheads_blackout is not universe polymorphic
Arguments no_sched_changes_bounded_overheads_blackout {Job} sched DB CSB CRPDB H_valid_overheads_model 
  t1 t2 _
no_sched_changes_bounded_overheads_blackout is opaque
Expands to: Constant
            prosa.analysis.facts.model.overheads.blackout_bound.no_sched_changes_bounded_overheads_blackout
Declared in library prosa.analysis.facts.model.overheads.blackout_bound, line 191, characters 8-51
@no_sched_changes_bounded_overheads_blackout
     : forall (Job : JobType) (sched : @schedule Job (processor_state Job)) (DB CSB CRPDB : duration),
       @overhead_resource_model Job sched DB CSB CRPDB ->
       forall t1 t2 : instant,
       is_true (@no_schedule_changes_during Job sched t1 t2) ->
       is_true (@blackout_during Job (processor_state Job) sched t1 t2 <= DB + CSB + CRPDB)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.no_sched_changes_bounded_overheads_blackout : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job))
  (DB CSB CRPDB : Prosa.Behavior.Time.duration),
  Prosa.Model.Processor.OverheadResourceModel.overhead_resource_model sched DB CSB CRPDB →
    ∀ (t1 t2 : Prosa.Behavior.Time.instant),
      Prosa.Analysis.Definitions.Overheads.ScheduleChange.no_schedule_changes_during sched t1 t2 = true →
        Prosa.Model.Processor.Supply.blackout_during sched t1 t2 ≤ DB + CSB + CRPDB
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_no_sched_changes_bounded_overheads_blackout
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
         (Prosa_Model_Processor_Supply_blackout_during_inst4 Job
            inst_3
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_3)
            sched t1 t2)
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) DB CSB)
            CRPDB)
```
