# `no_changes_implies_same_scheduled_job`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule_change.no_changes_implies_same_scheduled_job`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.no_changes_implies_same_scheduled_job`
- Certificate: `no_changes_implies_same_scheduled_job_correspondence`

## Official Rocq

```coq
no_changes_implies_same_scheduled_job :
forall {Job : JobType} (sched : @schedule Job (processor_state Job)) (t1 t2 t t' : instant)
  (oj : option (Equality.sort Job)),
is_true (@no_schedule_changes_during Job sched t1 t2) ->
is_true (t1 <= t < t2) ->
is_true (t1 <= t' < t2) -> @scheduled_job Job sched t = oj -> @scheduled_job Job sched t' = oj

no_changes_implies_same_scheduled_job is not universe polymorphic
Arguments no_changes_implies_same_scheduled_job {Job} sched t1 t2 t t' oj _ _ _ _
no_changes_implies_same_scheduled_job is opaque
Expands to: Constant
            prosa.analysis.facts.model.overheads.schedule_change.no_changes_implies_same_scheduled_job
Declared in library prosa.analysis.facts.model.overheads.schedule_change, line 140, characters 8-45
@no_changes_implies_same_scheduled_job
     : forall (Job : JobType) (sched : @schedule Job (processor_state Job)) (t1 t2 t t' : instant)
         (oj : option (Equality.sort Job)),
       is_true (@no_schedule_changes_during Job sched t1 t2) ->
       is_true (t1 <= t < t2) ->
       is_true (t1 <= t' < t2) -> @scheduled_job Job sched t = oj -> @scheduled_job Job sched t' = oj
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.no_changes_implies_same_scheduled_job : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job))
  (t1 t2 t t' : Prosa.Behavior.Time.instant) (oj : Option Job),
  Prosa.Analysis.Definitions.Overheads.ScheduleChange.no_schedule_changes_during sched t1 t2 = true →
    (decide (t1 ≤ t) && decide (t < t2)) = true →
      (decide (t1 ≤ t') && decide (t' < t2)) = true →
        Prosa.Model.Processor.Overheads.scheduled_job sched t = oj →
          Prosa.Model.Processor.Overheads.scheduled_job sched t' = oj
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_ScheduleChange_no_changes_implies_same_scheduled_job
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Overheads_processor_state Job
                       inst_3))
         (t1 t2 t t' : Prosa_Behavior_Time_instant) (oj : Option Job),
       @eq Bool
         (Prosa_Analysis_Definitions_Overheads_ScheduleChange_no_schedule_changes_during Job
            inst_3 sched t1
            t2)
         Bool_true ->
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t') (Nat_decLe t1 t'))
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t' t2) (Nat_decLt t' t2)))
         Bool_true ->
       @eq (Option Job)
         (Prosa_Model_Processor_Overheads_scheduled_job Job
            inst_3 sched t)
         oj ->
       @eq (Option Job)
         (Prosa_Model_Processor_Overheads_scheduled_job Job
            inst_3 sched t')
         oj
```
