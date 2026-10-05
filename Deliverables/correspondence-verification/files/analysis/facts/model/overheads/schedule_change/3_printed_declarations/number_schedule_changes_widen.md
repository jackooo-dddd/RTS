# `number_schedule_changes_widen`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_widen`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.number_schedule_changes_widen`
- Certificate: `number_schedule_changes_widen_correspondence`

## Official Rocq

```coq
number_schedule_changes_widen :
forall {Job : JobType} (sched : @schedule Job (processor_state Job)) (t1 t2 t1' t2' : instant),
is_true (t1 <= t1') ->
is_true (t2' <= t2) ->
is_true (@number_schedule_changes Job sched t1' t2' <= @number_schedule_changes Job sched t1 t2)

number_schedule_changes_widen is not universe polymorphic
Arguments number_schedule_changes_widen {Job} sched t1 t2 t1' t2' _ _
number_schedule_changes_widen is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_widen
Declared in library prosa.analysis.facts.model.overheads.schedule_change, line 59, characters 8-37
@number_schedule_changes_widen
     : forall (Job : JobType) (sched : @schedule Job (processor_state Job)) (t1 t2 t1' t2' : instant),
       is_true (t1 <= t1') ->
       is_true (t2' <= t2) ->
       is_true (@number_schedule_changes Job sched t1' t2' <= @number_schedule_changes Job sched t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.number_schedule_changes_widen : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job))
  (t1 t2 t1' t2' : Prosa.Behavior.Time.instant),
  t1 ≤ t1' →
    t2' ≤ t2 →
      Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes sched t1' t2' ≤
        Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes sched t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_ScheduleChange_number_schedule_changes_widen
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Overheads_processor_state Job
                       inst_3))
         (t1 t2 t1' t2' : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t1' ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t2' t2 ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
            inst_3 sched
            t1' t2')
         (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
            inst_3 sched t1
            t2)
```
