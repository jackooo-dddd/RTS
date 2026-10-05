# `number_schedule_changes_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_cat`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.number_schedule_changes_cat`
- Certificate: `number_schedule_changes_cat_correspondence`

## Official Rocq

```coq
number_schedule_changes_cat :
forall {Job : JobType} (sched : @schedule Job (processor_state Job)) (t t1 t2 : instant),
is_true (t1 <= t <= t2) ->
@number_schedule_changes Job sched t1 t2 =
@number_schedule_changes Job sched t1 t + @number_schedule_changes Job sched t t2

number_schedule_changes_cat is not universe polymorphic
Arguments number_schedule_changes_cat {Job} sched t t1 t2 _
number_schedule_changes_cat is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_cat
Declared in library prosa.analysis.facts.model.overheads.schedule_change, line 17, characters 8-35
@number_schedule_changes_cat
     : forall (Job : JobType) (sched : @schedule Job (processor_state Job)) (t t1 t2 : instant),
       is_true (t1 <= t <= t2) ->
       @number_schedule_changes Job sched t1 t2 =
       @number_schedule_changes Job sched t1 t + @number_schedule_changes Job sched t t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.number_schedule_changes_cat : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job))
  (t t1 t2 : Prosa.Behavior.Time.instant),
  (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
    Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes sched t1 t2 =
      Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes sched t1 t +
        Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes sched t t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_ScheduleChange_number_schedule_changes_cat
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Overheads_processor_state Job
                       inst_3))
         (t t1 t2 : Prosa_Behavior_Time_instant),
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t t2) (Nat_decLe t t2)))
         Bool_true ->
       @eq Nat
         (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
            inst_3 sched t1
            t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
               inst_3 sched
               t1 t)
            (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
               inst_3 sched
               t t2))
```
