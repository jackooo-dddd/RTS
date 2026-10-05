# `no_schedule_changes_implies_constant_schedule`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule_change.no_schedule_changes_implies_constant_schedule`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.no_schedule_changes_implies_constant_schedule`
- Certificate: `no_schedule_changes_implies_constant_schedule_correspondence`

## Official Rocq

```coq
no_schedule_changes_implies_constant_schedule :
forall {Job : JobType} (sched : @schedule Job (processor_state Job)) (t1 t2 t : instant),
is_true (t1 <= t < t2) ->
@number_schedule_changes Job sched t1 t2 = 0 -> is_true (~~ @schedule_change Job sched t)

no_schedule_changes_implies_constant_schedule is not universe polymorphic
Arguments no_schedule_changes_implies_constant_schedule {Job} sched t1 t2 t _ _
no_schedule_changes_implies_constant_schedule is opaque
Expands to: Constant
            prosa.analysis.facts.model.overheads.schedule_change.no_schedule_changes_implies_constant_schedule
Declared in library prosa.analysis.facts.model.overheads.schedule_change, line 122, characters 8-53
@no_schedule_changes_implies_constant_schedule
     : forall (Job : JobType) (sched : @schedule Job (processor_state Job)) (t1 t2 t : instant),
       is_true (t1 <= t < t2) ->
       @number_schedule_changes Job sched t1 t2 = 0 -> is_true (~~ @schedule_change Job sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.no_schedule_changes_implies_constant_schedule : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job))
  (t1 t2 t : Prosa.Behavior.Time.instant),
  (decide (t1 ≤ t) && decide (t < t2)) = true →
    Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes sched t1 t2 = 0 →
      (!Prosa.Analysis.Definitions.Overheads.ScheduleChange.schedule_change sched t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_ScheduleChange_no_schedule_changes_implies_constant_schedule
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Overheads_processor_state Job
                       inst_3))
         (t1 t2 t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       @eq Nat
         (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
            inst_3 sched t1
            t2)
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_Overheads_ScheduleChange_schedule_change Job
               inst_3 sched
               t))
         Bool_true
```
