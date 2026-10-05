# `first_schedule_change_exists`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule_change.first_schedule_change_exists`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.first_schedule_change_exists`
- Certificate: `first_schedule_change_exists_correspondence`

## Official Rocq

```coq
first_schedule_change_exists :
forall {Job : JobType} (sched : @schedule Job (processor_state Job)) (t1 t2 : instant) (k : nat),
is_true (0 < k) ->
@number_schedule_changes Job sched t1 t2 = k ->
exists t : nat,
  is_true (t1 <= t < t2) /\
  is_true (@schedule_change Job sched t) /\
  @number_schedule_changes Job sched t1 t = 0 /\ @number_schedule_changes Job sched t t2 = k

first_schedule_change_exists is not universe polymorphic
Arguments first_schedule_change_exists {Job} sched t1 t2 k%nat_scope _ _
first_schedule_change_exists is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.schedule_change.first_schedule_change_exists
Declared in library prosa.analysis.facts.model.overheads.schedule_change, line 30, characters 8-36
@first_schedule_change_exists
     : forall (Job : JobType) (sched : @schedule Job (processor_state Job)) (t1 t2 : instant) (k : nat),
       is_true (0 < k) ->
       @number_schedule_changes Job sched t1 t2 = k ->
       exists t : nat,
         is_true (t1 <= t < t2) /\
         is_true (@schedule_change Job sched t) /\
         @number_schedule_changes Job sched t1 t = 0 /\ @number_schedule_changes Job sched t t2 = k
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.first_schedule_change_exists : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job))
  (t1 t2 : Prosa.Behavior.Time.instant) (k : ℕ),
  0 < k →
    Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes sched t1 t2 = k →
      ∃ t,
        (decide (t1 ≤ t) && decide (t < t2)) = true ∧
          Prosa.Analysis.Definitions.Overheads.ScheduleChange.schedule_change sched t = true ∧
            Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes sched t1 t = 0 ∧
              Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes sched t t2 = k
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_ScheduleChange_first_schedule_change_exists
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Overheads_processor_state Job
                       inst_3))
         (t1 t2 : Prosa_Behavior_Time_instant) (k : Nat),
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) k ->
       @eq Nat
         (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
            inst_3 sched t1
            t2)
         k ->
       Exists Nat
         (fun t : Nat =>
          And
            (@eq Bool
               (Bool_and
                  (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
                  (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
               Bool_true)
            (And
               (@eq Bool
                  (Prosa_Analysis_Definitions_Overheads_ScheduleChange_schedule_change Job
                     inst_3
                     sched t)
                  Bool_true)
               (And
                  (@eq Nat
                     (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
                        inst_3
                        sched t1 t)
                     (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
                  (@eq Nat
                     (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
                        inst_3
                        sched t t2)
                     k))))
```
