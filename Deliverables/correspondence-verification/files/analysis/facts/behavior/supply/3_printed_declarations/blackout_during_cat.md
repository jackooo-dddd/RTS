# `blackout_during_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.supply.blackout_during_cat`
- Lean: `Prosa.Analysis.Facts.Behavior.Supply.blackout_during_cat`
- Certificate: `fs_blackout_during_cat_correspondence`

## Official Rocq

```coq
blackout_during_cat :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (t1 t2 t : instant),
is_true (t1 <= t <= t2) ->
@blackout_during Job PState sched t1 t + @blackout_during Job PState sched t t2 =
@blackout_during Job PState sched t1 t2

blackout_during_cat is not universe polymorphic
Arguments blackout_during_cat {Job PState} sched t1 t2 t _
blackout_during_cat is opaque
Expands to: Constant prosa.analysis.facts.behavior.supply.blackout_during_cat
Declared in library prosa.analysis.facts.behavior.supply, line 165, characters 8-27
@blackout_during_cat
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (t1 t2 t : instant),
       is_true (t1 <= t <= t2) ->
       @blackout_during Job PState sched t1 t + @blackout_during Job PState sched t t2 =
       @blackout_during Job PState sched t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Supply.blackout_during_cat : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 t : Prosa.Behavior.Time.instant),
  t1 ≤ t ∧ t ≤ t2 →
    Prosa.Model.Processor.Supply.blackout_during sched t1 t + Prosa.Model.Processor.Supply.blackout_during sched t t2 =
      Prosa.Model.Processor.Supply.blackout_during sched t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Supply_blackout_during_cat
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 t : Prosa_Behavior_Time_instant),
       And (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t)
         (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t t2) ->
       @eq Nat
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Processor_Supply_blackout_during Job
               inst_3 PState sched t1 t)
            (Prosa_Model_Processor_Supply_blackout_during Job
               inst_3 PState sched t t2))
         (Prosa_Model_Processor_Supply_blackout_during Job
            inst_3 PState sched t1 t2)
```
