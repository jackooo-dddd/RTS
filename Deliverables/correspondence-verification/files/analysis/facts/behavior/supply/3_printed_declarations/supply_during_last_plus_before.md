# `supply_during_last_plus_before`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.supply.supply_during_last_plus_before`
- Lean: `Prosa.Analysis.Facts.Behavior.Supply.supply_during_last_plus_before`
- Certificate: `fs_supply_during_last_plus_before_correspondence`

## Official Rocq

```coq
supply_during_last_plus_before :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (t1 t2 : nat),
is_true (t1 <= t2) ->
@supply_during Job PState sched t1 t2.+1 =
@supply_during Job PState sched t1 t2 + @supply_at Job PState sched t2

supply_during_last_plus_before is not universe polymorphic
Arguments supply_during_last_plus_before {Job PState} sched (t1 t2)%nat_scope _
supply_during_last_plus_before is opaque
Expands to: Constant prosa.analysis.facts.behavior.supply.supply_during_last_plus_before
Declared in library prosa.analysis.facts.behavior.supply, line 123, characters 8-38
@supply_during_last_plus_before
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (t1 t2 : nat),
       is_true (t1 <= t2) ->
       @supply_during Job PState sched t1 t2.+1 =
       @supply_during Job PState sched t1 t2 + @supply_at Job PState sched t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Supply.supply_during_last_plus_before : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : Prosa.Behavior.Time.instant),
  t1 ≤ t2 →
    Prosa.Model.Processor.Supply.supply_during sched t1 (t2 + 1) =
      Prosa.Model.Processor.Supply.supply_during sched t1 t2 + Prosa.Model.Processor.Supply.supply_at sched t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Supply_supply_during_last_plus_before
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Model_Processor_Supply_supply_during Job
            inst_3 PState sched t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t2
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
         (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
            (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
            (Prosa_Model_Processor_Supply_supply_during Job
               inst_3 PState sched t1 t2)
            (Prosa_Model_Processor_Supply_supply_at Job
               inst_3 PState sched t2))
```
