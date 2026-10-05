# `blackout_during_complement`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.supply.blackout_during_complement`
- Lean: `Prosa.Analysis.Facts.Behavior.Supply.blackout_during_complement`
- Certificate: `fs_blackout_during_complement_correspondence`

## Official Rocq

```coq
blackout_during_complement :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_supply_proc_model Job PState ->
forall (sched : @schedule Job PState) (t : instant) (δ : nat),
@blackout_during Job PState sched t (t + δ) = δ - @supply_during Job PState sched t (t + δ)

blackout_during_complement is not universe polymorphic
Arguments blackout_during_complement {Job PState} H_unit_supply_proc_model sched t δ%nat_scope
blackout_during_complement is opaque
Expands to: Constant prosa.analysis.facts.behavior.supply.blackout_during_complement
Declared in library prosa.analysis.facts.behavior.supply, line 153, characters 8-34
@blackout_during_complement
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_supply_proc_model Job PState ->
       forall (sched : @schedule Job PState) (t : instant) (δ : nat),
       @blackout_during Job PState sched t (t + δ) = δ - @supply_during Job PState sched t (t + δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Supply.blackout_during_complement : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
    ∀ (t δ : Prosa.Behavior.Time.instant),
      Prosa.Model.Processor.Supply.blackout_during sched t (t + δ) =
        δ - Prosa.Model.Processor.Supply.supply_during sched t (t + δ)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Supply_blackout_during_complement
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_3 PState ->
       forall t _UU03b4_ : Prosa_Behavior_Time_instant,
       @eq Nat
         (Prosa_Model_Processor_Supply_blackout_during Job
            inst_3 PState sched t
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t _UU03b4_))
         (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Job_work Prosa_Behavior_Time_instant
            (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) _UU03b4_
            (Prosa_Model_Processor_Supply_supply_during Job
               inst_3 PState sched t
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
                  _UU03b4_)))
```
