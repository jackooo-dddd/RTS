# `supply_at_complement`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.supply.supply_at_complement`
- Lean: `Prosa.Analysis.Facts.Behavior.Supply.supply_at_complement`
- Certificate: `fs_supply_at_complement_correspondence`

## Official Rocq

```coq
supply_at_complement :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_supply_proc_model Job PState ->
forall (sched : @schedule Job PState) (t : instant),
@supply_at Job PState sched t = 1 - nat_of_bool (@is_blackout Job PState sched t)

supply_at_complement is not universe polymorphic
Arguments supply_at_complement {Job PState} H_unit_supply_proc_model sched t
supply_at_complement is opaque
Expands to: Constant prosa.analysis.facts.behavior.supply.supply_at_complement
Declared in library prosa.analysis.facts.behavior.supply, line 67, characters 8-28
@supply_at_complement
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_supply_proc_model Job PState ->
       forall (sched : @schedule Job PState) (t : instant),
       @supply_at Job PState sched t = 1 - nat_of_bool (@is_blackout Job PState sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Supply.supply_at_complement : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
    ∀ (t : Prosa.Behavior.Time.instant),
      Prosa.Model.Processor.Supply.supply_at sched t = 1 - (Prosa.Model.Processor.Supply.is_blackout sched t).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Supply_supply_at_complement
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_3 PState ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Prosa_Behavior_Job_work
         (Prosa_Model_Processor_Supply_supply_at Job
            inst_3 PState sched t)
         (HSub_hSub_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
            (instHSub_inst1 Prosa_Behavior_Job_work instSubNat)
            (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
            (Bool_toNat
               (Prosa_Model_Processor_Supply_is_blackout Job
                  inst_3 PState sched t)))
```
