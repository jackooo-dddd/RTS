# `supply_at_le_1`

- Kind (Rocq): Remark
- Rocq: `prosa.analysis.facts.behavior.supply.supply_at_le_1`
- Lean: `Prosa.Analysis.Facts.Behavior.Supply.supply_at_le_1`
- Certificate: `fs_supply_at_le_1_correspondence`

## Official Rocq

```coq
supply_at_le_1 :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_supply_proc_model Job PState ->
forall (sched : @schedule Job PState) (t : instant), is_true (@supply_at Job PState sched t <= 1)

supply_at_le_1 is not universe polymorphic
Arguments supply_at_le_1 {Job PState} H_unit_supply_proc_model sched t
supply_at_le_1 is opaque
Expands to: Constant prosa.analysis.facts.behavior.supply.supply_at_le_1
Declared in library prosa.analysis.facts.behavior.supply, line 86, characters 9-23
@supply_at_le_1
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_supply_proc_model Job PState ->
       forall (sched : @schedule Job PState) (t : instant), is_true (@supply_at Job PState sched t <= 1)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Supply.supply_at_le_1 : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
    ∀ (t : Prosa.Behavior.Time.instant), Prosa.Model.Processor.Supply.supply_at sched t ≤ 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Supply_supply_at_le_1
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_3 PState ->
       forall t : Prosa_Behavior_Time_instant,
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Model_Processor_Supply_supply_at Job
            inst_3 PState sched t)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
```
