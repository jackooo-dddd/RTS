# `service_at_le_supply_at`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.supply.service_at_le_supply_at`
- Lean: `Prosa.Analysis.Facts.Behavior.Supply.service_at_le_supply_at`
- Certificate: `fs_service_at_le_supply_at_correspondence`

## Official Rocq

```coq
service_at_le_supply_at :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant),
is_true (@service_at Job PState sched j t <= @supply_at Job PState sched t)

service_at_le_supply_at is not universe polymorphic
Arguments service_at_le_supply_at {Job PState} sched j t
service_at_le_supply_at is opaque
Expands to: Constant prosa.analysis.facts.behavior.supply.service_at_le_supply_at
Declared in library prosa.analysis.facts.behavior.supply, line 22, characters 8-31
@service_at_le_supply_at
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (@service_at Job PState sched j t <= @supply_at Job PState sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Supply.service_at_le_supply_at : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.service_at sched j t ≤ Prosa.Model.Processor.Supply.supply_at sched t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Supply_service_at_le_supply_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j t)
         (Prosa_Model_Processor_Supply_supply_at Job
            inst_3 PState sched t)
```
