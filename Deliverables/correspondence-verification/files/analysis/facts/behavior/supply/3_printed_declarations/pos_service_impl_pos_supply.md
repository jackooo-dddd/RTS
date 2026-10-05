# `pos_service_impl_pos_supply`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.supply.pos_service_impl_pos_supply`
- Lean: `Prosa.Analysis.Facts.Behavior.Supply.pos_service_impl_pos_supply`
- Certificate: `fs_pos_service_impl_pos_supply_correspondence`

## Official Rocq

```coq
pos_service_impl_pos_supply :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t : instant),
is_true (0 < @service_at Job PState sched j t) -> is_true (0 < @supply_at Job PState sched t)

pos_service_impl_pos_supply is not universe polymorphic
Arguments pos_service_impl_pos_supply {Job PState} sched j t _
pos_service_impl_pos_supply is opaque
Expands to: Constant prosa.analysis.facts.behavior.supply.pos_service_impl_pos_supply
Declared in library prosa.analysis.facts.behavior.supply, line 32, characters 12-39
@pos_service_impl_pos_supply
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (0 < @service_at Job PState sched j t) -> is_true (0 < @supply_at Job PState sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Supply.pos_service_impl_pos_supply : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
  0 < Prosa.Behavior.Service.service_at sched j t → 0 < Prosa.Model.Processor.Supply.supply_at sched t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Supply_pos_service_impl_pos_supply
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j t) ->
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Model_Processor_Supply_supply_at Job
            inst_3 PState sched t)
```
