# `blackout_or_supply`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.supply.blackout_or_supply`
- Lean: `Prosa.Analysis.Facts.Behavior.Supply.blackout_or_supply`
- Certificate: `fs_blackout_or_supply_correspondence`

## Official Rocq

```coq
blackout_or_supply :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (t : instant),
is_true (@is_blackout Job PState sched t) \/ is_true (@has_supply Job PState sched t)

blackout_or_supply is not universe polymorphic
Arguments blackout_or_supply {Job PState} sched t
blackout_or_supply is opaque
Expands to: Constant prosa.analysis.facts.behavior.supply.blackout_or_supply
Declared in library prosa.analysis.facts.behavior.supply, line 42, characters 8-26
@blackout_or_supply
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (t : instant),
       is_true (@is_blackout Job PState sched t) \/ is_true (@has_supply Job PState sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Supply.blackout_or_supply : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
  (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Processor.Supply.is_blackout sched t = true ∨ Prosa.Model.Processor.Supply.has_supply sched t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Supply_blackout_or_supply
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t : Prosa_Behavior_Time_instant),
       Or
         (@eq Bool
            (Prosa_Model_Processor_Supply_is_blackout Job
               inst_3 PState sched t)
            Bool_true)
         (@eq Bool
            (Prosa_Model_Processor_Supply_has_supply Job
               inst_3 PState sched t)
            Bool_true)
```
