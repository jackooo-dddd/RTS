# `blackout_during_unit_growth`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.supply.blackout_during_unit_growth`
- Lean: `Prosa.Analysis.Facts.Behavior.Supply.blackout_during_unit_growth`
- Certificate: `fs_blackout_during_unit_growth_correspondence`

## Official Rocq

```coq
blackout_during_unit_growth :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (t : instant),
unit_growth_function (@blackout_during Job PState sched t)

blackout_during_unit_growth is not universe polymorphic
Arguments blackout_during_unit_growth {Job PState} sched t t
blackout_during_unit_growth is opaque
Expands to: Constant prosa.analysis.facts.behavior.supply.blackout_during_unit_growth
Declared in library prosa.analysis.facts.behavior.supply, line 177, characters 8-35
@blackout_during_unit_growth
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (t : instant),
       unit_growth_function (@blackout_during Job PState sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Supply.blackout_during_unit_growth : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t : Prosa.Behavior.Time.instant),
  Prosa.Util.UnitGrowth.unit_growth_function (Prosa.Model.Processor.Supply.blackout_during sched t)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Supply_blackout_during_unit_growth
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t : Prosa_Behavior_Time_instant),
       Prosa_Util_UnitGrowth_unit_growth_function
         (Prosa_Model_Processor_Supply_blackout_during Job
            inst_3 PState sched t)
```
