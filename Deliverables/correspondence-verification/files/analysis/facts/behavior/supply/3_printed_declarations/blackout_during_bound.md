# `blackout_during_bound`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.supply.blackout_during_bound`
- Lean: `Prosa.Analysis.Facts.Behavior.Supply.blackout_during_bound`
- Certificate: `fs_blackout_during_bound_correspondence`

## Official Rocq

```coq
blackout_during_bound :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (t : instant) (δ : nat),
is_true (@blackout_during Job PState sched t (t + δ) <= δ)

blackout_during_bound is not universe polymorphic
Arguments blackout_during_bound {Job PState} sched t δ%nat_scope
blackout_during_bound is opaque
Expands to: Constant prosa.analysis.facts.behavior.supply.blackout_during_bound
Declared in library prosa.analysis.facts.behavior.supply, line 113, characters 8-29
@blackout_during_bound
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (t : instant) (δ : nat),
       is_true (@blackout_during Job PState sched t (t + δ) <= δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Supply.blackout_during_bound : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t δ : Prosa.Behavior.Time.instant),
  Prosa.Model.Processor.Supply.blackout_during sched t (t + δ) ≤ δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Supply_blackout_during_bound
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t _UU03b4_ : Prosa_Behavior_Time_instant),
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Processor_Supply_blackout_during Job
            inst_3 PState sched t
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t _UU03b4_))
         _UU03b4_
```
