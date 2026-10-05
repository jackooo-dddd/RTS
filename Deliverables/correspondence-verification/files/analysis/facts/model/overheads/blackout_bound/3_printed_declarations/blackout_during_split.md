# `blackout_during_split`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.blackout_bound.blackout_during_split`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.blackout_during_split`
- Certificate: `blackout_during_split_correspondence`

## Official Rocq

```coq
blackout_during_split :
forall {Job : JobType} (sched : @schedule Job (processor_state Job)) (t1 t2 : instant),
@blackout_during Job (processor_state Job) sched t1 t2 =
@total_time_in_dispatch Job sched t1 t2 + @total_time_in_context_switch Job sched t1 t2 +
@total_time_in_CRPD Job sched t1 t2

blackout_during_split is not universe polymorphic
Arguments blackout_during_split {Job} sched t1 t2
blackout_during_split is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.blackout_bound.blackout_during_split
Declared in library prosa.analysis.facts.model.overheads.blackout_bound, line 41, characters 8-29
@blackout_during_split
     : forall (Job : JobType) (sched : @schedule Job (processor_state Job)) (t1 t2 : instant),
       @blackout_during Job (processor_state Job) sched t1 t2 =
       @total_time_in_dispatch Job sched t1 t2 + @total_time_in_context_switch Job sched t1 t2 +
       @total_time_in_CRPD Job sched t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.blackout_during_split : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job))
  (t1 t2 : Prosa.Behavior.Time.instant),
  Prosa.Model.Processor.Supply.blackout_during sched t1 t2 =
    Prosa.Model.Processor.Overheads.total_time_in_dispatch sched t1 t2 +
        Prosa.Model.Processor.Overheads.total_time_in_context_switch sched t1 t2 +
      Prosa.Model.Processor.Overheads.total_time_in_CRPD sched t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_BlackoutBound_blackout_during_split
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Overheads_processor_state Job
                       inst_3))
         (t1 t2 : Prosa_Behavior_Time_instant),
       @eq Nat
         (Prosa_Model_Processor_Supply_blackout_during_inst4 Job
            inst_3
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_3)
            sched t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
               (Prosa_Model_Processor_Overheads_total_time_in_dispatch Job
                  inst_3
                  sched t1 t2)
               (Prosa_Model_Processor_Overheads_total_time_in_context_switch Job
                  inst_3
                  sched t1 t2))
            (Prosa_Model_Processor_Overheads_total_time_in_CRPD Job
               inst_3 sched
               t1 t2))
```
