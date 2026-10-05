# `ideal_proc_has_supply`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.ideal_proc_has_supply`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_has_supply`
- Certificate: `ideal_proc_has_supply_correspondence`

## Official Rocq

```coq
ideal_proc_has_supply :
forall {Job : JobType} (sched : @schedule Job (ideal.processor_state Job)) (t : instant),
is_true (@has_supply Job (ideal.processor_state Job) sched t)

ideal_proc_has_supply is not universe polymorphic
Arguments ideal_proc_has_supply {Job} sched t
ideal_proc_has_supply is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.ideal_proc_has_supply
Declared in library prosa.analysis.facts.model.ideal.schedule, line 136, characters 8-29
@ideal_proc_has_supply
     : forall (Job : JobType) (sched : @schedule Job (ideal.processor_state Job)) (t : instant),
       is_true (@has_supply Job (ideal.processor_state Job) sched t)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_has_supply : ∀ (Job : Prosa.Behavior.Job.JobType)
  [inst : DecidableEq Job] (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t : Prosa.Behavior.Time.instant), Prosa.Model.Processor.Supply.has_supply sched t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_proc_has_supply
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Processor_Supply_has_supply_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched t)
         Bool_true
```
