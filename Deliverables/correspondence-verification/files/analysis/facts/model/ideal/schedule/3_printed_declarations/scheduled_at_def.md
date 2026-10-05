# `scheduled_at_def`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.scheduled_at_def`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.scheduled_at_def`
- Certificate: `scheduled_at_def_correspondence`

## Official Rocq

```coq
scheduled_at_def :
forall {Job : JobType} (sched : @schedule Job (ideal.processor_state Job)) (j : Equality.sort Job)
  (t : instant),
@scheduled_at Job (ideal.processor_state Job) sched j t = (sched t == @Some (Equality.sort Job) j)

scheduled_at_def is not universe polymorphic
Arguments scheduled_at_def {Job} sched j t
scheduled_at_def is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.scheduled_at_def
Declared in library prosa.analysis.facts.model.ideal.schedule, line 92, characters 8-24
@scheduled_at_def
     : forall (Job : JobType) (sched : @schedule Job (ideal.processor_state Job)) 
         (j : Equality.sort Job) (t : instant),
       @scheduled_at Job (ideal.processor_state Job) sched j t = (sched t == @Some (Equality.sort Job) j)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.scheduled_at_def : ∀ (Job : Prosa.Behavior.Job.JobType)
  [inst : DecidableEq Job] (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (j : Job) (t : Prosa.Behavior.Time.instant), Prosa.Behavior.Service.scheduled_at sched j t = decide (sched t = some j)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_scheduled_at_def
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j t)
         (Decidable_decide
            (@eq
               (Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3))
               (sched t) (Option_some Job j))
            (Prosa_Analysis_Facts_Model_Ideal_Schedule_idealStateDecidableEqSome Job
               inst_3 
               (sched t) j))
```
