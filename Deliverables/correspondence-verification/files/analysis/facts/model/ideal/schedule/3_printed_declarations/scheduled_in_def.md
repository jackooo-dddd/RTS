# `scheduled_in_def`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.scheduled_in_def`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.scheduled_in_def`
- Certificate: `scheduled_in_def_correspondence`

## Official Rocq

```coq
scheduled_in_def :
forall {Job : JobType} (j : Equality.sort Job) (s : @State Job (ideal.processor_state Job)),
@scheduled_in Job (ideal.processor_state Job) j s = (s == @Some (Equality.sort Job) j)

scheduled_in_def is not universe polymorphic
Arguments scheduled_in_def {Job} j s
scheduled_in_def is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.scheduled_in_def
Declared in library prosa.analysis.facts.model.ideal.schedule, line 82, characters 8-24
@scheduled_in_def
     : forall (Job : JobType) (j : Equality.sort Job) (s : @State Job (ideal.processor_state Job)),
       @scheduled_in Job (ideal.processor_state Job) j s = (s == @Some (Equality.sort Job) j)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.scheduled_in_def : ∀ (Job : Prosa.Behavior.Job.JobType)
  [inst : DecidableEq Job] (j : Job) (s : Prosa.Behavior.Schedule.ProcessorState.State Job),
  (Prosa.Model.Processor.Ideal.processor_state Job).scheduled_in j s = decide (s = some j)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_scheduled_in_def
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (j : Job)
         (s : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
                inst_3
                (Prosa_Model_Processor_Ideal_processor_state Job
                   inst_3)),
       @eq Bool
         (Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            j s)
         (Decidable_decide
            (@eq
               (Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3))
               s (Option_some Job j))
            (Prosa_Analysis_Facts_Model_Ideal_Schedule_idealStateDecidableEqSome Job
               inst_3 s j))
```
