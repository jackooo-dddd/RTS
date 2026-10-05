# `service_in_service_on`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.service_in_service_on`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.service_in_service_on`
- Certificate: `service_in_service_on_correspondence`

## Official Rocq

```coq
service_in_service_on :
forall {Job : JobType} (j : Equality.sort Job) (s : @State Job (ideal.processor_state Job)),
@service_in Job (ideal.processor_state Job) j s = @service_on Job (ideal.processor_state Job) j s tt

service_in_service_on is not universe polymorphic
Arguments service_in_service_on {Job} j s
service_in_service_on is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.service_in_service_on
Declared in library prosa.analysis.facts.model.ideal.schedule, line 39, characters 8-29
@service_in_service_on
     : forall (Job : JobType) (j : Equality.sort Job) (s : @State Job (ideal.processor_state Job)),
       @service_in Job (ideal.processor_state Job) j s = @service_on Job (ideal.processor_state Job) j s tt
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.service_in_service_on : ∀ (Job : Prosa.Behavior.Job.JobType)
  [inst : DecidableEq Job] (j : Job) (s : Prosa.Behavior.Schedule.ProcessorState.State Job),
  (Prosa.Model.Processor.Ideal.processor_state Job).service_in j s = Prosa.Behavior.Schedule.service_on j s ()
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_service_in_service_on
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (j : Job)
         (s : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
                inst_3
                (Prosa_Model_Processor_Ideal_processor_state Job
                   inst_3)),
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Schedule_ProcessorState_service_in_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            j s)
         (Prosa_Behavior_Schedule_ProcessorState_service_on_inst2 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            j s Unit_unit)
```
