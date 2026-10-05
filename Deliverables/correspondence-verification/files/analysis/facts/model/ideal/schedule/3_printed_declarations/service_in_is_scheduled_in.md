# `service_in_is_scheduled_in`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.service_in_is_scheduled_in`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.service_in_is_scheduled_in`
- Certificate: `service_in_is_scheduled_in_correspondence`

## Official Rocq

```coq
service_in_is_scheduled_in :
forall {Job : JobType} (j : Equality.sort Job) (s : @State Job (ideal.processor_state Job)),
@service_in Job (ideal.processor_state Job) j s =
nat_of_bool (@scheduled_in Job (ideal.processor_state Job) j s)

service_in_is_scheduled_in is not universe polymorphic
Arguments service_in_is_scheduled_in {Job} j s
service_in_is_scheduled_in is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.service_in_is_scheduled_in
Declared in library prosa.analysis.facts.model.ideal.schedule, line 111, characters 8-34
@service_in_is_scheduled_in
     : forall (Job : JobType) (j : Equality.sort Job) (s : @State Job (ideal.processor_state Job)),
       @service_in Job (ideal.processor_state Job) j s =
       nat_of_bool (@scheduled_in Job (ideal.processor_state Job) j s)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.service_in_is_scheduled_in : ∀ (Job : Prosa.Behavior.Job.JobType)
  [inst : DecidableEq Job] (j : Job) (s : Prosa.Behavior.Schedule.ProcessorState.State Job),
  (Prosa.Model.Processor.Ideal.processor_state Job).service_in j s =
    ((Prosa.Model.Processor.Ideal.processor_state Job).scheduled_in j s).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_service_in_is_scheduled_in
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
         (Bool_toNat
            (Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               j s))
```
