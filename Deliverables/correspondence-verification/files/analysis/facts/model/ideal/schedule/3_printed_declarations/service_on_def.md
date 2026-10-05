# `service_on_def`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.service_on_def`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.service_on_def`
- Certificate: `service_on_def_correspondence`

## Official Rocq

```coq
service_on_def :
forall {Job : JobType} (j : Equality.sort Job) (s : @State Job (ideal.processor_state Job))
  (c : Finite.sort (@Core Job (ideal.processor_state Job))),
@service_on Job (ideal.processor_state Job) j s c = nat_of_bool (s == @Some (Equality.sort Job) j)

service_on_def is not universe polymorphic
Arguments service_on_def {Job} j s c
service_on_def is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.service_on_def
Declared in library prosa.analysis.facts.model.ideal.schedule, line 99, characters 8-22
@service_on_def
     : forall (Job : JobType) (j : Equality.sort Job) (s : @State Job (ideal.processor_state Job))
         (c : Finite.sort (@Core Job (ideal.processor_state Job))),
       @service_on Job (ideal.processor_state Job) j s c = nat_of_bool (s == @Some (Equality.sort Job) j)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.service_on_def : ∀ (Job : Prosa.Behavior.Job.JobType) [inst : DecidableEq Job]
  (j : Job) (s : Prosa.Behavior.Schedule.ProcessorState.State Job)
  (c : Prosa.Behavior.Schedule.ProcessorState.Core Job),
  Prosa.Behavior.Schedule.service_on j s c = (decide (s = some j)).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_service_on_def
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (j : Job)
         (s : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
                inst_3
                (Prosa_Model_Processor_Ideal_processor_state Job
                   inst_3))
         (c : Prosa_Behavior_Schedule_ProcessorState_Core_inst2 Job
                inst_3
                (Prosa_Model_Processor_Ideal_processor_state Job
                   inst_3)),
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Schedule_ProcessorState_service_on_inst2 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            j s c)
         (Bool_toNat
            (Decidable_decide
               (@eq
                  (Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
                     inst_3
                     (Prosa_Model_Processor_Ideal_processor_state Job
                        inst_3))
                  s (Option_some Job j))
               (Prosa_Analysis_Facts_Model_Ideal_Schedule_idealStateDecidableEqSome Job
                  inst_3 s j)))
```
