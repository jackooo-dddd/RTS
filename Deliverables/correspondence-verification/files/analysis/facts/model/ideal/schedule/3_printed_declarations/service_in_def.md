# `service_in_def`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.service_in_def`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.service_in_def`
- Certificate: `service_in_def_correspondence`

## Official Rocq

```coq
service_in_def :
forall {Job : JobType} (j : Equality.sort Job) (s : @State Job (ideal.processor_state Job)),
@service_in Job (ideal.processor_state Job) j s = nat_of_bool (s == @Some (Equality.sort Job) j)

service_in_def is not universe polymorphic
Arguments service_in_def {Job} j s
service_in_def is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.service_in_def
Declared in library prosa.analysis.facts.model.ideal.schedule, line 48, characters 8-22
@service_in_def
     : forall (Job : JobType) (j : Equality.sort Job) (s : @State Job (ideal.processor_state Job)),
       @service_in Job (ideal.processor_state Job) j s = nat_of_bool (s == @Some (Equality.sort Job) j)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.service_in_def : ∀ (Job : Prosa.Behavior.Job.JobType) [inst : DecidableEq Job]
  (j : Job) (s : Prosa.Behavior.Schedule.ProcessorState.State Job),
  (Prosa.Model.Processor.Ideal.processor_state Job).service_in j s = (decide (s = some j)).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_service_in_def
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
