# `service_at_def`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.service_at_def`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.service_at_def`
- Certificate: `service_at_def_correspondence`

## Official Rocq

```coq
service_at_def :
forall {Job : JobType} (sched : @schedule Job (ideal.processor_state Job)) (j : Equality.sort Job)
  (t : instant),
@service_at Job (ideal.processor_state Job) sched j t = nat_of_bool (sched t == @Some (Equality.sort Job) j)

service_at_def is not universe polymorphic
Arguments service_at_def {Job} sched j t
service_at_def is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.service_at_def
Declared in library prosa.analysis.facts.model.ideal.schedule, line 104, characters 8-22
@service_at_def
     : forall (Job : JobType) (sched : @schedule Job (ideal.processor_state Job)) 
         (j : Equality.sort Job) (t : instant),
       @service_at Job (ideal.processor_state Job) sched j t =
       nat_of_bool (sched t == @Some (Equality.sort Job) j)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.service_at_def : ∀ (Job : Prosa.Behavior.Job.JobType) [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)) (j : Job)
  (t : Prosa.Behavior.Time.instant), Prosa.Behavior.Service.service_at sched j t = (decide (sched t = some j)).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_service_at_def
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j t)
         (Bool_toNat
            (Decidable_decide
               (@eq
                  (Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
                     inst_3
                     (Prosa_Model_Processor_Ideal_processor_state Job
                        inst_3))
                  (sched t) (Option_some Job j))
               (Prosa_Analysis_Facts_Model_Ideal_Schedule_idealStateDecidableEqSome Job
                  inst_3 
                  (sched t) j)))
```
