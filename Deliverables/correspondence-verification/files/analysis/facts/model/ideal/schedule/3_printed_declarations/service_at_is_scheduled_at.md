# `service_at_is_scheduled_at`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.service_at_is_scheduled_at`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.service_at_is_scheduled_at`
- Certificate: `service_at_is_scheduled_at_correspondence`

## Official Rocq

```coq
service_at_is_scheduled_at :
forall {Job : JobType} (sched : @schedule Job (ideal.processor_state Job)) (j : Equality.sort Job)
  (t : instant),
@service_at Job (ideal.processor_state Job) sched j t =
nat_of_bool (@scheduled_at Job (ideal.processor_state Job) sched j t)

service_at_is_scheduled_at is not universe polymorphic
Arguments service_at_is_scheduled_at {Job} sched j t
service_at_is_scheduled_at is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.service_at_is_scheduled_at
Declared in library prosa.analysis.facts.model.ideal.schedule, line 118, characters 8-34
@service_at_is_scheduled_at
     : forall (Job : JobType) (sched : @schedule Job (ideal.processor_state Job)) 
         (j : Equality.sort Job) (t : instant),
       @service_at Job (ideal.processor_state Job) sched j t =
       nat_of_bool (@scheduled_at Job (ideal.processor_state Job) sched j t)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.service_at_is_scheduled_at : ∀ (Job : Prosa.Behavior.Job.JobType)
  [inst : DecidableEq Job] (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.service_at sched j t = (Prosa.Behavior.Service.scheduled_at sched j t).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_service_at_is_scheduled_at
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
            (Prosa_Behavior_Service_scheduled_at_inst4 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               sched j t))
```
