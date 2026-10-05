# `ideal_not_idle_implies_sched`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.ideal_not_idle_implies_sched`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_not_idle_implies_sched`
- Certificate: `ideal_not_idle_implies_sched_correspondence`

## Official Rocq

```coq
ideal_not_idle_implies_sched :
forall {Job : JobType} (sched : @schedule Job (ideal.processor_state Job)) (j : Equality.sort Job)
  (t : instant),
is_true (@ideal.ideal_is_idle Job sched t) -> @service_at Job (ideal.processor_state Job) sched j t = 0

ideal_not_idle_implies_sched is not universe polymorphic
Arguments ideal_not_idle_implies_sched {Job} sched j t _
ideal_not_idle_implies_sched is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.ideal_not_idle_implies_sched
Declared in library prosa.analysis.facts.model.ideal.schedule, line 168, characters 8-36
@ideal_not_idle_implies_sched
     : forall (Job : JobType) (sched : @schedule Job (ideal.processor_state Job)) 
         (j : Equality.sort Job) (t : instant),
       is_true (@ideal.ideal_is_idle Job sched t) ->
       @service_at Job (ideal.processor_state Job) sched j t = 0
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_not_idle_implies_sched : ∀ (Job : Prosa.Behavior.Job.JobType)
  [inst : DecidableEq Job] (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Processor.Ideal.ideal_is_idle sched t = true → Prosa.Behavior.Service.service_at sched j t = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_not_idle_implies_sched
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Processor_Ideal_ideal_is_idle Job
            inst_3 sched t)
         Bool_true ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j t)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
```
