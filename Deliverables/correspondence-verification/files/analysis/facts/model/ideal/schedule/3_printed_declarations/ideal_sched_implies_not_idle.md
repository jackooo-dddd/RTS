# `ideal_sched_implies_not_idle`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.ideal.schedule.ideal_sched_implies_not_idle`
- Lean: `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_sched_implies_not_idle`
- Certificate: `ideal_sched_implies_not_idle_correspondence`

## Official Rocq

```coq
ideal_sched_implies_not_idle :
forall {Job : JobType} (sched : @schedule Job (ideal.processor_state Job)) (j : Equality.sort Job)
  (t : instant),
is_true (@scheduled_at Job (ideal.processor_state Job) sched j t) ->
~ is_true (@ideal.ideal_is_idle Job sched t)

ideal_sched_implies_not_idle is not universe polymorphic
Arguments ideal_sched_implies_not_idle {Job} sched j t _ _
ideal_sched_implies_not_idle is opaque
Expands to: Constant prosa.analysis.facts.model.ideal.schedule.ideal_sched_implies_not_idle
Declared in library prosa.analysis.facts.model.ideal.schedule, line 158, characters 8-36
@ideal_sched_implies_not_idle
     : forall (Job : JobType) (sched : @schedule Job (ideal.processor_state Job)) 
         (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job (ideal.processor_state Job) sched j t) ->
       ~ is_true (@ideal.ideal_is_idle Job sched t)
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_sched_implies_not_idle : ∀ (Job : Prosa.Behavior.Job.JobType)
  [inst : DecidableEq Job] (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.scheduled_at sched j t = true → ¬Prosa.Model.Processor.Ideal.ideal_is_idle sched t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_sched_implies_not_idle
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
         Bool_true ->
       Not
         (@eq Bool
            (Prosa_Model_Processor_Ideal_ideal_is_idle Job
               inst_3 sched t)
            Bool_true)
```
