# `scheduled_at_iff_scheduled_job`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule.scheduled_at_iff_scheduled_job`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Schedule.scheduled_at_iff_scheduled_job`
- Certificate: `scheduled_at_iff_scheduled_job_correspondence`

## Official Rocq

```coq
scheduled_at_iff_scheduled_job :
forall {Job : JobType} (sched : @schedule Job (overheads.processor_state Job)) (j : Equality.sort Job)
  (t : instant),
is_true (@scheduled_at Job (overheads.processor_state Job) sched j t) <->
@overheads.scheduled_job Job sched t = @Some (Equality.sort Job) j

scheduled_at_iff_scheduled_job is not universe polymorphic
Arguments scheduled_at_iff_scheduled_job {Job} sched j t
scheduled_at_iff_scheduled_job is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.schedule.scheduled_at_iff_scheduled_job
Declared in library prosa.analysis.facts.model.overheads.schedule, line 87, characters 8-38
@scheduled_at_iff_scheduled_job
     : forall (Job : JobType) (sched : @schedule Job (overheads.processor_state Job)) 
         (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job (overheads.processor_state Job) sched j t) <->
       @overheads.scheduled_job Job sched t = @Some (Equality.sort Job) j
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Schedule.scheduled_at_iff_scheduled_job : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job)) (j : Job)
  (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.scheduled_at sched j t = true ↔ Prosa.Model.Processor.Overheads.scheduled_job sched t = some j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Schedule_scheduled_at_iff_scheduled_job
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Overheads_processor_state Job
                       inst_3))
         (j : Job) (t : Prosa_Behavior_Time_instant),
       Iff
         (@eq Bool
            (Prosa_Behavior_Service_scheduled_at_inst4 Job
               inst_3
               (Prosa_Model_Processor_Overheads_processor_state Job
                  inst_3)
               sched j t)
            Bool_true)
         (@eq (Option Job)
            (Prosa_Model_Processor_Overheads_scheduled_job Job
               inst_3 sched t)
            (Option_some Job j))
```
