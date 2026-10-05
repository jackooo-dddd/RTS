# `scheduled_job_dec`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.schedule.scheduled_job_dec`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Schedule.scheduled_job_dec`
- Certificate: `scheduled_job_dec_correspondence`

## Official Rocq

```coq
scheduled_job_dec :
forall {Job : JobType} (sched : @schedule Job (overheads.processor_state Job)) (t : instant),
@overheads.scheduled_job Job sched t = @None (Equality.sort Job) \/
(exists j : Equality.sort Job, @overheads.scheduled_job Job sched t = @Some (Equality.sort Job) j)

scheduled_job_dec is not universe polymorphic
Arguments scheduled_job_dec {Job} sched t
scheduled_job_dec is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.schedule.scheduled_job_dec
Declared in library prosa.analysis.facts.model.overheads.schedule, line 78, characters 8-25
@scheduled_job_dec
     : forall (Job : JobType) (sched : @schedule Job (overheads.processor_state Job)) (t : instant),
       @overheads.scheduled_job Job sched t = @None (Equality.sort Job) \/
       (exists j : Equality.sort Job, @overheads.scheduled_job Job sched t = @Some (Equality.sort Job) j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Schedule.scheduled_job_dec : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job))
  (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Processor.Overheads.scheduled_job sched t = none ∨
    ∃ j, Prosa.Model.Processor.Overheads.scheduled_job sched t = some j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Schedule_scheduled_job_dec
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Overheads_processor_state Job
                       inst_3))
         (t : Prosa_Behavior_Time_instant),
       Or
         (@eq (Option Job)
            (Prosa_Model_Processor_Overheads_scheduled_job Job
               inst_3 sched t)
            (Option_none Job))
         (Exists Job
            (fun j : Job =>
             Prosa_Model_Processor_Overheads_scheduled_job Job
               inst_3 sched t =
             Option_some Job j))
```
