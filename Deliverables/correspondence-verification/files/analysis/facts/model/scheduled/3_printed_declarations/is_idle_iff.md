# `is_idle_iff`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.model.scheduled.is_idle_iff`
- Lean: `Prosa.Analysis.Facts.Model.Scheduled.is_idle_iff`
- Certificate: `is_idle_iff_correspondence`

## Official Rocq

```coq
is_idle_iff :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (t : instant),
@is_idle Job PState arr_seq sched t =
(@scheduled_job_at Job PState arr_seq sched t == @None (Equality.sort Job))

is_idle_iff is not universe polymorphic
Arguments is_idle_iff {Job PState} arr_seq sched t
is_idle_iff is opaque
Expands to: Constant prosa.analysis.facts.model.scheduled.is_idle_iff
Declared in library prosa.analysis.facts.model.scheduled, line 181, characters 14-25
@is_idle_iff
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (t : instant),
       @is_idle Job PState arr_seq sched t =
       (@scheduled_job_at Job PState arr_seq sched t == @None (Equality.sort Job))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Scheduled.is_idle_iff : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState) (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t =
    decide (Prosa.Model.Schedule.Scheduled.scheduled_job_at arr_seq sched t = none)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Scheduled_is_idle_iff
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Schedule_Scheduled_is_idle Job
            inst_3 PState arr_seq sched t)
         (Decidable_decide
            (@eq (Option Job)
               (Prosa_Model_Schedule_Scheduled_scheduled_job_at Job
                  inst_3 PState arr_seq
                  sched t)
               (Option_none Job))
            (Option_decidableEqNone Job
               (Prosa_Model_Schedule_Scheduled_scheduled_job_at Job
                  inst_3 PState arr_seq
                  sched t)))
```
