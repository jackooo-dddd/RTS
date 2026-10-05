# `job_completes_within_busy_interval`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.busy_interval.job_completes_within_busy_interval`
- Lean: `Prosa.Analysis.Abstract.BusyInterval.job_completes_within_busy_interval`
- Certificate: `job_completes_within_busy_interval_correspondence`

## Official Rocq

```coq
job_completes_within_busy_interval :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job}
  {H3 : Interference Job} {H4 : InterferingWorkload Job} (sched : @schedule Job PState)
  (j : Equality.sort Job) (t1 t2 : instant),
@busy_interval Job H1 H2 PState sched H3 H4 j t1 t2 -> is_true (@completed_by Job PState sched H2 j t2)

job_completes_within_busy_interval is not universe polymorphic
Arguments job_completes_within_busy_interval {Job H1 H2 PState H3 H4} sched j t1 t2 H_busy_interval
job_completes_within_busy_interval is opaque
Expands to: Constant prosa.analysis.abstract.busy_interval.job_completes_within_busy_interval
Declared in library prosa.analysis.abstract.busy_interval, line 107, characters 8-42
@job_completes_within_busy_interval
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job)
         (H3 : Interference Job) (H4 : InterferingWorkload Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : instant),
       @busy_interval Job H1 H2 PState sched H3 H4 j t1 t2 ->
       is_true (@completed_by Job PState sched H2 j t2)
```

## Lean

```lean
@Prosa.Analysis.Abstract.BusyInterval.job_completes_within_busy_interval : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [inst_3 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_4 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
    Prosa.Behavior.Service.completed_by sched j t2 = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_BusyInterval_job_completes_within_busy_interval
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (inst_14 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (inst_17 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_3
         inst_14
         inst_17
         inst_6
         inst_9 PState sched j t1 t2 ->
       @eq Bool
         (Prosa_Behavior_Service_completed_by Job
            inst_3 PState sched
            inst_9 j t2)
         Bool_true
```
