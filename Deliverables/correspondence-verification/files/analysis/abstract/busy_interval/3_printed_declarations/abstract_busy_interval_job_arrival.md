# `abstract_busy_interval_job_arrival`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.abstract.busy_interval.abstract_busy_interval_job_arrival`
- Lean: `Prosa.Analysis.Abstract.BusyInterval.abstract_busy_interval_job_arrival`
- Certificate: `abstract_busy_interval_job_arrival_correspondence`

## Official Rocq

```coq
abstract_busy_interval_job_arrival :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job}
  {H3 : Interference Job} {H4 : InterferingWorkload Job} (sched : @schedule Job PState)
  (j : Equality.sort Job) (t1 t2 : instant),
@busy_interval Job H1 H2 PState sched H3 H4 j t1 t2 -> is_true (t1 <= @job_arrival Job H1 j)

abstract_busy_interval_job_arrival is not universe polymorphic
Arguments abstract_busy_interval_job_arrival {Job H1 H2 PState H3 H4} sched j t1 t2 H_busy_interval
abstract_busy_interval_job_arrival is opaque
Expands to: Constant prosa.analysis.abstract.busy_interval.abstract_busy_interval_job_arrival
Declared in library prosa.analysis.abstract.busy_interval, line 175, characters 7-41
@abstract_busy_interval_job_arrival
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job)
         (H3 : Interference Job) (H4 : InterferingWorkload Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : instant),
       @busy_interval Job H1 H2 PState sched H3 H4 j t1 t2 -> is_true (t1 <= @job_arrival Job H1 j)
```

## Lean

```lean
@Prosa.Analysis.Abstract.BusyInterval.abstract_busy_interval_job_arrival : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [inst_3 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_4 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 → t1 ≤ Prosa.Behavior.Job.job_arrival j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_BusyInterval_abstract_busy_interval_job_arrival
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
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j)
```
