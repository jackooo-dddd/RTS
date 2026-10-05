# `busy_interval_prefix_case`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.busy_interval.busy_interval_prefix_case`
- Lean: `Prosa.Analysis.Abstract.BusyInterval.busy_interval_prefix_case`
- Certificate: `busy_interval_prefix_case_correspondence`

## Official Rocq

```coq
busy_interval_prefix_case :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job}
  {H3 : Interference Job} {H4 : InterferingWorkload Job} (sched : @schedule Job PState)
  (j : Equality.sort Job) (t1 t2 : instant),
@busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t2 \/
~ @busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t2

busy_interval_prefix_case is not universe polymorphic
Arguments busy_interval_prefix_case {Job H1 H2 PState H3 H4} sched j t1 t2
busy_interval_prefix_case is opaque
Expands to: Constant prosa.analysis.abstract.busy_interval.busy_interval_prefix_case
Declared in library prosa.analysis.abstract.busy_interval, line 52, characters 8-33
@busy_interval_prefix_case
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job)
         (H3 : Interference Job) (H4 : InterferingWorkload Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : instant),
       @busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t2 \/
       ~ @busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Abstract.BusyInterval.busy_interval_prefix_case : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [inst_3 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_4 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2 ∨
    ¬Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_BusyInterval_busy_interval_prefix_case
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
       Or
         (Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
            inst_3
            inst_14
            inst_17
            inst_6
            inst_9 PState sched j t1 t2)
         (Not
            (Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
               inst_3
               inst_14
               inst_17
               inst_6
               inst_9 PState sched j t1 t2))
```
