# `busy_interval_is_unique`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.abstract.definitions.busy_interval_is_unique`
- Lean: `Prosa.Analysis.Abstract.Definitions.busy_interval_is_unique`
- Certificate: `ad_busy_interval_unique_statement_correspondence`

## Official Rocq

```coq
busy_interval_is_unique :
forall {Job : JobType} {H0 : JobArrival Job} {H1 : JobCost Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState) {H2 : Interference Job} {H3 : InterferingWorkload Job}
  (j : Equality.sort Job) (t1 t2 t1' t2' : instant),
@busy_interval Job H0 H1 PState sched H2 H3 j t1 t2 ->
@busy_interval Job H0 H1 PState sched H2 H3 j t1' t2' -> t1 = t1' /\ t2 = t2'

busy_interval_is_unique is not universe polymorphic
Arguments busy_interval_is_unique {Job H0 H1 PState} sched {H2 H3} j t1 t2 t1' t2' _ _
busy_interval_is_unique is opaque
Expands to: Constant prosa.analysis.abstract.definitions.busy_interval_is_unique
Declared in library prosa.analysis.abstract.definitions, line 162, characters 7-30
@busy_interval_is_unique
     : forall (Job : JobType) (H0 : JobArrival Job) (H1 : JobCost Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState) (H2 : Interference Job) (H3 : InterferingWorkload Job)
         (j : Equality.sort Job) (t1 t2 t1' t2' : instant),
       @busy_interval Job H0 H1 PState sched H2 H3 j t1 t2 ->
       @busy_interval Job H0 H1 PState sched H2 H3 j t1' t2' -> t1 = t1' /\ t2 = t2'
```

## Lean

```lean
@Prosa.Analysis.Abstract.Definitions.busy_interval_is_unique : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_2 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 t1' t2' : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
    Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1' t2' → t1 = t1' ∧ t2 = t2'
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_busy_interval_is_unique
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (inst_9 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_3)
         (inst_12 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_15 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 t1' t2' : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_3
         inst_6
         inst_9
         inst_12
         inst_15 PState sched j t1 t2 ->
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_3
         inst_6
         inst_9
         inst_12
         inst_15 PState sched j t1' t2' ->
       And (@eq Prosa_Behavior_Time_instant t1 t1') (@eq Prosa_Behavior_Time_instant t2 t2')
```
