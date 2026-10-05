# `terminating_busy_prefix_is_busy_interval`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.busy_interval.terminating_busy_prefix_is_busy_interval`
- Lean: `Prosa.Analysis.Abstract.BusyInterval.terminating_busy_prefix_is_busy_interval`
- Certificate: `terminating_busy_prefix_is_busy_interval_correspondence`

## Official Rocq

```coq
terminating_busy_prefix_is_busy_interval :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job}
  {H3 : Interference Job} {H4 : InterferingWorkload Job} (sched : @schedule Job PState)
  (j : Equality.sort Job),
is_true (@job_cost_positive Job H2 j) ->
forall (t1 : instant) (t2 t2' : nat),
is_true (t2 <= t2') ->
@busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t2 ->
~ @busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t2' ->
exists t2'' : instant, @busy_interval Job H1 H2 PState sched H3 H4 j t1 t2''

terminating_busy_prefix_is_busy_interval is not universe polymorphic
Arguments terminating_busy_prefix_is_busy_interval {Job H1 H2 PState H3 H4} sched 
  j H_job_cost_positive t1 (t2 t2')%nat_scope _ _ _
terminating_busy_prefix_is_busy_interval is opaque
Expands to: Constant prosa.analysis.abstract.busy_interval.terminating_busy_prefix_is_busy_interval
Declared in library prosa.analysis.abstract.busy_interval, line 75, characters 8-48
@terminating_busy_prefix_is_busy_interval
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job)
         (H3 : Interference Job) (H4 : InterferingWorkload Job) (sched : @schedule Job PState)
         (j : Equality.sort Job),
       is_true (@job_cost_positive Job H2 j) ->
       forall (t1 : instant) (t2 t2' : nat),
       is_true (t2 <= t2') ->
       @busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t2 ->
       ~ @busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t2' ->
       exists t2'' : instant, @busy_interval Job H1 H2 PState sched H3 H4 j t1 t2''
```

## Lean

```lean
@Prosa.Analysis.Abstract.BusyInterval.terminating_busy_prefix_is_busy_interval : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [inst_3 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_4 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job),
  Prosa.Model.Job.Properties.job_cost_positive j = true →
    ∀ (t1 : Prosa.Behavior.Time.instant) (t2 t2' : ℕ),
      t2 ≤ t2' →
        Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2 →
          ¬Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2' →
            ∃ t2'', Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2''
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_BusyInterval_terminating_busy_prefix_is_busy_interval
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
         (j : Job),
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_9 j)
         Bool_true ->
       forall (t1 : Prosa_Behavior_Time_instant) (t2 t2' : Nat),
       LE_le_inst1 Nat instLENat t2 t2' ->
       Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
         inst_3
         inst_14
         inst_17
         inst_6
         inst_9 PState sched j t1 t2 ->
       Not
         (Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
            inst_3
            inst_14
            inst_17
            inst_6
            inst_9 PState sched j t1 t2') ->
       Exists Prosa_Behavior_Time_instant
         (fun t2'' : Prosa_Behavior_Time_instant =>
          Prosa_Analysis_Abstract_Definitions_busy_interval Job
            inst_3
            inst_14
            inst_17
            inst_6
            inst_9 PState sched j t1 t2'')
```
