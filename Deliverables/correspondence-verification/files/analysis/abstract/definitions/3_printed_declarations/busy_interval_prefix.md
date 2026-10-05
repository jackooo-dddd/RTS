# `busy_interval_prefix`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.definitions.busy_interval_prefix`
- Lean: `Prosa.Analysis.Abstract.Definitions.busy_interval_prefix`
- Certificate: `ad_busy_interval_prefix_correspondence`

## Official Rocq

```coq
busy_interval_prefix :
forall {Job : JobType},
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
@schedule Job PState ->
Interference Job -> InterferingWorkload Job -> Equality.sort Job -> instant -> instant -> Prop

busy_interval_prefix is not universe polymorphic
Arguments busy_interval_prefix {Job H0 H1 PState} sched {H2 H3} j t1 t2
busy_interval_prefix is transparent
Expands to: Constant prosa.analysis.abstract.definitions.busy_interval_prefix
Declared in library prosa.analysis.abstract.definitions, line 149, characters 13-33
@busy_interval_prefix
     : forall Job : JobType,
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       @schedule Job PState ->
       Interference Job -> InterferingWorkload Job -> Equality.sort Job -> instant -> instant -> Prop
```

Body:

```coq
busy_interval_prefix =
fun (Job : JobType) (H0 : JobArrival Job) (H1 : JobCost Job) (PState : ProcessorState Job)
  (sched : @schedule Job PState) (H2 : Interference Job) (H3 : InterferingWorkload Job)
  (j : Equality.sort Job) (t1 t2 : instant) =>
is_true (t1 <= @job_arrival Job H0 j < t2) /\
is_true (@quiet_time Job H0 H1 PState sched H2 H3 j t1) /\
(forall t : nat, is_true (t1 < t < t2) -> ~ is_true (@quiet_time Job H0 H1 PState sched H2 H3 j t))
     : forall {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       @schedule Job PState ->
       Interference Job -> InterferingWorkload Job -> Equality.sort Job -> instant -> instant -> Prop

Arguments busy_interval_prefix {Job H0 H1 PState} sched {H2 H3} j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Abstract.Definitions.busy_interval_prefix : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              Prosa.Behavior.Schedule.schedule PState →
                Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop
def Prosa.Analysis.Abstract.Definitions.busy_interval_prefix.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              Prosa.Behavior.Schedule.schedule PState →
                Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Analysis.Abstract.Definitions.Interference Job]
    [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Job.JobCost Job] {PState} sched j t1 t2 =>
  (t1 ≤ Prosa.Behavior.Job.job_arrival j ∧ Prosa.Behavior.Job.job_arrival j < t2) ∧
    Prosa.Analysis.Abstract.Definitions.quiet_time sched j t1 = true ∧
      ∀ (t : Prosa.Behavior.Time.instant),
        t1 < t ∧ t < t2 → ¬Prosa.Analysis.Abstract.Definitions.quiet_time sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_busy_interval_prefix
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp
```

Body:

```coq
Prosa_Analysis_Abstract_Definitions_busy_interval_prefix@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                                Job
                                                                                inst_3)
  (inst_9 : Prosa_Analysis_Abstract_Definitions_InterferingWorkload
                                                                                Job
                                                                                inst_3)
  (inst_12 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (inst_15 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
And
  (And
     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_12 j))
     (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_12 j)
        t2))
  (And
     (@eq Bool
        (Prosa_Analysis_Abstract_Definitions_quiet_time Job
           inst_3
           inst_6
           inst_9
           inst_12
           inst_15 PState sched j t1)
        Bool_true)
     (forall t : Prosa_Behavior_Time_instant,
      And (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t)
        (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t t2) ->
      Not
        (@eq Bool
           (Prosa_Analysis_Abstract_Definitions_quiet_time Job
              inst_3
              inst_6
              inst_9
              inst_12
              inst_15 PState sched j t)
           Bool_true)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp

Arguments Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15 PState 
  sched j t1 t2
```
