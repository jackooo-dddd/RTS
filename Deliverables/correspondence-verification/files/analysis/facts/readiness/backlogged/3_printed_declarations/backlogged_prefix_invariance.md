# `backlogged_prefix_invariance`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.readiness.backlogged.backlogged_prefix_invariance`
- Lean: `Prosa.Analysis.Facts.Readiness.Backlogged.backlogged_prefix_invariance`
- Certificate: `backlogged_prefix_invariance_correspondence`

## Official Rocq

```coq
backlogged_prefix_invariance :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job}
  {RM : @JobReady Job PState H H0},
@nonclairvoyant_readiness Job H H0 PState RM ->
forall (sched sched' : @schedule Job PState) (h : instant),
@identical_prefix Job PState sched sched' h ->
forall (t : nat) (j : Equality.sort Job),
is_true (t < h) -> @backlogged Job PState H H0 RM sched j t = @backlogged Job PState H H0 RM sched' j t

backlogged_prefix_invariance is not universe polymorphic
Arguments backlogged_prefix_invariance {Job H H0 PState RM} H_nonclairvoyant_job_readiness 
  sched sched' h H_shared_prefix t%nat_scope j _
backlogged_prefix_invariance is opaque
Expands to: Constant prosa.analysis.facts.readiness.backlogged.backlogged_prefix_invariance
Declared in library prosa.analysis.facts.readiness.backlogged, line 87, characters 8-36
@backlogged_prefix_invariance
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job)
         (RM : @JobReady Job PState H H0),
       @nonclairvoyant_readiness Job H H0 PState RM ->
       forall (sched sched' : @schedule Job PState) (h : instant),
       @identical_prefix Job PState sched sched' h ->
       forall (t : nat) (j : Equality.sort Job),
       is_true (t < h) ->
       @backlogged Job PState H H0 RM sched j t = @backlogged Job PState H H0 RM sched' j t
```

## Lean

```lean
@Prosa.Analysis.Facts.Readiness.Backlogged.backlogged_prefix_invariance : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [RM : Prosa.Behavior.Ready.JobReady Job PState],
  Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness RM →
    ∀ (sched sched' : Prosa.Behavior.Schedule.schedule PState) (h : Prosa.Behavior.Time.instant),
      Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix sched sched' h →
        ∀ (t : ℕ) (j : Job),
          t < h → Prosa.Behavior.Ready.backlogged sched j t = Prosa.Behavior.Ready.backlogged sched' j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Readiness_Backlogged_backlogged_prefix_invariance
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (RM : Prosa_Behavior_Ready_JobReady Job
                 inst_3 PState
                 inst_6
                 inst_9),
       Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness Job
         inst_3
         inst_6
         inst_9 PState RM ->
       forall
         (sched
          sched' : Prosa_Behavior_Schedule_schedule Job
                     inst_3 PState)
         (h : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix Job
         inst_3 PState sched sched' h ->
       forall (t : Nat) (j : Job),
       LT_lt_inst1 Nat instLTNat t h ->
       @eq Bool
         (Prosa_Behavior_Ready_backlogged Job
            inst_3 PState
            inst_6
            inst_9 RM sched j t)
         (Prosa_Behavior_Ready_backlogged Job
            inst_3 PState
            inst_6
            inst_9 RM sched' j t)
```
