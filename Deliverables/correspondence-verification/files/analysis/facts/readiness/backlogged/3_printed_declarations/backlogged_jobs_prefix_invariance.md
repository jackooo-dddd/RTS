# `backlogged_jobs_prefix_invariance`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.readiness.backlogged.backlogged_jobs_prefix_invariance`
- Lean: `Prosa.Analysis.Facts.Readiness.Backlogged.backlogged_jobs_prefix_invariance`
- Certificate: `backlogged_jobs_prefix_invariance_correspondence`

## Official Rocq

```coq
backlogged_jobs_prefix_invariance :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job}
  {RM : @JobReady Job PState H H0},
@nonclairvoyant_readiness Job H H0 PState RM ->
forall (arr_seq : arrival_sequence Job) (sched sched' : @schedule Job PState) (h : instant),
@identical_prefix Job PState sched sched' h ->
forall t : nat,
is_true (t < h) ->
@jobs_backlogged_at Job H0 H PState RM arr_seq sched t =
@jobs_backlogged_at Job H0 H PState RM arr_seq sched' t

backlogged_jobs_prefix_invariance is not universe polymorphic
Arguments backlogged_jobs_prefix_invariance {Job H H0 PState RM} H_nonclairvoyant_job_readiness 
  arr_seq sched sched' h H_shared_prefix t%nat_scope _
backlogged_jobs_prefix_invariance is opaque
Expands to: Constant prosa.analysis.facts.readiness.backlogged.backlogged_jobs_prefix_invariance
Declared in library prosa.analysis.facts.readiness.backlogged, line 117, characters 8-41
@backlogged_jobs_prefix_invariance
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job)
         (RM : @JobReady Job PState H H0),
       @nonclairvoyant_readiness Job H H0 PState RM ->
       forall (arr_seq : arrival_sequence Job) (sched sched' : @schedule Job PState) (h : instant),
       @identical_prefix Job PState sched sched' h ->
       forall t : nat,
       is_true (t < h) ->
       @jobs_backlogged_at Job H0 H PState RM arr_seq sched t =
       @jobs_backlogged_at Job H0 H PState RM arr_seq sched' t
```

## Lean

```lean
@Prosa.Analysis.Facts.Readiness.Backlogged.backlogged_jobs_prefix_invariance : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [RM : Prosa.Behavior.Ready.JobReady Job PState],
  Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness RM →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
      (sched sched' : Prosa.Behavior.Schedule.schedule PState) (h : Prosa.Behavior.Time.instant),
      Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix sched sched' h →
        ∀ t < h,
          Prosa.Model.Schedule.WorkConserving.jobs_backlogged_at arr_seq sched t =
            Prosa.Model.Schedule.WorkConserving.jobs_backlogged_at arr_seq sched' t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Readiness_Backlogged_backlogged_jobs_prefix_invariance
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
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched
          sched' : Prosa_Behavior_Schedule_schedule Job
                     inst_3 PState)
         (h : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix Job
         inst_3 PState sched sched' h ->
       forall t : Nat,
       LT_lt_inst1 Nat instLTNat t h ->
       @eq (List Job)
         (Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at Job
            inst_3
            inst_9
            inst_6 PState RM arr_seq
            sched t)
         (Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at Job
            inst_3
            inst_9
            inst_6 PState RM arr_seq
            sched' t)
```
