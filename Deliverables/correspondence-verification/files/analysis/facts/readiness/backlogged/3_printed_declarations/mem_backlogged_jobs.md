# `mem_backlogged_jobs`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.readiness.backlogged.mem_backlogged_jobs`
- Lean: `Prosa.Analysis.Facts.Readiness.Backlogged.mem_backlogged_jobs`
- Certificate: `mem_backlogged_jobs_correspondence`

## Official Rocq

```coq
mem_backlogged_jobs :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job}
  {jr : @JobReady Job PState H H0} (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
@consistent_arrival_times Job H0 arr_seq ->
forall (j : Equality.sort Job) (t : instant),
@arrives_in Job arr_seq j ->
is_true (@backlogged Job PState H H0 jr sched j t) ->
is_true (j \in @jobs_backlogged_at Job H0 H PState jr arr_seq sched t)

mem_backlogged_jobs is not universe polymorphic
Arguments mem_backlogged_jobs {Job H H0 PState jr} arr_seq sched H_consistent_arrival_times j t _ _
mem_backlogged_jobs is opaque
Expands to: Constant prosa.analysis.facts.readiness.backlogged.mem_backlogged_jobs
Declared in library prosa.analysis.facts.readiness.backlogged, line 27, characters 8-27
@mem_backlogged_jobs
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job)
         (jr : @JobReady Job PState H H0) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
       @consistent_arrival_times Job H0 arr_seq ->
       forall (j : Equality.sort Job) (t : instant),
       @arrives_in Job arr_seq j ->
       is_true (@backlogged Job PState H H0 jr sched j t) ->
       is_true (j \in @jobs_backlogged_at Job H0 H PState jr arr_seq sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Readiness.Backlogged.mem_backlogged_jobs : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [jr : Prosa.Behavior.Ready.JobReady Job PState]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Behavior.Ready.backlogged sched j t = true →
          decide (j ∈ Prosa.Model.Schedule.WorkConserving.jobs_backlogged_at arr_seq sched t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Readiness_Backlogged_mem_backlogged_jobs
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
         (jr : Prosa_Behavior_Ready_JobReady Job
                 inst_3 PState
                 inst_6
                 inst_9)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_3
         inst_9 arr_seq ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Behavior_Ready_backlogged Job
            inst_3 PState
            inst_6
            inst_9 jr sched j t)
         Bool_true ->
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at Job
                  inst_3
                  inst_9
                  inst_6 PState jr
                  arr_seq sched t)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job
                  inst_3)
               j
               (Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at Job
                  inst_3
                  inst_9
                  inst_6 PState jr
                  arr_seq sched t)))
         Bool_true
```
