# `backlogged_job_arrives_in`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.readiness.backlogged.backlogged_job_arrives_in`
- Lean: `Prosa.Analysis.Facts.Readiness.Backlogged.backlogged_job_arrives_in`
- Certificate: `backlogged_job_arrives_in_correspondence`

## Official Rocq

```coq
backlogged_job_arrives_in :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job}
  {jr : @JobReady Job PState H H0} (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  (j : Equality.sort Job) (t : instant),
is_true (j \in @jobs_backlogged_at Job H0 H PState jr arr_seq sched t) -> @arrives_in Job arr_seq j

backlogged_job_arrives_in is not universe polymorphic
Arguments backlogged_job_arrives_in {Job H H0 PState jr} arr_seq sched j t _
backlogged_job_arrives_in is opaque
Expands to: Constant prosa.analysis.facts.readiness.backlogged.backlogged_job_arrives_in
Declared in library prosa.analysis.facts.readiness.backlogged, line 46, characters 8-33
@backlogged_job_arrives_in
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job)
         (jr : @JobReady Job PState H H0) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (j \in @jobs_backlogged_at Job H0 H PState jr arr_seq sched t) -> @arrives_in Job arr_seq j
```

## Lean

```lean
@Prosa.Analysis.Facts.Readiness.Backlogged.backlogged_job_arrives_in : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [jr : Prosa.Behavior.Ready.JobReady Job PState]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  (j : Job) (t : Prosa.Behavior.Time.instant),
  decide (j ∈ Prosa.Model.Schedule.WorkConserving.jobs_backlogged_at arr_seq sched t) = true →
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Readiness_Backlogged_backlogged_job_arrives_in
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
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
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
         Bool_true ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j
```
