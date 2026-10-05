# `job_pending_at_arrival`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.job_pending_at_arrival`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.job_pending_at_arrival`
- Certificate: `job_pending_at_arrival_correspondence`

## Official Rocq

```coq
job_pending_at_arrival :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState) (j : Equality.sort Job),
is_true (0 < @job_cost Job H j) ->
@jobs_must_arrive_to_execute Job H0 PState sched ->
is_true (@pending Job PState sched H H0 j (@job_arrival Job H0 j))

job_pending_at_arrival is not universe polymorphic
Arguments job_pending_at_arrival {Job H H0 PState} sched j H_positive_cost H_jobs_must_arrive
job_pending_at_arrival is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.job_pending_at_arrival
Declared in library prosa.analysis.facts.behavior.completion, line 332, characters 8-30
@job_pending_at_arrival
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState) (j : Equality.sort Job),
       is_true (0 < @job_cost Job H j) ->
       @jobs_must_arrive_to_execute Job H0 PState sched ->
       is_true (@pending Job PState sched H H0 j (@job_arrival Job H0 j))
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.job_pending_at_arrival : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job),
  0 < Prosa.Behavior.Job.job_cost j →
    Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
      Prosa.Behavior.Service.pending sched j (Prosa.Behavior.Job.job_arrival j) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_job_pending_at_arrival
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
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job),
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6 j) ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_9 PState sched ->
       @eq Bool
         (Prosa_Behavior_Service_pending Job
            inst_3 PState sched
            inst_6
            inst_9 j
            (Prosa_Behavior_Job_JobArrival_job_arrival Job
               inst_3
               inst_9 j))
         Bool_true
```
