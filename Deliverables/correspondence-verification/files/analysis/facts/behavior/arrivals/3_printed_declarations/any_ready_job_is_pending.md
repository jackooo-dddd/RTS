# `any_ready_job_is_pending`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.any_ready_job_is_pending`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.any_ready_job_is_pending`
- Certificate: `any_ready_job_is_pending_correspondence`

## Official Rocq

```coq
any_ready_job_is_pending :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  {H : JobCost Job} {H0 : JobArrival Job} {jr : @JobReady Job PState H H0} (j : Equality.sort Job)
  (t : instant),
is_true (@job_ready Job PState H H0 jr sched j t) -> is_true (@pending Job PState sched H H0 j t)

any_ready_job_is_pending is not universe polymorphic
Arguments any_ready_job_is_pending {Job PState} sched {H H0 jr} j t _
any_ready_job_is_pending is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.any_ready_job_is_pending
Declared in library prosa.analysis.facts.behavior.arrivals, line 62, characters 8-32
@any_ready_job_is_pending
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (H : JobCost Job) (H0 : JobArrival Job) (jr : @JobReady Job PState H H0) 
         (j : Equality.sort Job) (t : instant),
       is_true (@job_ready Job PState H H0 jr sched j t) -> is_true (@pending Job PState sched H H0 j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.any_ready_job_is_pending : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobArrival Job] [inst_3 : Prosa.Behavior.Ready.JobReady Job PState] (j : Job)
  (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Ready.job_ready sched j t = true → Prosa.Behavior.Service.pending sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_any_ready_job_is_pending
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (inst_10 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_13 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_16 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_10
            inst_13)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Ready_JobReady_job_ready Job
            inst_3 PState
            inst_10
            inst_13
            inst_16 sched j t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_pending Job
            inst_3 PState sched
            inst_10
            inst_13 j t)
         Bool_true
```
