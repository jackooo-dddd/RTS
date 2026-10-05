# `jobs_must_arrive_to_be_ready`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.arrivals.jobs_must_arrive_to_be_ready`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.jobs_must_arrive_to_be_ready`
- Certificate: `jobs_must_arrive_to_be_ready_correspondence`

## Official Rocq

```coq
jobs_must_arrive_to_be_ready :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  {H : JobCost Job} {H0 : JobArrival Job} {jr : @JobReady Job PState H H0},
@jobs_must_be_ready_to_execute Job H0 PState sched H jr -> @jobs_must_arrive_to_execute Job H0 PState sched

jobs_must_arrive_to_be_ready is not universe polymorphic
Arguments jobs_must_arrive_to_be_ready {Job PState} sched {H H0 jr} _ j t _
jobs_must_arrive_to_be_ready is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.jobs_must_arrive_to_be_ready
Declared in library prosa.analysis.facts.behavior.arrivals, line 73, characters 8-36
@jobs_must_arrive_to_be_ready
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (H : JobCost Job) (H0 : JobArrival Job) (jr : @JobReady Job PState H H0),
       @jobs_must_be_ready_to_execute Job H0 PState sched H jr ->
       @jobs_must_arrive_to_execute Job H0 PState sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.jobs_must_arrive_to_be_ready : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobArrival Job] [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
  Prosa.Behavior.Ready.jobs_must_be_ready_to_execute sched → Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_jobs_must_arrive_to_be_ready
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
            inst_13),
       Prosa_Behavior_Ready_jobs_must_be_ready_to_execute Job
         inst_3
         inst_13 PState sched
         inst_10
         inst_16 ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_13 PState sched
```
