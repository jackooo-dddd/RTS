# `completed_jobs_are_not_ready`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.completed_jobs_are_not_ready`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.completed_jobs_are_not_ready`
- Certificate: `completed_jobs_are_not_ready_correspondence`

## Official Rocq

```coq
completed_jobs_are_not_ready :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  {H : JobCost Job} {H0 : JobArrival Job} {jr : @JobReady Job PState H H0},
@jobs_must_be_ready_to_execute Job H0 PState sched H jr -> @completed_jobs_dont_execute Job PState sched H

completed_jobs_are_not_ready is not universe polymorphic
Arguments completed_jobs_are_not_ready {Job PState} sched {H H0 jr} _ j t _
completed_jobs_are_not_ready is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.completed_jobs_are_not_ready
Declared in library prosa.analysis.facts.behavior.completion, line 361, characters 8-36
@completed_jobs_are_not_ready
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (H : JobCost Job) (H0 : JobArrival Job) (jr : @JobReady Job PState H H0),
       @jobs_must_be_ready_to_execute Job H0 PState sched H jr ->
       @completed_jobs_dont_execute Job PState sched H
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.completed_jobs_are_not_ready : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobArrival Job] [jr : Prosa.Behavior.Ready.JobReady Job PState],
  Prosa.Behavior.Ready.jobs_must_be_ready_to_execute sched → Prosa.Behavior.Ready.completed_jobs_dont_execute sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_completed_jobs_are_not_ready
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
         (jr : Prosa_Behavior_Ready_JobReady Job
                 inst_3 PState
                 inst_10
                 inst_13),
       Prosa_Behavior_Ready_jobs_must_be_ready_to_execute Job
         inst_3
         inst_13 PState sched
         inst_10 jr ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_10
```
