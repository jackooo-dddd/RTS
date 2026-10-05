# `valid_schedule_implies_completed_jobs_dont_execute`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.completion.valid_schedule_implies_completed_jobs_dont_execute`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.valid_schedule_implies_completed_jobs_dont_execute`
- Certificate: `valid_schedule_implies_completed_jobs_dont_execute_correspondence`

## Official Rocq

```coq
valid_schedule_implies_completed_jobs_dont_execute :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  {H : JobCost Job} {H0 : JobArrival Job} {jr : @JobReady Job PState H H0} (arr_seq : arrival_sequence Job),
@valid_schedule Job H0 PState sched H jr arr_seq -> @completed_jobs_dont_execute Job PState sched H

valid_schedule_implies_completed_jobs_dont_execute is not universe polymorphic
Arguments valid_schedule_implies_completed_jobs_dont_execute {Job PState} sched {H H0 jr} arr_seq _ j t _
valid_schedule_implies_completed_jobs_dont_execute is opaque
Expands to: Constant
            prosa.analysis.facts.behavior.completion.valid_schedule_implies_completed_jobs_dont_execute
Declared in library prosa.analysis.facts.behavior.completion, line 370, characters 12-62
@valid_schedule_implies_completed_jobs_dont_execute
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (H : JobCost Job) (H0 : JobArrival Job) (jr : @JobReady Job PState H H0)
         (arr_seq : arrival_sequence Job),
       @valid_schedule Job H0 PState sched H jr arr_seq -> @completed_jobs_dont_execute Job PState sched H
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.valid_schedule_implies_completed_jobs_dont_execute : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobArrival Job] [jr : Prosa.Behavior.Ready.JobReady Job PState]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Ready.valid_schedule sched arr_seq → Prosa.Behavior.Ready.completed_jobs_dont_execute sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_valid_schedule_implies_completed_jobs_dont_execute
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
                 inst_13)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_13 PState sched
         inst_10 jr arr_seq ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_10
```
