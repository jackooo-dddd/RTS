# `ready_implies_incomplete`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.ready_implies_incomplete`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.ready_implies_incomplete`
- Certificate: `ready_implies_incomplete_correspondence`

## Official Rocq

```coq
ready_implies_incomplete :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  {H : JobCost Job} {H0 : JobArrival Job} {jr : @JobReady Job PState H H0} (j : Equality.sort Job)
  (t : instant),
is_true (@job_ready Job PState H H0 jr sched j t) -> is_true (~~ @completed_by Job PState sched H j t)

ready_implies_incomplete is not universe polymorphic
Arguments ready_implies_incomplete {Job PState} sched {H H0 jr} j t _
ready_implies_incomplete is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.ready_implies_incomplete
Declared in library prosa.analysis.facts.behavior.completion, line 356, characters 8-32
@ready_implies_incomplete
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (H : JobCost Job) (H0 : JobArrival Job) (jr : @JobReady Job PState H H0) 
         (j : Equality.sort Job) (t : instant),
       is_true (@job_ready Job PState H H0 jr sched j t) -> is_true (~~ @completed_by Job PState sched H j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.ready_implies_incomplete : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobArrival Job] [jr : Prosa.Behavior.Ready.JobReady Job PState] (j : Job)
  (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Ready.job_ready sched j t = true → (!Prosa.Behavior.Service.completed_by sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_ready_implies_incomplete
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
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Ready_JobReady_job_ready Job
            inst_3 PState
            inst_10
            inst_13 jr sched j t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3 PState sched
               inst_10 j t))
         Bool_true
```
