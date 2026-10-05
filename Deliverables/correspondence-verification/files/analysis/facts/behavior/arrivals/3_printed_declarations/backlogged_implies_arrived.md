# `backlogged_implies_arrived`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.arrivals.backlogged_implies_arrived`
- Lean: `Prosa.Analysis.Facts.Behavior.Arrivals.backlogged_implies_arrived`
- Certificate: `backlogged_implies_arrived_correspondence`

## Official Rocq

```coq
backlogged_implies_arrived :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  {H : JobCost Job} {H0 : JobArrival Job} {jr : @JobReady Job PState H H0} (j : Equality.sort Job)
  (t : instant),
is_true (@backlogged Job PState H H0 jr sched j t) -> is_true (@has_arrived Job H0 j t)

backlogged_implies_arrived is not universe polymorphic
Arguments backlogged_implies_arrived {Job PState} sched {H H0 jr} j t _
backlogged_implies_arrived is opaque
Expands to: Constant prosa.analysis.facts.behavior.arrivals.backlogged_implies_arrived
Declared in library prosa.analysis.facts.behavior.arrivals, line 84, characters 12-38
@backlogged_implies_arrived
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (H : JobCost Job) (H0 : JobArrival Job) (jr : @JobReady Job PState H H0) 
         (j : Equality.sort Job) (t : instant),
       is_true (@backlogged Job PState H H0 jr sched j t) -> is_true (@has_arrived Job H0 j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Arrivals.backlogged_implies_arrived : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobArrival Job] [inst_3 : Prosa.Behavior.Ready.JobReady Job PState] (j : Job)
  (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Ready.backlogged sched j t = true → Prosa.Behavior.Arrival_sequence.has_arrived j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Arrivals_backlogged_implies_arrived
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
         (Prosa_Behavior_Ready_backlogged Job
            inst_3 PState
            inst_10
            inst_13
            inst_16 sched j t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_has_arrived Job
            inst_3
            inst_13 j t)
         Bool_true
```
