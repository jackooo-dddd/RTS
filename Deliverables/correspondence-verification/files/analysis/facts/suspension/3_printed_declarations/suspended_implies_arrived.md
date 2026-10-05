# `suspended_implies_arrived`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.suspension.suspended_implies_arrived`
- Lean: `Prosa.Analysis.Facts.Suspension.suspended_implies_arrived`
- Certificate: `suspended_implies_arrived_correspondence`

## Official Rocq

```coq
suspended_implies_arrived :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobSuspension Job}
  {PState : ProcessorState Job} (sched : @schedule Job PState) (j : Equality.sort Job) 
  (t : instant),
is_true (@suspended Job PState H H0 H1 sched j t) -> is_true (@has_arrived Job H j t)

suspended_implies_arrived is not universe polymorphic
Arguments suspended_implies_arrived {Job H H0 H1 PState} sched j t _
suspended_implies_arrived is opaque
Expands to: Constant prosa.analysis.facts.suspension.suspended_implies_arrived
Declared in library prosa.analysis.facts.suspension, line 56, characters 8-33
@suspended_implies_arrived
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobSuspension Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (j : Equality.sort Job) 
         (t : instant),
       is_true (@suspended Job PState H H0 H1 sched j t) -> is_true (@has_arrived Job H j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Suspension.suspended_implies_arrived : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Model.Readiness.Suspension.JobSuspension Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Readiness.Suspension.suspended sched j t = true → Prosa.Behavior.Arrival_sequence.has_arrived j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Suspension_suspended_implies_arrived
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job inst_3)
         (inst_12 : 
          Prosa_Model_Readiness_Suspension_JobSuspension Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Readiness_Suspension_suspended Job
            inst_3 PState
            inst_6
            inst_9
            inst_12 sched j t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_has_arrived Job
            inst_3
            inst_6 j t)
         Bool_true
```
