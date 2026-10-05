# `incomplete_implies_positive_cost`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.completion.incomplete_implies_positive_cost`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.incomplete_implies_positive_cost`
- Certificate: `incomplete_implies_positive_cost_correspondence`

## Official Rocq

```coq
incomplete_implies_positive_cost :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (j : Equality.sort Job) (t : instant),
is_true (~~ @completed_by Job PState sched H j t) -> is_true (@job_cost_positive Job H j)

incomplete_implies_positive_cost is not universe polymorphic
Arguments incomplete_implies_positive_cost {Job H PState} sched j t _
incomplete_implies_positive_cost is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.incomplete_implies_positive_cost
Declared in library prosa.analysis.facts.behavior.completion, line 60, characters 12-44
@incomplete_implies_positive_cost
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (~~ @completed_by Job PState sched H j t) -> is_true (@job_cost_positive Job H j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.incomplete_implies_positive_cost : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (t : Prosa.Behavior.Time.instant),
  (!Prosa.Behavior.Service.completed_by sched j t) = true → Prosa.Model.Job.Properties.job_cost_positive j = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_incomplete_implies_positive_cost
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3 PState sched
               inst_6 j t))
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_6 j)
         Bool_true
```
