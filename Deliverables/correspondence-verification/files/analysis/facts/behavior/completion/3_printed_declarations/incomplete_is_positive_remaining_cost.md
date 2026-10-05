# `incomplete_is_positive_remaining_cost`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.incomplete_is_positive_remaining_cost`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.incomplete_is_positive_remaining_cost`
- Certificate: `incomplete_is_positive_remaining_cost_correspondence`

## Official Rocq

```coq
incomplete_is_positive_remaining_cost :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (j : Equality.sort Job) (t : instant),
is_true (~~ @completed_by Job PState sched H j t) <-> is_true (0 < @remaining_cost Job PState sched H j t)

incomplete_is_positive_remaining_cost is not universe polymorphic
Arguments incomplete_is_positive_remaining_cost {Job H PState} sched j t
incomplete_is_positive_remaining_cost is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.incomplete_is_positive_remaining_cost
Declared in library prosa.analysis.facts.behavior.completion, line 51, characters 8-45
@incomplete_is_positive_remaining_cost
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t : instant),
       is_true (~~ @completed_by Job PState sched H j t) <->
       is_true (0 < @remaining_cost Job PState sched H j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.incomplete_is_positive_remaining_cost : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (t : Prosa.Behavior.Time.instant),
  (!Prosa.Behavior.Service.completed_by sched j t) = true ↔ 0 < Prosa.Behavior.Service.remaining_cost sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_incomplete_is_positive_remaining_cost
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
       Iff
         (@eq Bool
            (Bool_not
               (Prosa_Behavior_Service_completed_by Job
                  inst_3 PState sched
                  inst_6 j t))
            Bool_true)
         (LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
            (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
            (Prosa_Behavior_Service_remaining_cost Job
               inst_3 PState sched
               inst_6 j t))
```
