# `incomplete_implies_scheduled_later`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.deadlines.incomplete_implies_scheduled_later`
- Lean: `Prosa.Analysis.Facts.Behavior.Deadlines.incomplete_implies_scheduled_later`
- Certificate: `incomplete_implies_scheduled_later_correspondence`

## Official Rocq

```coq
incomplete_implies_scheduled_later :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant),
is_true (@job_meets_deadline Job PState sched H H0 j) ->
is_true (~~ @completed_by Job PState sched H j t) ->
exists t' : nat, is_true (t <= t' < @job_deadline Job H0 j) /\ is_true (@scheduled_at Job PState sched j t')

incomplete_implies_scheduled_later is not universe polymorphic
Arguments incomplete_implies_scheduled_later {Job H H0 PState} sched j t _ _
incomplete_implies_scheduled_later is opaque
Expands to: Constant prosa.analysis.facts.behavior.deadlines.incomplete_implies_scheduled_later
Declared in library prosa.analysis.facts.behavior.deadlines, line 38, characters 10-44
@incomplete_implies_scheduled_later
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant),
       is_true (@job_meets_deadline Job PState sched H H0 j) ->
       is_true (~~ @completed_by Job PState sched H j t) ->
       exists t' : nat,
         is_true (t <= t' < @job_deadline Job H0 j) /\ is_true (@scheduled_at Job PState sched j t')
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Deadlines.incomplete_implies_scheduled_later : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.job_meets_deadline sched j = true →
    (!Prosa.Behavior.Service.completed_by sched j t) = true →
      ∃ t',
        (decide (t ≤ t') && decide (t' < Prosa.Behavior.Job.job_deadline j)) = true ∧
          Prosa.Behavior.Service.scheduled_at sched j t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Deadlines_incomplete_implies_scheduled_later
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_job_meets_deadline Job
            inst_3 PState sched
            inst_6
            inst_9 j)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3 PState sched
               inst_6 j t))
         Bool_true ->
       Exists Nat
         (fun t' : Nat =>
          And
            (@eq Bool
               (Bool_and
                  (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t t') (Nat_decLe t t'))
                  (Decidable_decide
                     (LT_lt_inst1 Nat instLTNat t'
                        (Prosa_Behavior_Job_JobDeadline_job_deadline Job
                           inst_3
                           inst_9 j))
                     (Nat_decLt t'
                        (Prosa_Behavior_Job_JobDeadline_job_deadline Job
                           inst_3
                           inst_9 j))))
               Bool_true)
            (@eq Bool
               (Prosa_Behavior_Service_scheduled_at Job
                  inst_3 PState sched j
                  t')
               Bool_true))
```
