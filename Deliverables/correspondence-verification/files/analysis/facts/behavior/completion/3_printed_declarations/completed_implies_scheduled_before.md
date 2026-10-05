# `completed_implies_scheduled_before`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.completed_implies_scheduled_before`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.completed_implies_scheduled_before`
- Certificate: `completed_implies_scheduled_before_correspondence`

## Official Rocq

```coq
completed_implies_scheduled_before :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState) (j : Equality.sort Job),
is_true (0 < @job_cost Job H j) ->
@jobs_must_arrive_to_execute Job H0 PState sched ->
forall t : instant,
is_true (@completed_by Job PState sched H j t) ->
exists t' : nat, is_true (@job_arrival Job H0 j <= t' < t) /\ is_true (@scheduled_at Job PState sched j t')

completed_implies_scheduled_before is not universe polymorphic
Arguments completed_implies_scheduled_before {Job H H0 PState} sched j H_positive_cost H_jobs_must_arrive t _
completed_implies_scheduled_before is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.completed_implies_scheduled_before
Declared in library prosa.analysis.facts.behavior.completion, line 319, characters 8-42
@completed_implies_scheduled_before
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState) (j : Equality.sort Job),
       is_true (0 < @job_cost Job H j) ->
       @jobs_must_arrive_to_execute Job H0 PState sched ->
       forall t : instant,
       is_true (@completed_by Job PState sched H j t) ->
       exists t' : nat,
         is_true (@job_arrival Job H0 j <= t' < t) /\ is_true (@scheduled_at Job PState sched j t')
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.completed_implies_scheduled_before : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job),
  0 < Prosa.Behavior.Job.job_cost j →
    Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
      ∀ (t : Prosa.Behavior.Time.instant),
        Prosa.Behavior.Service.completed_by sched j t = true →
          ∃ t',
            (decide (Prosa.Behavior.Job.job_arrival j ≤ t') && decide (t' < t)) = true ∧
              Prosa.Behavior.Service.scheduled_at sched j t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_completed_implies_scheduled_before
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job),
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6 j) ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_9 PState sched ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Behavior_Service_completed_by Job
            inst_3 PState sched
            inst_6 j t)
         Bool_true ->
       Exists Nat
         (fun t' : Nat =>
          And
            (@eq Bool
               (Bool_and
                  (Decidable_decide
                     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_3
                           inst_9 j)
                        t')
                     (Nat_decLe
                        (Prosa_Behavior_Job_JobArrival_job_arrival Job
                           inst_3
                           inst_9 j)
                        t'))
                  (Decidable_decide (LT_lt_inst1 Nat instLTNat t' t) (Nat_decLt t' t)))
               Bool_true)
            (@eq Bool
               (Prosa_Behavior_Service_scheduled_at Job
                  inst_3 PState sched
                  j t')
               Bool_true))
```
