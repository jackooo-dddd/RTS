# `moved_earlier_implies_deadline_met`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.swaps.moved_earlier_implies_deadline_met`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.moved_earlier_implies_deadline_met`
- Certificate: `moved_earlier_implies_deadline_met_correspondence`

## Official Rocq

```coq
moved_earlier_implies_deadline_met :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState),
@completed_jobs_dont_execute Job PState sched H ->
forall t1 t2 : instant,
is_true (t1 <= t2) ->
forall j : Equality.sort Job,
is_true (@job_meets_deadline Job PState sched H H0 j) ->
is_true (@scheduled_at Job PState sched j t2) ->
is_true (@job_meets_deadline Job PState (@swapped Job PState sched t1 t2) H H0 j)

moved_earlier_implies_deadline_met is not universe polymorphic
Arguments moved_earlier_implies_deadline_met {Job H H0 PState} sched H_completed_jobs 
  t1 t2 H_well_ordered j H_deadline_met _
moved_earlier_implies_deadline_met is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.moved_earlier_implies_deadline_met
Declared in library prosa.analysis.facts.transform.swaps, line 418, characters 10-44
@moved_earlier_implies_deadline_met
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState),
       @completed_jobs_dont_execute Job PState sched H ->
       forall t1 t2 : instant,
       is_true (t1 <= t2) ->
       forall j : Equality.sort Job,
       is_true (@job_meets_deadline Job PState sched H H0 j) ->
       is_true (@scheduled_at Job PState sched j t2) ->
       is_true (@job_meets_deadline Job PState (@swapped Job PState sched t1 t2) H H0 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.moved_earlier_implies_deadline_met : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
    ∀ (t1 t2 : Prosa.Behavior.Time.instant),
      t1 ≤ t2 →
        ∀ (j : Job),
          Prosa.Behavior.Service.job_meets_deadline sched j = true →
            Prosa.Behavior.Service.scheduled_at sched j t2 = true →
              Prosa.Behavior.Service.job_meets_deadline (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_moved_earlier_implies_deadline_met
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
                    inst_3 PState),
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_6 ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       forall j : Job,
       @eq Bool
         (Prosa_Behavior_Service_job_meets_deadline Job
            inst_3 PState sched
            inst_6
            inst_9 j)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t2)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_job_meets_deadline Job
            inst_3 PState
            (Prosa_Analysis_Transform_Swap_swapped Job
               inst_3 PState sched t1 t2)
            inst_6
            inst_9 j)
         Bool_true
```
