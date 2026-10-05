# `moved_later_implies_deadline_met`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.swaps.moved_later_implies_deadline_met`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.moved_later_implies_deadline_met`
- Certificate: `moved_later_implies_deadline_met_correspondence`

## Official Rocq

```coq
moved_later_implies_deadline_met :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState) (t1 t2 : instant),
is_true (t1 <= t2) ->
(forall j1 j2 : Equality.sort Job,
 is_true (@scheduled_at Job PState sched j1 t1) ->
 is_true (@scheduled_at Job PState sched j2 t2) ->
 is_true (@job_deadline Job H0 j2 <= @job_deadline Job H0 j1)) ->
(forall j1 : Equality.sort Job,
 is_true (@scheduled_at Job PState sched j1 t1) ->
 exists j2 : Equality.sort Job,
   is_true (@scheduled_at Job PState sched j2 t2) /\ is_true (t2 < @job_deadline Job H0 j2)) ->
forall j : Equality.sort Job,
is_true (@job_meets_deadline Job PState sched H H0 j) ->
is_true (@scheduled_at Job PState sched j t1) ->
is_true (@job_meets_deadline Job PState (@swapped Job PState sched t1 t2) H H0 j)

moved_later_implies_deadline_met is not universe polymorphic
Arguments moved_later_implies_deadline_met {Job H H0 PState} sched t1 t2 H_well_ordered
  (H_not_EDF H_no_idle_time_at_t2)%function_scope j H_deadline_met _
moved_later_implies_deadline_met is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.moved_later_implies_deadline_met
Declared in library prosa.analysis.facts.transform.swaps, line 430, characters 10-42
@moved_later_implies_deadline_met
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState) (t1 t2 : instant),
       is_true (t1 <= t2) ->
       (forall j1 j2 : Equality.sort Job,
        is_true (@scheduled_at Job PState sched j1 t1) ->
        is_true (@scheduled_at Job PState sched j2 t2) ->
        is_true (@job_deadline Job H0 j2 <= @job_deadline Job H0 j1)) ->
       (forall j1 : Equality.sort Job,
        is_true (@scheduled_at Job PState sched j1 t1) ->
        exists j2 : Equality.sort Job,
          is_true (@scheduled_at Job PState sched j2 t2) /\ is_true (t2 < @job_deadline Job H0 j2)) ->
       forall j : Equality.sort Job,
       is_true (@job_meets_deadline Job PState sched H H0 j) ->
       is_true (@scheduled_at Job PState sched j t1) ->
       is_true (@job_meets_deadline Job PState (@swapped Job PState sched t1 t2) H H0 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.moved_later_implies_deadline_met : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
  (t1 t2 : Prosa.Behavior.Time.instant),
  t1 ≤ t2 →
    (∀ (j1 j2 : Job),
        Prosa.Behavior.Service.scheduled_at sched j1 t1 = true →
          Prosa.Behavior.Service.scheduled_at sched j2 t2 = true →
            Prosa.Behavior.Job.job_deadline j2 ≤ Prosa.Behavior.Job.job_deadline j1) →
      (∀ (j1 : Job),
          Prosa.Behavior.Service.scheduled_at sched j1 t1 = true →
            ∃ j2, Prosa.Behavior.Service.scheduled_at sched j2 t2 = true ∧ t2 < Prosa.Behavior.Job.job_deadline j2) →
        ∀ (j : Job),
          Prosa.Behavior.Service.job_meets_deadline sched j = true →
            Prosa.Behavior.Service.scheduled_at sched j t1 = true →
              Prosa.Behavior.Service.job_meets_deadline (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_moved_later_implies_deadline_met
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
         (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       (forall j1 j2 : Job,
        @eq Bool
          (Prosa_Behavior_Service_scheduled_at Job
             inst_3 PState sched j1 t1)
          Bool_true ->
        @eq Bool
          (Prosa_Behavior_Service_scheduled_at Job
             inst_3 PState sched j2 t2)
          Bool_true ->
        LE_le_inst1 Prosa_Behavior_Time_instant instLENat
          (Prosa_Behavior_Job_JobDeadline_job_deadline Job
             inst_3
             inst_9 j2)
          (Prosa_Behavior_Job_JobDeadline_job_deadline Job
             inst_3
             inst_9 j1)) ->
       (forall j1 : Job,
        @eq Bool
          (Prosa_Behavior_Service_scheduled_at Job
             inst_3 PState sched j1 t1)
          Bool_true ->
        Exists Job
          (fun j2 : Job =>
           And
             (@eq Bool
                (Prosa_Behavior_Service_scheduled_at Job
                   inst_3 PState sched j2
                   t2)
                Bool_true)
             (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t2
                (Prosa_Behavior_Job_JobDeadline_job_deadline Job
                   inst_3
                   inst_9 j2)))) ->
       forall j : Job,
       @eq Bool
         (Prosa_Behavior_Service_job_meets_deadline Job
            inst_3 PState sched
            inst_6
            inst_9 j)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t1)
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
