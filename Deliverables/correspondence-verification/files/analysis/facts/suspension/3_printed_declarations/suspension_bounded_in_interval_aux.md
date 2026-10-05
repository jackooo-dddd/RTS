# `suspension_bounded_in_interval_aux`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.suspension.suspension_bounded_in_interval_aux`
- Lean: `Prosa.Analysis.Facts.Suspension.suspension_bounded_in_interval_aux`
- Certificate: `suspension_bounded_in_interval_aux_correspondence`

## Official Rocq

```coq
suspension_bounded_in_interval_aux :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobSuspension Job}
  {PState : ProcessorState Job} (sched : @schedule Job PState) (j : Equality.sort Job) 
  (t1 t2 : instant) (ρ : work) (tf : instant),
is_true (t1 <= tf < t2) ->
is_true (@suspended Job PState H H0 H1 sched j tf) ->
@service Job PState sched j tf = ρ ->
(forall to : nat,
 is_true (t1 <= to < tf) ->
 is_true (~~ (@suspended Job PState H H0 H1 sched j to && (@service Job PState sched j to == ρ)))) ->
is_true
  (\sum_(t1 <= t < t2 | @service Job PState sched j t == ρ)
      nat_of_bool (@suspended Job PState H H0 H1 sched j t) <=
   @job_suspension Job H1 j ρ)

suspension_bounded_in_interval_aux is not universe polymorphic
Arguments suspension_bounded_in_interval_aux {Job H H0 H1 PState} sched j t1 t2 ρ 
  tf INtf H_suspended_tf H_service_at_tf H_before_tf%function_scope
suspension_bounded_in_interval_aux is opaque
Expands to: Constant prosa.analysis.facts.suspension.suspension_bounded_in_interval_aux
Declared in library prosa.analysis.facts.suspension, line 203, characters 12-46
@suspension_bounded_in_interval_aux
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobSuspension Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (j : Equality.sort Job)
         (t1 t2 : instant) (ρ : work) (tf : instant),
       is_true (t1 <= tf < t2) ->
       is_true (@suspended Job PState H H0 H1 sched j tf) ->
       @service Job PState sched j tf = ρ ->
       (forall to : nat,
        is_true (t1 <= to < tf) ->
        is_true (~~ (@suspended Job PState H H0 H1 sched j to && (@service Job PState sched j to == ρ)))) ->
       is_true
         (\sum_(t1 <= t < t2 | @service Job PState sched j t == ρ)
             nat_of_bool (@suspended Job PState H H0 H1 sched j t) <=
          @job_suspension Job H1 j ρ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Suspension.suspension_bounded_in_interval_aux : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Model.Readiness.Suspension.JobSuspension Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant)
  (ρ : Prosa.Behavior.Job.work) (tf : Prosa.Behavior.Time.instant),
  (decide (t1 ≤ tf) && decide (tf < t2)) = true →
    Prosa.Model.Readiness.Suspension.suspended sched j tf = true →
      Prosa.Behavior.Service.service sched j tf = ρ →
        (∀ (t0 : ℕ),
            (decide (t1 ≤ t0) && decide (t0 < tf)) = true →
              (!(Prosa.Model.Readiness.Suspension.suspended sched j t0 &&
                    decide (Prosa.Behavior.Service.service sched j t0 = ρ))) =
                true) →
          (∑ t ∈ Finset.Ico t1 t2,
              if Prosa.Behavior.Service.service sched j t = ρ then
                (Prosa.Model.Readiness.Suspension.suspended sched j t).toNat
              else 0) ≤
            Prosa.Model.Readiness.Suspension.job_suspension j ρ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Suspension_suspension_bounded_in_interval_aux
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
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) (_UU03c1_ : Prosa_Behavior_Job_work)
         (tf : Prosa_Behavior_Time_instant),
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 tf) (Nat_decLe t1 tf))
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat tf t2) (Nat_decLt tf t2)))
         Bool_true ->
       @eq Bool
         (Prosa_Model_Readiness_Suspension_suspended Job
            inst_3 PState
            inst_6
            inst_9
            inst_12 sched j tf)
         Bool_true ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j tf)
         _UU03c1_ ->
       (forall t0 : Nat,
        @eq Bool
          (Bool_and
             (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t0) (Nat_decLe t1 t0))
             (Decidable_decide (LT_lt_inst1 Nat instLTNat t0 tf) (Nat_decLt t0 tf)))
          Bool_true ->
        @eq Bool
          (Bool_not
             (Bool_and
                (Prosa_Model_Readiness_Suspension_suspended Job
                   inst_3 PState
                   inst_6
                   inst_9
                   inst_12 sched j t0)
                (Decidable_decide
                   (@eq Prosa_Behavior_Job_work
                      (Prosa_Behavior_Service_service Job
                         inst_3 PState sched j
                         t0)
                      _UU03c1_)
                   (instDecidableEqNat
                      (Prosa_Behavior_Service_service Job
                         inst_3 PState sched j
                         t0)
                      _UU03c1_))))
          Bool_true) ->
       LE_le_inst1 Nat instLENat
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat
               (fun t : Nat =>
                ite Nat
                  (@eq Prosa_Behavior_Job_work
                     (Prosa_Behavior_Service_service Job
                        inst_3 PState sched j t)
                     _UU03c1_)
                  (instDecidableEqNat
                     (Prosa_Behavior_Service_service Job
                        inst_3 PState sched j t)
                     _UU03c1_)
                  (Bool_toNat
                     (Prosa_Model_Readiness_Suspension_suspended Job
                        inst_3 PState
                        inst_6
                        inst_9
                        inst_12 sched j t))
                  (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
               (List_range' t1 (Nat_sub t2 t1) 1)))
         (Prosa_Model_Readiness_Suspension_JobSuspension_job_suspension Job
            inst_3
            inst_12 j _UU03c1_)
```
