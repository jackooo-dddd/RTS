# `exists_some_point`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.suspension.exists_some_point`
- Lean: `Prosa.Analysis.Facts.Suspension.exists_some_point`
- Certificate: `exists_some_point_correspondence`

## Official Rocq

```coq
exists_some_point :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobSuspension Job}
  {PState : ProcessorState Job} (sched : @schedule Job PState) (j : Equality.sort Job) 
  (t1 t2 : instant) (ρ : work),
(exists2 t : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
   is_true (t \in index_iota t1 t2) &
   is_true (@suspended Job PState H H0 H1 sched j t && (@service Job PState sched j t == ρ))) ->
exists t' : nat,
  is_true (t1 <= t' < t2) /\
  is_true (@suspended Job PState H H0 H1 sched j t') /\
  @service Job PState sched j t' = ρ /\
  (forall to : nat,
   is_true (t1 <= to < t') ->
   is_true (~~ (@suspended Job PState H H0 H1 sched j to && (@service Job PState sched j to == ρ))))

exists_some_point is not universe polymorphic
Arguments exists_some_point {Job H H0 H1 PState} sched j t1 t2 ρ _
exists_some_point is opaque
Expands to: Constant prosa.analysis.facts.suspension.exists_some_point
Declared in library prosa.analysis.facts.suspension, line 221, characters 10-27
@exists_some_point
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobSuspension Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (j : Equality.sort Job)
         (t1 t2 : instant) (ρ : work),
       (exists2 t : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
          is_true (t \in index_iota t1 t2) &
          is_true (@suspended Job PState H H0 H1 sched j t && (@service Job PState sched j t == ρ))) ->
       exists t' : nat,
         is_true (t1 <= t' < t2) /\
         is_true (@suspended Job PState H H0 H1 sched j t') /\
         @service Job PState sched j t' = ρ /\
         (forall to : nat,
          is_true (t1 <= to < t') ->
          is_true (~~ (@suspended Job PState H H0 H1 sched j to && (@service Job PState sched j to == ρ))))
```

## Lean

```lean
@Prosa.Analysis.Facts.Suspension.exists_some_point : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Model.Readiness.Suspension.JobSuspension Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant)
  (ρ : Prosa.Behavior.Job.work),
  (∃ t,
      decide (t ∈ List.range' t1 (t2 - t1)) = true ∧
        (Prosa.Model.Readiness.Suspension.suspended sched j t &&
            decide (Prosa.Behavior.Service.service sched j t = ρ)) =
          true) →
    ∃ t',
      (decide (t1 ≤ t') && decide (t' < t2)) = true ∧
        Prosa.Model.Readiness.Suspension.suspended sched j t' = true ∧
          Prosa.Behavior.Service.service sched j t' = ρ ∧
            ∀ (t0 : ℕ),
              (decide (t1 ≤ t0) && decide (t0 < t')) = true →
                (!(Prosa.Model.Readiness.Suspension.suspended sched j t0 &&
                      decide (Prosa.Behavior.Service.service sched j t0 = ρ))) =
                  true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Suspension_exists_some_point
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
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) (_UU03c1_ : Prosa_Behavior_Job_work),
       Exists Nat
         (fun t : Nat =>
          And
            (@eq Bool
               (Decidable_decide
                  (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
                     (List_range' t1
                        (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                           Prosa_Behavior_Time_instant
                           (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1)
                        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
                     t)
                  (List_instDecidableMemOfLawfulBEq_inst1 Nat
                     (instBEqOfDecidableEq_inst1 Nat instDecidableEqNat) Nat_instLawfulBEq t
                     (List_range' t1
                        (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                           Prosa_Behavior_Time_instant
                           (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1)
                        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))))
               Bool_true)
            (@eq Bool
               (Bool_and
                  (Prosa_Model_Readiness_Suspension_suspended Job
                     inst_3 PState
                     inst_6
                     inst_9
                     inst_12 sched j t)
                  (Decidable_decide
                     (@eq Prosa_Behavior_Job_work
                        (Prosa_Behavior_Service_service Job
                           inst_3 PState sched
                           j t)
                        _UU03c1_)
                     (instDecidableEqNat
                        (Prosa_Behavior_Service_service Job
                           inst_3 PState sched
                           j t)
                        _UU03c1_)))
               Bool_true)) ->
       Exists Nat
         (fun t' : Nat =>
          And
            (@eq Bool
               (Bool_and
                  (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t')
                     (Nat_decLe t1 t'))
                  (Decidable_decide (LT_lt_inst1 Nat instLTNat t' t2) (Nat_decLt t' t2)))
               Bool_true)
            (And
               (@eq Bool
                  (Prosa_Model_Readiness_Suspension_suspended Job
                     inst_3 PState
                     inst_6
                     inst_9
                     inst_12 sched j t')
                  Bool_true)
               (And
                  (@eq Prosa_Behavior_Job_work
                     (Prosa_Behavior_Service_service Job
                        inst_3 PState sched j
                        t')
                     _UU03c1_)
                  (forall t0 : Nat,
                   @eq Bool
                     (Bool_and
                        (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t0)
                           (Nat_decLe t1 t0))
                        (Decidable_decide (LT_lt_inst1 Nat instLTNat t0 t') (Nat_decLt t0 t')))
                     Bool_true ->
                   @eq Bool
                     (Bool_not
                        (Bool_and
                           (Prosa_Model_Readiness_Suspension_suspended Job
                              inst_3 PState
                              inst_6
                              inst_9
                              inst_12 sched j
                              t0)
                           (Decidable_decide
                              (@eq Prosa_Behavior_Job_work
                                 (Prosa_Behavior_Service_service Job
                                    inst_3
                                    PState sched j t0)
                                 _UU03c1_)
                              (instDecidableEqNat
                                 (Prosa_Behavior_Service_service Job
                                    inst_3
                                    PState sched j t0)
                                 _UU03c1_))))
                     Bool_true))))
```
