# `job_completes_at_most_once`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.completes_at.job_completes_at_most_once`
- Lean: `Prosa.Analysis.Facts.CompletesAt.job_completes_at_most_once`
- Certificate: `job_completes_at_most_once_correspondence`

## Official Rocq

```coq
job_completes_at_most_once :
forall {Job : JobType} {H0 : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (j : Equality.sort Job) (t1 t2 : instant),
is_true (\sum_(t1 <= t < t2) nat_of_bool (@completes_at Job PState sched H0 j t) <= 1)

job_completes_at_most_once is not universe polymorphic
Arguments job_completes_at_most_once {Job H0 PState} sched j t1 t2
job_completes_at_most_once is opaque
Expands to: Constant prosa.analysis.facts.completes_at.job_completes_at_most_once
Declared in library prosa.analysis.facts.completes_at, line 49, characters 8-34
@job_completes_at_most_once
     : forall (Job : JobType) (H0 : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : instant),
       is_true (\sum_(t1 <= t < t2) nat_of_bool (@completes_at Job PState sched H0 j t) <= 1)
```

## Lean

```lean
@Prosa.Analysis.Facts.CompletesAt.job_completes_at_most_once : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (t1 t2 : Prosa.Behavior.Time.instant),
  ∑ t ∈ Finset.Ico t1 t2, (Prosa.Behavior.Service.completes_at sched j t).toNat ≤ 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_CompletesAt_job_completes_at_most_once
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       List_foldr_inst3 Nat Nat Nat_add 0
         (List_map_inst3 Nat Nat
            (fun t : Nat =>
             Bool_recl (fun _ : Bool => Nat) 0 1
               (Bool_recl (fun _ : Bool => Bool) Bool_false
                  (Decidable_recl
                     (job_cost _ _ inst_6 j <=
                      List_foldr_inst3 Nat Nat
                        (fun
                           x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                            x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                         Nat_add
                           x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                           x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                        0
                        (List_map_inst3 Nat Nat
                           (fun t0 : Prosa_Behavior_Time_instant =>
                            @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                              (fun l : List_inst1 Prosa_Behavior_Job_work =>
                               List_foldr_inst3 Nat Nat
                                 (fun
                                    x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                     x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                  Nat_add
                                    x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                 0 l)
                              (fun (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                 (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                        (List_isSetoid_inst1 Prosa_Behavior_Job_work) _l_UU2081_ _l_UU2082_) =>
                               List_Perm_foldr_eq_inst3 Nat Nat
                                 (fun
                                    x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                     x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                  Nat_add
                                    x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                 _l_UU2081_ _l_UU2082_
                                 (Multiset_sum__proof_1_inst1 Nat
                                    (AddCommMonoid_mk_inst1 Nat
                                       (AddMonoid_mk_inst1 Nat
                                          (AddSemigroup_mk_inst1 Nat (Add_mk_inst1 Nat Nat_add) Nat_add_assoc)
                                          (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                          (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n)) Nat_zero_mul
                                          Nat_succ_mul)
                                       Nat_add_comm))
                                 p 0)
                              (@Quot.lift (List (Core _ _ PState)) (List_Perm (Core _ _ PState))
                                 (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                 (fun
                                    l : List
                                          (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                             inst_3
                                             PState) =>
                                  @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                    (List_map_inst2 (Core _ _ PState) Nat
                                       (fun
                                          c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                inst_3
                                                PState =>
                                        service_on _ _ PState j (sched t0) c)
                                       l))
                                 (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                    (fun
                                       c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                             inst_3
                                             PState =>
                                     service_on _ _ PState j (sched t0) c))
                                 (val _ (elems _ (coreFintype _ _ PState)))))
                           (List_range' 0 (Nat_sub t 0) 1)))
                     (fun
                        _ : Decidable
                              (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                                 (Prosa_Behavior_Job_JobCost_job_cost Job
                                    inst_3
                                    inst_6 j)
                                 (Prosa_Behavior_Service_service Job
                                    inst_3
                                    PState sched j t)) =>
                      Bool)
                     (fun
                        _ : Not
                              (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                                 (Prosa_Behavior_Job_JobCost_job_cost Job
                                    inst_3
                                    inst_6 j)
                                 (Prosa_Behavior_Service_service Job
                                    inst_3
                                    PState sched j t)) =>
                      Bool_false)
                     (fun
                        _ : LE_le_inst1 Prosa_Behavior_Job_work instLENat
                              (Prosa_Behavior_Job_JobCost_job_cost Job
                                 inst_3
                                 inst_6 j)
                              (Prosa_Behavior_Service_service Job
                                 inst_3 PState
                                 sched j t) =>
                      Bool_true)
                     (Decidable_recl
                        (@eq Bool
                           (Nat_ble
                              (job_cost _ _
                                 inst_6 j)
                              (List_foldr_inst3 Nat Nat
                                 (fun
                                    x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                     x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                  Nat_add
                                    x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                 0
                                 (List_map_inst3 Nat Nat
                                    (fun t0 : Prosa_Behavior_Time_instant =>
                                     @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                       (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                        List_foldr_inst3 Nat Nat
                                          (fun
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                              x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                           Nat_add
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                             x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                          0 l)
                                       (fun (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                          (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                                 (List_isSetoid_inst1 Prosa_Behavior_Job_work) _l_UU2081_
                                                 _l_UU2082_) =>
                                        List_Perm_foldr_eq_inst3 Nat Nat
                                          (fun
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                              x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                           Nat_add
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                             x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                          _l_UU2081_ _l_UU2082_
                                          (Multiset_sum__proof_1_inst1 Nat
                                             (AddCommMonoid_mk_inst1 Nat
                                                (AddMonoid_mk_inst1 Nat
                                                   (AddSemigroup_mk_inst1 Nat (Add_mk_inst1 Nat Nat_add)
                                                      Nat_add_assoc)
                                                   (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                   (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                   Nat_zero_mul Nat_succ_mul)
                                                Nat_add_comm))
                                          p 0)
                                       (@Quot.lift (List (Core _ _ PState)) (List_Perm (Core _ _ PState))
                                          (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                          (fun
                                             l : List
                                                   (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                      inst_3
                                                      PState) =>
                                           @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                             (List_map_inst2 (Core _ _ PState) Nat
                                                (fun
                                                   c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                         inst_3
                                                         PState =>
                                                 service_on _ _ PState j (sched t0) c)
                                                l))
                                          (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                             (fun
                                                c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                      inst_3
                                                      PState =>
                                              service_on _ _ PState j (sched t0) c))
                                          (val _ (elems _ (coreFintype _ _ PState)))))
                                    (List_range' 0 (Nat_sub t 0) 1))))
                           Bool_true)
                        (fun
                           _ : Decidable
                                 (@eq Bool
                                    (Nat_ble
                                       (Prosa_Behavior_Job_JobCost_job_cost Job
                                          inst_3
                                          inst_6
                                          j)
                                       (Prosa_Behavior_Service_service Job
                                          inst_3
                                          PState sched j t))
                                    Bool_true) =>
                         Decidable
                           (job_cost _ _
                              inst_6 j <=
                            List_foldr_inst3 Nat Nat
                              (fun
                                 x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                  x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                               Nat_add
                                 x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                 x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                              0
                              (List_map_inst3 Nat Nat
                                 (fun t0 : Prosa_Behavior_Time_instant =>
                                  @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                    (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                     List_foldr_inst3 Nat Nat
                                       (fun
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                           x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                        Nat_add
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                          x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                       0 l)
                                    (fun (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                       (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                              (List_isSetoid_inst1 Prosa_Behavior_Job_work) _l_UU2081_
                                              _l_UU2082_) =>
                                     List_Perm_foldr_eq_inst3 Nat Nat
                                       (fun
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                           x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                        Nat_add
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                          x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                       _l_UU2081_ _l_UU2082_
                                       (Multiset_sum__proof_1_inst1 Nat
                                          (AddCommMonoid_mk_inst1 Nat
                                             (AddMonoid_mk_inst1 Nat
                                                (AddSemigroup_mk_inst1 Nat (Add_mk_inst1 Nat Nat_add)
                                                   Nat_add_assoc)
                                                (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                Nat_zero_mul Nat_succ_mul)
                                             Nat_add_comm))
                                       p 0)
                                    (@Quot.lift (List (Core _ _ PState)) (List_Perm (Core _ _ PState))
                                       (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                       (fun
                                          l : List
                                                (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                   inst_3
                                                   PState) =>
                                        @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                          (List_map_inst2 (Core _ _ PState) Nat
                                             (fun
                                                c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                      inst_3
                                                      PState =>
                                              service_on _ _ PState j (sched t0) c)
                                             l))
                                       (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                          (fun
                                             c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                   inst_3
                                                   PState =>
                                           service_on _ _ PState j (sched t0) c))
                                       (val _ (elems _ (coreFintype _ _ PState)))))
                                 (List_range' 0 (Nat_sub t 0) 1))))
                        (fun
                           h : Not
                                 (@eq Bool
                                    (Nat_ble
                                       (Prosa_Behavior_Job_JobCost_job_cost Job
                                          inst_3
                                          inst_6
                                          j)
                                       (Prosa_Behavior_Service_service Job
                                          inst_3
                                          PState sched j t))
                                    Bool_true) =>
                         Decidable_isFalse
                           (job_cost _ _
                              inst_6 j <=
                            List_foldr_inst3 Nat Nat
                              (fun
                                 x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                  x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                               Nat_add
                                 x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                 x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                              0
                              (List_map_inst3 Nat Nat
                                 (fun t0 : Prosa_Behavior_Time_instant =>
                                  @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                    (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                     List_foldr_inst3 Nat Nat
                                       (fun
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                           x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                        Nat_add
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                          x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                       0 l)
                                    (fun (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                       (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                              (List_isSetoid_inst1 Prosa_Behavior_Job_work) _l_UU2081_
                                              _l_UU2082_) =>
                                     List_Perm_foldr_eq_inst3 Nat Nat
                                       (fun
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                           x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                        Nat_add
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                          x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                       _l_UU2081_ _l_UU2082_
                                       (Multiset_sum__proof_1_inst1 Nat
                                          (AddCommMonoid_mk_inst1 Nat
                                             (AddMonoid_mk_inst1 Nat
                                                (AddSemigroup_mk_inst1 Nat (Add_mk_inst1 Nat Nat_add)
                                                   Nat_add_assoc)
                                                (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                Nat_zero_mul Nat_succ_mul)
                                             Nat_add_comm))
                                       p 0)
                                    (@Quot.lift (List (Core _ _ PState)) (List_Perm (Core _ _ PState))
                                       (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                       (fun
                                          l : List
                                                (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                   inst_3
                                                   PState) =>
                                        @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                          (List_map_inst2 (Core _ _ PState) Nat
                                             (fun
                                                c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                      inst_3
                                                      PState =>
                                              service_on _ _ PState j (sched t0) c)
                                             l))
                                       (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                          (fun
                                             c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                   inst_3
                                                   PState =>
                                           service_on _ _ PState j (sched t0) c))
                                       (val _ (elems _ (coreFintype _ _ PState)))))
                                 (List_range' 0 (Nat_sub t 0) 1)))
                           (Nat_not_le_of_not_ble_eq_true
                              (job_cost _ _
                                 inst_6 j)
                              (List_foldr_inst3 Nat Nat
                                 (fun
                                    x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                     x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                  Nat_add
                                    x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                 0
                                 (List_map_inst3 Nat Nat
                                    (fun t0 : Prosa_Behavior_Time_instant =>
                                     @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                       (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                        List_foldr_inst3 Nat Nat
                                          (fun
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                              x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                           Nat_add
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                             x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                          0 l)
                                       (fun (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                          (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                                 (List_isSetoid_inst1 Prosa_Behavior_Job_work) _l_UU2081_
                                                 _l_UU2082_) =>
                                        List_Perm_foldr_eq_inst3 Nat Nat
                                          (fun
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                              x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                           Nat_add
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                             x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                          _l_UU2081_ _l_UU2082_
                                          (Multiset_sum__proof_1_inst1 Nat
                                             (AddCommMonoid_mk_inst1 Nat
                                                (AddMonoid_mk_inst1 Nat
                                                   (AddSemigroup_mk_inst1 Nat (Add_mk_inst1 Nat Nat_add)
                                                      Nat_add_assoc)
                                                   (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                   (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                   Nat_zero_mul Nat_succ_mul)
                                                Nat_add_comm))
                                          p 0)
                                       (@Quot.lift (List (Core _ _ PState)) (List_Perm (Core _ _ PState))
                                          (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                          (fun
                                             l : List
                                                   (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                      inst_3
                                                      PState) =>
                                           @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                             (List_map_inst2 (Core _ _ PState) Nat
                                                (fun
                                                   c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                         inst_3
                                                         PState =>
                                                 service_on _ _ PState j (sched t0) c)
                                                l))
                                          (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                             (fun
                                                c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                      inst_3
                                                      PState =>
                                              service_on _ _ PState j (sched t0) c))
                                          (val _ (elems _ (coreFintype _ _ PState)))))
                                    (List_range' 0 (Nat_sub t 0) 1)))
                              h))
                        (fun
                           h : @eq Bool
                                 (Nat_ble
                                    (Prosa_Behavior_Job_JobCost_job_cost Job
                                       inst_3
                                       inst_6
                                       j)
                                    (Prosa_Behavior_Service_service Job
                                       inst_3
                                       PState sched j t))
                                 Bool_true =>
                         Decidable_isTrue
                           (job_cost _ _
                              inst_6 j <=
                            List_foldr_inst3 Nat Nat
                              (fun
                                 x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                  x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                               Nat_add
                                 x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                 x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                              0
                              (List_map_inst3 Nat Nat
                                 (fun t0 : Prosa_Behavior_Time_instant =>
                                  @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                    (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                     List_foldr_inst3 Nat Nat
                                       (fun
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                           x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                        Nat_add
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                          x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                       0 l)
                                    (fun (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                       (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                              (List_isSetoid_inst1 Prosa_Behavior_Job_work) _l_UU2081_
                                              _l_UU2082_) =>
                                     List_Perm_foldr_eq_inst3 Nat Nat
                                       (fun
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                           x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                        Nat_add
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                          x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                       _l_UU2081_ _l_UU2082_
                                       (Multiset_sum__proof_1_inst1 Nat
                                          (AddCommMonoid_mk_inst1 Nat
                                             (AddMonoid_mk_inst1 Nat
                                                (AddSemigroup_mk_inst1 Nat (Add_mk_inst1 Nat Nat_add)
                                                   Nat_add_assoc)
                                                (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                Nat_zero_mul Nat_succ_mul)
                                             Nat_add_comm))
                                       p 0)
                                    (@Quot.lift (List (Core _ _ PState)) (List_Perm (Core _ _ PState))
                                       (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                       (fun
                                          l : List
                                                (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                   inst_3
                                                   PState) =>
                                        @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                          (List_map_inst2 (Core _ _ PState) Nat
                                             (fun
                                                c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                      inst_3
                                                      PState =>
                                              service_on _ _ PState j (sched t0) c)
                                             l))
                                       (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                          (fun
                                             c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                   inst_3
                                                   PState =>
                                           service_on _ _ PState j (sched t0) c))
                                       (val _ (elems _ (coreFintype _ _ PState)))))
                                 (List_range' 0 (Nat_sub t 0) 1)))
                           (Nat_le_of_ble_eq_true
                              (job_cost _ _
                                 inst_6 j)
                              (List_foldr_inst3 Nat Nat
                                 (fun
                                    x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                     x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                  Nat_add
                                    x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                 0
                                 (List_map_inst3 Nat Nat
                                    (fun t0 : Prosa_Behavior_Time_instant =>
                                     @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                       (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                        List_foldr_inst3 Nat Nat
                                          (fun
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                              x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                           Nat_add
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                             x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                          0 l)
                                       (fun (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                          (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                                 (List_isSetoid_inst1 Prosa_Behavior_Job_work) _l_UU2081_
                                                 _l_UU2082_) =>
                                        List_Perm_foldr_eq_inst3 Nat Nat
                                          (fun
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                              x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                           Nat_add
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                             x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                          _l_UU2081_ _l_UU2082_
                                          (Multiset_sum__proof_1_inst1 Nat
                                             (AddCommMonoid_mk_inst1 Nat
                                                (AddMonoid_mk_inst1 Nat
                                                   (AddSemigroup_mk_inst1 Nat (Add_mk_inst1 Nat Nat_add)
                                                      Nat_add_assoc)
                                                   (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                   (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                   Nat_zero_mul Nat_succ_mul)
                                                Nat_add_comm))
                                          p 0)
                                       (@Quot.lift (List (Core _ _ PState)) (List_Perm (Core _ _ PState))
                                          (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                          (fun
                                             l : List
                                                   (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                      inst_3
                                                      PState) =>
                                           @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                             (List_map_inst2 (Core _ _ PState) Nat
                                                (fun
                                                   c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                         inst_3
                                                         PState =>
                                                 service_on _ _ PState j (sched t0) c)
                                                l))
                                          (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                             (fun
                                                c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                      inst_3
                                                      PState =>
                                              service_on _ _ PState j (sched t0) c))
                                          (val _ (elems _ (coreFintype _ _ PState)))))
                                    (List_range' 0 (Nat_sub t 0) 1)))
                              h))
                        (Bool_recl (fun x : Bool => Decidable (@eq Bool x Bool_true))
                           (Decidable_isFalse (@eq Bool Bool_false Bool_true)
                              (fun h : @eq Bool Bool_false Bool_true =>
                               Eq_indl Bool Bool_false
                                 (fun (x____at___Init_Prelude2055208596__hygCtx__hyg17 : Bool)
                                    (_ : @eq Bool Bool_false x____at___Init_Prelude2055208596__hygCtx__hyg17) =>
                                  Bool_recl (fun _ : Bool => SProp) (False -> False) False
                                    x____at___Init_Prelude2055208596__hygCtx__hyg17)
                                 (fun h0 : False => h0) Bool_true h))
                           (Decidable_isTrue (@eq Bool Bool_true Bool_true) (@eq_refl Bool Bool_true))
                           (Nat_ble
                              (job_cost _ _
                                 inst_6 j)
                              (List_foldr_inst3 Nat Nat
                                 (fun
                                    x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                     x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                  Nat_add
                                    x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                 0
                                 (List_map_inst3 Nat Nat
                                    (fun t0 : Prosa_Behavior_Time_instant =>
                                     @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                       (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                        List_foldr_inst3 Nat Nat
                                          (fun
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                              x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                           Nat_add
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                             x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                          0 l)
                                       (fun (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                          (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                                 (List_isSetoid_inst1 Prosa_Behavior_Job_work) _l_UU2081_
                                                 _l_UU2082_) =>
                                        List_Perm_foldr_eq_inst3 Nat Nat
                                          (fun
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                              x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                           Nat_add
                                             x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                             x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                          _l_UU2081_ _l_UU2082_
                                          (Multiset_sum__proof_1_inst1 Nat
                                             (AddCommMonoid_mk_inst1 Nat
                                                (AddMonoid_mk_inst1 Nat
                                                   (AddSemigroup_mk_inst1 Nat (Add_mk_inst1 Nat Nat_add)
                                                      Nat_add_assoc)
                                                   (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                   (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                   Nat_zero_mul Nat_succ_mul)
                                                Nat_add_comm))
                                          p 0)
                                       (@Quot.lift (List (Core _ _ PState)) (List_Perm (Core _ _ PState))
                                          (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                          (fun
                                             l : List
                                                   (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                      inst_3
                                                      PState) =>
                                           @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                             (List_map_inst2 (Core _ _ PState) Nat
                                                (fun
                                                   c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                         inst_3
                                                         PState =>
                                                 service_on _ _ PState j (sched t0) c)
                                                l))
                                          (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                             (fun
                                                c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                      inst_3
                                                      PState =>
                                              service_on _ _ PState j (sched t0) c))
                                          (val _ (elems _ (coreFintype _ _ PState)))))
                                    (List_range' 0 (Nat_sub t 0) 1)))))))
                  (Bool_recl (fun _ : Bool => Bool)
                     (Decidable_recl (@eq Nat t 0)
                        (fun
                           _ : Decidable
                                 (@eq Prosa_Behavior_Time_instant t
                                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0))) =>
                         Bool)
                        (fun
                           _ : Not
                                 (@eq Prosa_Behavior_Time_instant t
                                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0))) =>
                         Bool_false)
                        (fun
                           _ : @eq Prosa_Behavior_Time_instant t
                                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) =>
                         Bool_true)
                        (Bool_recl
                           (fun x : Bool =>
                            @eq Bool
                              (Nat_beq t (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)))
                              x ->
                            Decidable (@eq Nat t 0))
                           (fun
                              h : @eq Bool
                                    (Nat_beq t
                                       (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)))
                                    Bool_false =>
                            Decidable_isFalse (@eq Nat t 0) (Nat_ne_of_beq_eq_false t 0 h))
                           (fun
                              h : @eq Bool
                                    (Nat_beq t
                                       (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)))
                                    Bool_true =>
                            Decidable_isTrue (@eq Nat t 0) (Nat_eq_of_beq_eq_true t 0 h))
                           (Nat_beq t 0) (@eq_refl Bool (Nat_beq t 0))))
                     Bool_true
                     (Bool_recl (fun _ : Bool => Bool) Bool_true Bool_false
                        (Decidable_recl
                           (job_cost _ _
                              inst_6 j <=
                            List_foldr_inst3 Nat Nat
                              (fun
                                 x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                  x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                               Nat_add
                                 x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                 x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                              0
                              (List_map_inst3 Nat Nat
                                 (fun t0 : Prosa_Behavior_Time_instant =>
                                  @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                    (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                     List_foldr_inst3 Nat Nat
                                       (fun
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                           x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                        Nat_add
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                          x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                       0 l)
                                    (fun (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                       (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                              (List_isSetoid_inst1 Prosa_Behavior_Job_work) _l_UU2081_
                                              _l_UU2082_) =>
                                     List_Perm_foldr_eq_inst3 Nat Nat
                                       (fun
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                           x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                        Nat_add
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                          x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                       _l_UU2081_ _l_UU2082_
                                       (Multiset_sum__proof_1_inst1 Nat
                                          (AddCommMonoid_mk_inst1 Nat
                                             (AddMonoid_mk_inst1 Nat
                                                (AddSemigroup_mk_inst1 Nat (Add_mk_inst1 Nat Nat_add)
                                                   Nat_add_assoc)
                                                (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                Nat_zero_mul Nat_succ_mul)
                                             Nat_add_comm))
                                       p 0)
                                    (@Quot.lift (List (Core _ _ PState)) (List_Perm (Core _ _ PState))
                                       (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                       (fun
                                          l : List
                                                (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                   inst_3
                                                   PState) =>
                                        @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                          (List_map_inst2 (Core _ _ PState) Nat
                                             (fun
                                                c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                      inst_3
                                                      PState =>
                                              service_on _ _ PState j (sched t0) c)
                                             l))
                                       (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                          (fun
                                             c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                   inst_3
                                                   PState =>
                                           service_on _ _ PState j (sched t0) c))
                                       (val _ (elems _ (coreFintype _ _ PState)))))
                                 (List_range' 0 (Nat_sub (Nat_sub t 1) 0) 1)))
                           (fun
                              _ : Decidable
                                    (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                                       (Prosa_Behavior_Job_JobCost_job_cost Job
                                          inst_3
                                          inst_6
                                          j)
                                       (Prosa_Behavior_Service_service Job
                                          inst_3
                                          PState sched j
                                          (HSub_hSub_inst7 Prosa_Behavior_Time_instant
                                             Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                                             (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t
                                             (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1
                                                (instOfNatNat 1))))) =>
                            Bool)
                           (fun
                              _ : Not
                                    (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                                       (Prosa_Behavior_Job_JobCost_job_cost Job
                                          inst_3
                                          inst_6
                                          j)
                                       (Prosa_Behavior_Service_service Job
                                          inst_3
                                          PState sched j
                                          (HSub_hSub_inst7 Prosa_Behavior_Time_instant
                                             Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                                             (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t
                                             (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1
                                                (instOfNatNat 1))))) =>
                            Bool_false)
                           (fun
                              _ : LE_le_inst1 Prosa_Behavior_Job_work instLENat
                                    (Prosa_Behavior_Job_JobCost_job_cost Job
                                       inst_3
                                       inst_6
                                       j)
                                    (Prosa_Behavior_Service_service Job
                                       inst_3
                                       PState sched j
                                       (HSub_hSub_inst7 Prosa_Behavior_Time_instant
                                          Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                                          (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t
                                          (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))) =>
                            Bool_true)
                           (Decidable_recl
                              (@eq Bool
                                 (Nat_ble
                                    (job_cost _ _
                                       inst_6
                                       j)
                                    (List_foldr_inst3 Nat Nat
                                       (fun
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                           x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                        Nat_add
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                          x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                       0
                                       (List_map_inst3 Nat Nat
                                          (fun t0 : Prosa_Behavior_Time_instant =>
                                           @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                             (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                              List_foldr_inst3 Nat Nat
                                                (fun
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                                 Nat_add
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                   x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                                0 l)
                                             (fun
                                                (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                                (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                                       (List_isSetoid_inst1 Prosa_Behavior_Job_work)
                                                       _l_UU2081_ _l_UU2082_) =>
                                              List_Perm_foldr_eq_inst3 Nat Nat
                                                (fun
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                                 Nat_add
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                   x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                                _l_UU2081_ _l_UU2082_
                                                (Multiset_sum__proof_1_inst1 Nat
                                                   (AddCommMonoid_mk_inst1 Nat
                                                      (AddMonoid_mk_inst1 Nat
                                                         (AddSemigroup_mk_inst1 Nat
                                                            (Add_mk_inst1 Nat Nat_add) Nat_add_assoc)
                                                         (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                         (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                         Nat_zero_mul Nat_succ_mul)
                                                      Nat_add_comm))
                                                p 0)
                                             (@Quot.lift (List (Core _ _ PState))
                                                (List_Perm (Core _ _ PState))
                                                (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                                (fun
                                                   l : List
                                                         (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                            inst_3
                                                            PState) =>
                                                 @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                                   (List_map_inst2 (Core _ _ PState) Nat
                                                      (fun
                                                         c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                               inst_3
                                                               PState =>
                                                       service_on _ _ PState j (sched t0) c)
                                                      l))
                                                (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                                   (fun
                                                      c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                            inst_3
                                                            PState =>
                                                    service_on _ _ PState j (sched t0) c))
                                                (val _ (elems _ (coreFintype _ _ PState)))))
                                          (List_range' 0 (Nat_sub (Nat_sub t 1) 0) 1))))
                                 Bool_true)
                              (fun
                                 _ : Decidable
                                       (@eq Bool
                                          (Nat_ble
                                             (Prosa_Behavior_Job_JobCost_job_cost Job
                                                inst_3
                                                inst_6
                                                j)
                                             (Prosa_Behavior_Service_service Job
                                                inst_3
                                                PState sched j
                                                (HSub_hSub_inst7 Prosa_Behavior_Time_instant
                                                   Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                                                   (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t
                                                   (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1
                                                      (instOfNatNat 1)))))
                                          Bool_true) =>
                               Decidable
                                 (job_cost _ _
                                    inst_6 j <=
                                  List_foldr_inst3 Nat Nat
                                    (fun
                                       x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                        x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                     Nat_add
                                       x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                       x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                    0
                                    (List_map_inst3 Nat Nat
                                       (fun t0 : Prosa_Behavior_Time_instant =>
                                        @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                          (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                           List_foldr_inst3 Nat Nat
                                             (fun
                                                x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                 x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                              Nat_add
                                                x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                             0 l)
                                          (fun (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                             (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                                    (List_isSetoid_inst1 Prosa_Behavior_Job_work) _l_UU2081_
                                                    _l_UU2082_) =>
                                           List_Perm_foldr_eq_inst3 Nat Nat
                                             (fun
                                                x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                 x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                              Nat_add
                                                x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                             _l_UU2081_ _l_UU2082_
                                             (Multiset_sum__proof_1_inst1 Nat
                                                (AddCommMonoid_mk_inst1 Nat
                                                   (AddMonoid_mk_inst1 Nat
                                                      (AddSemigroup_mk_inst1 Nat 
                                                         (Add_mk_inst1 Nat Nat_add) Nat_add_assoc)
                                                      (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                      (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                      Nat_zero_mul Nat_succ_mul)
                                                   Nat_add_comm))
                                             p 0)
                                          (@Quot.lift (List (Core _ _ PState)) (List_Perm (Core _ _ PState))
                                             (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                             (fun
                                                l : List
                                                      (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                         inst_3
                                                         PState) =>
                                              @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                                (List_map_inst2 (Core _ _ PState) Nat
                                                   (fun
                                                      c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                            inst_3
                                                            PState =>
                                                    service_on _ _ PState j (sched t0) c)
                                                   l))
                                             (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                                (fun
                                                   c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                         inst_3
                                                         PState =>
                                                 service_on _ _ PState j (sched t0) c))
                                             (val _ (elems _ (coreFintype _ _ PState)))))
                                       (List_range' 0 (Nat_sub (Nat_sub t 1) 0) 1))))
                              (fun
                                 h : Not
                                       (@eq Bool
                                          (Nat_ble
                                             (Prosa_Behavior_Job_JobCost_job_cost Job
                                                inst_3
                                                inst_6
                                                j)
                                             (Prosa_Behavior_Service_service Job
                                                inst_3
                                                PState sched j
                                                (HSub_hSub_inst7 Prosa_Behavior_Time_instant
                                                   Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                                                   (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t
                                                   (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1
                                                      (instOfNatNat 1)))))
                                          Bool_true) =>
                               Decidable_isFalse
                                 (job_cost _ _
                                    inst_6 j <=
                                  List_foldr_inst3 Nat Nat
                                    (fun
                                       x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                        x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                     Nat_add
                                       x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                       x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                    0
                                    (List_map_inst3 Nat Nat
                                       (fun t0 : Prosa_Behavior_Time_instant =>
                                        @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                          (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                           List_foldr_inst3 Nat Nat
                                             (fun
                                                x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                 x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                              Nat_add
                                                x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                             0 l)
                                          (fun (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                             (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                                    (List_isSetoid_inst1 Prosa_Behavior_Job_work) _l_UU2081_
                                                    _l_UU2082_) =>
                                           List_Perm_foldr_eq_inst3 Nat Nat
                                             (fun
                                                x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                 x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                              Nat_add
                                                x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                             _l_UU2081_ _l_UU2082_
                                             (Multiset_sum__proof_1_inst1 Nat
                                                (AddCommMonoid_mk_inst1 Nat
                                                   (AddMonoid_mk_inst1 Nat
                                                      (AddSemigroup_mk_inst1 Nat 
                                                         (Add_mk_inst1 Nat Nat_add) Nat_add_assoc)
                                                      (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                      (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                      Nat_zero_mul Nat_succ_mul)
                                                   Nat_add_comm))
                                             p 0)
                                          (@Quot.lift (List (Core _ _ PState)) (List_Perm (Core _ _ PState))
                                             (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                             (fun
                                                l : List
                                                      (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                         inst_3
                                                         PState) =>
                                              @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                                (List_map_inst2 (Core _ _ PState) Nat
                                                   (fun
                                                      c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                            inst_3
                                                            PState =>
                                                    service_on _ _ PState j (sched t0) c)
                                                   l))
                                             (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                                (fun
                                                   c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                         inst_3
                                                         PState =>
                                                 service_on _ _ PState j (sched t0) c))
                                             (val _ (elems _ (coreFintype _ _ PState)))))
                                       (List_range' 0 (Nat_sub (Nat_sub t 1) 0) 1)))
                                 (Nat_not_le_of_not_ble_eq_true
                                    (job_cost _ _
                                       inst_6
                                       j)
                                    (List_foldr_inst3 Nat Nat
                                       (fun
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                           x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                        Nat_add
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                          x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                       0
                                       (List_map_inst3 Nat Nat
                                          (fun t0 : Prosa_Behavior_Time_instant =>
                                           @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                             (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                              List_foldr_inst3 Nat Nat
                                                (fun
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                                 Nat_add
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                   x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                                0 l)
                                             (fun
                                                (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                                (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                                       (List_isSetoid_inst1 Prosa_Behavior_Job_work)
                                                       _l_UU2081_ _l_UU2082_) =>
                                              List_Perm_foldr_eq_inst3 Nat Nat
                                                (fun
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                                 Nat_add
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                   x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                                _l_UU2081_ _l_UU2082_
                                                (Multiset_sum__proof_1_inst1 Nat
                                                   (AddCommMonoid_mk_inst1 Nat
                                                      (AddMonoid_mk_inst1 Nat
                                                         (AddSemigroup_mk_inst1 Nat
                                                            (Add_mk_inst1 Nat Nat_add) Nat_add_assoc)
                                                         (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                         (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                         Nat_zero_mul Nat_succ_mul)
                                                      Nat_add_comm))
                                                p 0)
                                             (@Quot.lift (List (Core _ _ PState))
                                                (List_Perm (Core _ _ PState))
                                                (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                                (fun
                                                   l : List
                                                         (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                            inst_3
                                                            PState) =>
                                                 @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                                   (List_map_inst2 (Core _ _ PState) Nat
                                                      (fun
                                                         c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                               inst_3
                                                               PState =>
                                                       service_on _ _ PState j (sched t0) c)
                                                      l))
                                                (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                                   (fun
                                                      c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                            inst_3
                                                            PState =>
                                                    service_on _ _ PState j (sched t0) c))
                                                (val _ (elems _ (coreFintype _ _ PState)))))
                                          (List_range' 0 (Nat_sub (Nat_sub t 1) 0) 1)))
                                    h))
                              (fun
                                 h : @eq Bool
                                       (Nat_ble
                                          (Prosa_Behavior_Job_JobCost_job_cost Job
                                             inst_3
                                             inst_6
                                             j)
                                          (Prosa_Behavior_Service_service Job
                                             inst_3
                                             PState sched j
                                             (HSub_hSub_inst7 Prosa_Behavior_Time_instant
                                                Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                                                (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t
                                                (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1
                                                   (instOfNatNat 1)))))
                                       Bool_true =>
                               Decidable_isTrue
                                 (job_cost _ _
                                    inst_6 j <=
                                  List_foldr_inst3 Nat Nat
                                    (fun
                                       x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                        x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                     Nat_add
                                       x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                       x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                    0
                                    (List_map_inst3 Nat Nat
                                       (fun t0 : Prosa_Behavior_Time_instant =>
                                        @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                          (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                           List_foldr_inst3 Nat Nat
                                             (fun
                                                x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                 x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                              Nat_add
                                                x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                             0 l)
                                          (fun (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                             (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                                    (List_isSetoid_inst1 Prosa_Behavior_Job_work) _l_UU2081_
                                                    _l_UU2082_) =>
                                           List_Perm_foldr_eq_inst3 Nat Nat
                                             (fun
                                                x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                 x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                              Nat_add
                                                x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                             _l_UU2081_ _l_UU2082_
                                             (Multiset_sum__proof_1_inst1 Nat
                                                (AddCommMonoid_mk_inst1 Nat
                                                   (AddMonoid_mk_inst1 Nat
                                                      (AddSemigroup_mk_inst1 Nat 
                                                         (Add_mk_inst1 Nat Nat_add) Nat_add_assoc)
                                                      (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                      (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                      Nat_zero_mul Nat_succ_mul)
                                                   Nat_add_comm))
                                             p 0)
                                          (@Quot.lift (List (Core _ _ PState)) (List_Perm (Core _ _ PState))
                                             (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                             (fun
                                                l : List
                                                      (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                         inst_3
                                                         PState) =>
                                              @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                                (List_map_inst2 (Core _ _ PState) Nat
                                                   (fun
                                                      c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                            inst_3
                                                            PState =>
                                                    service_on _ _ PState j (sched t0) c)
                                                   l))
                                             (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                                (fun
                                                   c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                         inst_3
                                                         PState =>
                                                 service_on _ _ PState j (sched t0) c))
                                             (val _ (elems _ (coreFintype _ _ PState)))))
                                       (List_range' 0 (Nat_sub (Nat_sub t 1) 0) 1)))
                                 (Nat_le_of_ble_eq_true
                                    (job_cost _ _
                                       inst_6
                                       j)
                                    (List_foldr_inst3 Nat Nat
                                       (fun
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                           x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                        Nat_add
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                          x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                       0
                                       (List_map_inst3 Nat Nat
                                          (fun t0 : Prosa_Behavior_Time_instant =>
                                           @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                             (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                              List_foldr_inst3 Nat Nat
                                                (fun
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                                 Nat_add
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                   x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                                0 l)
                                             (fun
                                                (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                                (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                                       (List_isSetoid_inst1 Prosa_Behavior_Job_work)
                                                       _l_UU2081_ _l_UU2082_) =>
                                              List_Perm_foldr_eq_inst3 Nat Nat
                                                (fun
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                                 Nat_add
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                   x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                                _l_UU2081_ _l_UU2082_
                                                (Multiset_sum__proof_1_inst1 Nat
                                                   (AddCommMonoid_mk_inst1 Nat
                                                      (AddMonoid_mk_inst1 Nat
                                                         (AddSemigroup_mk_inst1 Nat
                                                            (Add_mk_inst1 Nat Nat_add) Nat_add_assoc)
                                                         (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                         (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                         Nat_zero_mul Nat_succ_mul)
                                                      Nat_add_comm))
                                                p 0)
                                             (@Quot.lift (List (Core _ _ PState))
                                                (List_Perm (Core _ _ PState))
                                                (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                                (fun
                                                   l : List
                                                         (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                            inst_3
                                                            PState) =>
                                                 @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                                   (List_map_inst2 (Core _ _ PState) Nat
                                                      (fun
                                                         c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                               inst_3
                                                               PState =>
                                                       service_on _ _ PState j (sched t0) c)
                                                      l))
                                                (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                                   (fun
                                                      c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                            inst_3
                                                            PState =>
                                                    service_on _ _ PState j (sched t0) c))
                                                (val _ (elems _ (coreFintype _ _ PState)))))
                                          (List_range' 0 (Nat_sub (Nat_sub t 1) 0) 1)))
                                    h))
                              (Bool_recl (fun x : Bool => Decidable (@eq Bool x Bool_true))
                                 (Decidable_isFalse (@eq Bool Bool_false Bool_true)
                                    (fun h : @eq Bool Bool_false Bool_true =>
                                     Eq_indl Bool Bool_false
                                       (fun (x____at___Init_Prelude2055208596__hygCtx__hyg17 : Bool)
                                          (_ : @eq Bool Bool_false
                                                 x____at___Init_Prelude2055208596__hygCtx__hyg17) =>
                                        Bool_recl (fun _ : Bool => SProp) (False -> False) False
                                          x____at___Init_Prelude2055208596__hygCtx__hyg17)
                                       (fun h0 : False => h0) Bool_true h))
                                 (Decidable_isTrue (@eq Bool Bool_true Bool_true) (@eq_refl Bool Bool_true))
                                 (Nat_ble
                                    (job_cost _ _
                                       inst_6
                                       j)
                                    (List_foldr_inst3 Nat Nat
                                       (fun
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                           x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                        Nat_add
                                          x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                          x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                       0
                                       (List_map_inst3 Nat Nat
                                          (fun t0 : Prosa_Behavior_Time_instant =>
                                           @Quot.lift (List_inst1 Nat) (List_Perm_inst1 Nat) Nat
                                             (fun l : List_inst1 Prosa_Behavior_Job_work =>
                                              List_foldr_inst3 Nat Nat
                                                (fun
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                                 Nat_add
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                   x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                                0 l)
                                             (fun
                                                (_l_UU2081_ _l_UU2082_ : List_inst1 Prosa_Behavior_Job_work)
                                                (p : Setoid_r (List_inst1 Prosa_Behavior_Job_work)
                                                       (List_isSetoid_inst1 Prosa_Behavior_Job_work)
                                                       _l_UU2081_ _l_UU2082_) =>
                                              List_Perm_foldr_eq_inst3 Nat Nat
                                                (fun
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                    x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32 : Prosa_Behavior_Job_work =>
                                                 Nat_add
                                                   x1____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32
                                                   x2____at___Mathlib_Algebra_BigOperators_Group_Multiset_Defs1557692325__hygCtx__hyg32)
                                                _l_UU2081_ _l_UU2082_
                                                (Multiset_sum__proof_1_inst1 Nat
                                                   (AddCommMonoid_mk_inst1 Nat
                                                      (AddMonoid_mk_inst1 Nat
                                                         (AddSemigroup_mk_inst1 Nat
                                                            (Add_mk_inst1 Nat Nat_add) Nat_add_assoc)
                                                         (Zero_mk_inst1 Nat 0) Nat_zero_add Nat_add_zero
                                                         (NSMul_mk_inst1 Nat (fun m n : Nat => Nat_mul m n))
                                                         Nat_zero_mul Nat_succ_mul)
                                                      Nat_add_comm))
                                                p 0)
                                             (@Quot.lift (List (Core _ _ PState))
                                                (List_Perm (Core _ _ PState))
                                                (@Quot.quot (List_inst1 Nat) (List_Perm_inst1 Nat))
                                                (fun
                                                   l : List
                                                         (Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                            inst_3
                                                            PState) =>
                                                 @Quot.mk (List_inst1 Nat) (List_Perm_inst1 Nat)
                                                   (List_map_inst2 (Core _ _ PState) Nat
                                                      (fun
                                                         c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                               inst_3
                                                               PState =>
                                                       service_on _ _ PState j (sched t0) c)
                                                      l))
                                                (Multiset_map__proof_1_inst2 (Core _ _ PState) Nat
                                                   (fun
                                                      c : Prosa_Behavior_Schedule_ProcessorState_Core Job
                                                            inst_3
                                                            PState =>
                                                    service_on _ _ PState j (sched t0) c))
                                                (val _ (elems _ (coreFintype _ _ PState)))))
                                          (List_range' 0 (Nat_sub (Nat_sub t 1) 0) 1)))))))))))
            (List_range' t1 (Nat_sub t2 t1) 1)) <=
       1
```
