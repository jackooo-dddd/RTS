# `correct_search_space`

- Kind (Rocq): Corollary
- Rocq: `prosa.results.rta.ideal.gel.bounded_pi.correct_search_space`
- Lean: `Prosa.Results.Rta.Ideal.Gel.BoundedPi.correct_search_space`
- Certificate: `correct_search_space_correspondence`

## Official Rocq

```coq
correct_search_space :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {H2 : MaxArrivals Task} {H5 : gel.PriorityPoint Task} (ts : seq (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H2) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall (priority_inversion_bound : duration -> duration) (L : duration),
is_true (0 < L) ->
forall R : duration,
(forall A : duration,
 is_true (@is_in_search_space Task H H2 H5 ts tsk priority_inversion_bound L A) ->
 exists F : duration,
   is_true
     (priority_inversion_bound A +
      (@task_request_bound_function Task H H2 tsk (A + 1) - (@task_cost Task H tsk - @task_rtct Task H0 tsk)) +
      (fun A0 Δ : duration =>
       \sum_(tsk_o <- ts | tsk_o != tsk)
          @task_request_bound_function Task H H2 tsk_o
            (minn
               (ssrint.absz
                  (@order.Order.max ssrnum.ring_display
                     (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
                        ssrint.ssrint_int__canonical__Num_POrderedZmodule)
                     (@ssralg.GRing.zero
                        (ssrnum.Num.POrderedZmodule.Exports.Num_POrderedZmodule__to__GRing_Nmodule
                           ssrint.ssrint_int__canonical__Num_POrderedZmodule))
                     ((fun (tsk_o0 : Equality.sort Task) (A1 : instant) =>
                       @ssralg.GRing.add
                         (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                            ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                         (@ssralg.GRing.add
                            (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                               ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                            (@ssralg.GRing.natmul
                               (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                  ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                               (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) 
                               (A1 + 1))
                            (@gel.task_priority_point Task H5 tsk))
                         (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
                            (@gel.task_priority_point Task H5 tsk_o0)))
                        tsk_o A0)))
               Δ))
        A (A + F) <=
      A + F) /\
   is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
is_true (0 < @task_cost Task H tsk) ->
is_true (0 < @max_arrivals Task H2 tsk 1) ->
forall A : nat,
search_space.is_in_search_space L
  (fun A0 Δ : duration =>
   @task_request_bound_function Task H H2 tsk (A0 + 1) - @task_cost Task H tsk +
   (fun A1 R0 : duration =>
    priority_inversion_bound A1 +
    (fun A2 Δ0 : duration =>
     \sum_(tsk_o <- ts | tsk_o != tsk)
        @task_request_bound_function Task H H2 tsk_o
          (minn
             (ssrint.absz
                (@order.Order.max ssrnum.ring_display
                   (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
                      ssrint.ssrint_int__canonical__Num_POrderedZmodule)
                   (@ssralg.GRing.zero
                      (ssrnum.Num.POrderedZmodule.Exports.Num_POrderedZmodule__to__GRing_Nmodule
                         ssrint.ssrint_int__canonical__Num_POrderedZmodule))
                   ((fun (tsk_o0 : Equality.sort Task) (A3 : instant) =>
                     @ssralg.GRing.add
                       (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                          ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                       (@ssralg.GRing.add
                          (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                             ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                          (@ssralg.GRing.natmul
                             (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                             (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) 
                             (A3 + 1))
                          (@gel.task_priority_point Task H5 tsk))
                       (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
                          (@gel.task_priority_point Task H5 tsk_o0)))
                      tsk_o A2)))
             Δ0))
      A1 R0)
     A0 Δ)
  A ->
exists F : nat,
  is_true
    (@task_request_bound_function Task H H2 tsk (A + 1) - (@task_cost Task H tsk - @task_rtct Task H0 tsk) +
     (fun A0 R0 : duration =>
      priority_inversion_bound A0 +
      (fun A1 Δ : duration =>
       \sum_(tsk_o <- ts | tsk_o != tsk)
          @task_request_bound_function Task H H2 tsk_o
            (minn
               (ssrint.absz
                  (@order.Order.max ssrnum.ring_display
                     (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
                        ssrint.ssrint_int__canonical__Num_POrderedZmodule)
                     (@ssralg.GRing.zero
                        (ssrnum.Num.POrderedZmodule.Exports.Num_POrderedZmodule__to__GRing_Nmodule
                           ssrint.ssrint_int__canonical__Num_POrderedZmodule))
                     ((fun (tsk_o0 : Equality.sort Task) (A2 : instant) =>
                       @ssralg.GRing.add
                         (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                            ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                         (@ssralg.GRing.add
                            (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                               ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                            (@ssralg.GRing.natmul
                               (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                  ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                               (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) 
                               (A2 + 1))
                            (@gel.task_priority_point Task H5 tsk))
                         (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
                            (@gel.task_priority_point Task H5 tsk_o0)))
                        tsk_o A1)))
               Δ))
        A0 R0)
       A (A + F) <=
     A + F) /\
  is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)

correct_search_space is not universe polymorphic
Arguments correct_search_space {Task H H0 H2 H5} ts%seq_scope H_valid_arrival_curve 
  tsk H_tsk_in_ts priority_inversion_bound%function_scope L H_L_positive R H_R_is_maximum%function_scope
  H_task_cost_pos H_arrival_curve_pos A%nat_scope _
correct_search_space is opaque
Expands to: Constant prosa.results.rta.ideal.gel.bounded_pi.correct_search_space
Declared in library prosa.results.rta.ideal.gel.bounded_pi, line 359, characters 14-34
@correct_search_space
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task)
         (H2 : MaxArrivals Task) (H5 : gel.PriorityPoint Task) (ts : seq (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H2) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall (priority_inversion_bound : duration -> duration) (L : duration),
       is_true (0 < L) ->
       forall R : duration,
       (forall A : duration,
        is_true (@is_in_search_space Task H H2 H5 ts tsk priority_inversion_bound L A) ->
        exists F : duration,
          is_true
            (priority_inversion_bound A +
             (@task_request_bound_function Task H H2 tsk (A + 1) -
              (@task_cost Task H tsk - @task_rtct Task H0 tsk)) +
             \sum_(tsk_o <- ts | tsk_o != tsk)
                @task_request_bound_function Task H H2 tsk_o
                  (minn
                     (ssrint.absz
                        (@order.Order.max ssrnum.ring_display
                           (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
                              ssrint.ssrint_int__canonical__Num_POrderedZmodule)
                           (@ssralg.GRing.zero
                              (ssrnum.Num.POrderedZmodule.Exports.Num_POrderedZmodule__to__GRing_Nmodule
                                 ssrint.ssrint_int__canonical__Num_POrderedZmodule))
                           (@ssralg.GRing.add
                              (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                 ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                              (@ssralg.GRing.add
                                 (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                    ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                                 (@ssralg.GRing.natmul
                                    (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                       ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                                    (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) 
                                    (A + 1))
                                 (@gel.task_priority_point Task H5 tsk))
                              (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
                                 (@gel.task_priority_point Task H5 tsk_o)))))
                     (A + F)) <=
             A + F) /\
          is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
       is_true (0 < @task_cost Task H tsk) ->
       is_true (0 < @max_arrivals Task H2 tsk 1) ->
       forall A : nat,
       search_space.is_in_search_space L
         (fun A0 Δ : duration =>
          @task_request_bound_function Task H H2 tsk (A0 + 1) - @task_cost Task H tsk +
          (priority_inversion_bound A0 +
           \sum_(tsk_o <- ts | tsk_o != tsk)
              @task_request_bound_function Task H H2 tsk_o
                (minn
                   (ssrint.absz
                      (@order.Order.max ssrnum.ring_display
                         (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
                            ssrint.ssrint_int__canonical__Num_POrderedZmodule)
                         (@ssralg.GRing.zero
                            (ssrnum.Num.POrderedZmodule.Exports.Num_POrderedZmodule__to__GRing_Nmodule
                               ssrint.ssrint_int__canonical__Num_POrderedZmodule))
                         (@ssralg.GRing.add
                            (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                               ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                            (@ssralg.GRing.add
                               (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                  ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                               (@ssralg.GRing.natmul
                                  (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                     ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                                  (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) 
                                  (A0 + 1))
                               (@gel.task_priority_point Task H5 tsk))
                            (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
                               (@gel.task_priority_point Task H5 tsk_o)))))
                   Δ)))
         A ->
       exists F : nat,
         is_true
           (@task_request_bound_function Task H H2 tsk (A + 1) -
            (@task_cost Task H tsk - @task_rtct Task H0 tsk) +
            (priority_inversion_bound A +
             \sum_(tsk_o <- ts | tsk_o != tsk)
                @task_request_bound_function Task H H2 tsk_o
                  (minn
                     (ssrint.absz
                        (@order.Order.max ssrnum.ring_display
                           (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
                              ssrint.ssrint_int__canonical__Num_POrderedZmodule)
                           (@ssralg.GRing.zero
                              (ssrnum.Num.POrderedZmodule.Exports.Num_POrderedZmodule__to__GRing_Nmodule
                                 ssrint.ssrint_int__canonical__Num_POrderedZmodule))
                           (@ssralg.GRing.add
                              (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                 ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                              (@ssralg.GRing.add
                                 (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                    ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                                 (@ssralg.GRing.natmul
                                    (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                       ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                                    (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) 
                                    (A + 1))
                                 (@gel.task_priority_point Task H5 tsk))
                              (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
                                 (@gel.task_priority_point Task H5 tsk_o)))))
                     (A + F))) <=
            A + F) /\
         is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Gel.BoundedPi.correct_search_space : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [inst_4 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  (ts : List Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (priority_inversion_bound : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration)
          (L : Prosa.Behavior.Time.duration),
          0 < L →
            ∀ (R : Prosa.Behavior.Time.duration),
              (∀ (A : Prosa.Behavior.Time.duration),
                  Prosa.Results.Rta.Ideal.Gel.BoundedPi.is_in_search_space ts tsk priority_inversion_bound L A = true →
                    ∃ F,
                      (priority_inversion_bound A +
                              (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1) -
                                (Prosa.Model.Task.Concept.task_cost tsk -
                                  Prosa.Model.Task.Preemption.Parameters.task_rtct tsk)) +
                            Prosa.Util.Sum.sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk)) fun tsk_o =>
                              Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk_o
                                (min
                                  (max 0
                                      (↑(A + 1) + Prosa.Model.Priority.Gel.task_priority_point tsk -
                                        Prosa.Model.Priority.Gel.task_priority_point tsk_o)).natAbs
                                  (A + F))) ≤
                          A + F ∧
                        F +
                            (Prosa.Model.Task.Concept.task_cost tsk -
                              Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                          R) →
                0 < Prosa.Model.Task.Concept.task_cost tsk →
                  0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
                    ∀ (A : ℕ),
                      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                          (fun A0 Δ =>
                            Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A0 + 1) -
                                Prosa.Model.Task.Concept.task_cost tsk +
                              (priority_inversion_bound A0 +
                                Prosa.Util.Sum.sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk)) fun tsk_o =>
                                  Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk_o
                                    (min
                                      (max 0
                                          (↑(A0 + 1) + Prosa.Model.Priority.Gel.task_priority_point tsk -
                                            Prosa.Model.Priority.Gel.task_priority_point tsk_o)).natAbs
                                      Δ)))
                          A →
                        ∃ F,
                          Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1) -
                                  (Prosa.Model.Task.Concept.task_cost tsk -
                                    Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) +
                                (priority_inversion_bound A +
                                  Prosa.Util.Sum.sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk)) fun tsk_o =>
                                    Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk_o
                                      (min
                                        (max 0
                                            (↑(A + 1) + Prosa.Model.Priority.Gel.task_priority_point tsk -
                                              Prosa.Model.Priority.Gel.task_priority_point tsk_o)).natAbs
                                        (A + F))) ≤
                              A + F ∧
                            F +
                                (Prosa.Model.Task.Concept.task_cost tsk -
                                  Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                              R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Gel_BoundedPi_correct_search_space
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
            inst_3)
         (inst_16 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_19 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (ts : List Task),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_16) ->
       forall tsk : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3)
               tsk ts))
         Bool_true ->
       forall (priority_inversion_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
         (L : Prosa_Behavior_Time_duration),
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Prosa_Behavior_Time_duration,
        @eq Bool
          (Prosa_Results_Rta_Ideal_Gel_BoundedPi_is_in_search_space Task
             inst_3
             inst_10
             inst_16
             inst_19 ts tsk
             priority_inversion_bound L A)
          Bool_true ->
        Exists Prosa_Behavior_Time_duration
          (fun F : Prosa_Behavior_Time_duration =>
           And
             (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                   (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                      (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) (priority_inversion_bound A)
                      (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                         (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                            inst_3
                            inst_10
                            inst_16 tsk
                            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                               Prosa_Behavior_Time_duration
                               (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                               (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                         (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                            Prosa_Behavior_Time_duration
                            (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                               inst_3
                               inst_10
                               tsk)
                            (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct
                               Task
                               inst_3
                               inst_13
                               tsk))))
                   (Prosa_Util_Sum_sumFiltered Task ts
                      (fun tsk_o : Task =>
                       Decidable_decide (Ne Task tsk_o tsk)
                         (instDecidableNot (@eq Task tsk_o tsk)
                            (inst_3 tsk_o
                               tsk)))
                      (fun tsk_o : Task =>
                       Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                         inst_3
                         inst_10
                         inst_16 tsk_o
                         (Min_min_inst1 Prosa_Behavior_Time_duration instMinNat
                            (Int_natAbs
                               (Max_max_inst1 Int Int_instMax (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
                                  (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int
                                     (instHSub_inst1 Int Int_instSub)
                                     (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int
                                        (instHAdd_inst1 Int Int_instAdd)
                                        (Nat_cast_inst1 Int instNatCastInt
                                           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat
                                              Prosa_Behavior_Time_duration
                                              (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                                              (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                                        (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                                           inst_3
                                           inst_19
                                           tsk))
                                     (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                                        inst_3
                                        inst_19
                                        tsk_o))))
                            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                               Prosa_Behavior_Time_duration
                               (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F)))))
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F))
             (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) F
                   (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                      Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                      (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                         inst_3
                         inst_10 tsk)
                      (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                         inst_3
                         inst_13 tsk)))
                R))) ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_3
            inst_10 tsk) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_16 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))) ->
       forall A : Nat,
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
         (fun A0 _UU0394_ : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
            (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
               (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                  inst_3
                  inst_10
                  inst_16 tsk
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A0
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
               (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                  inst_3
                  inst_10 tsk))
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
               (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) (priority_inversion_bound A0)
               (Prosa_Util_Sum_sumFiltered Task ts
                  (fun tsk_o : Task =>
                   Decidable_decide (Ne Task tsk_o tsk)
                     (instDecidableNot (@eq Task tsk_o tsk)
                        (inst_3 tsk_o tsk)))
                  (fun tsk_o : Task =>
                   Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                     inst_3
                     inst_10
                     inst_16 tsk_o
                     (Min_min_inst1 Prosa_Behavior_Time_duration instMinNat
                        (Int_natAbs
                           (Max_max_inst1 Int Int_instMax (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
                              (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int
                                 (instHSub_inst1 Int Int_instSub)
                                 (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int
                                    (instHAdd_inst1 Int Int_instAdd)
                                    (Nat_cast_inst1 Int instNatCastInt
                                       (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat
                                          Prosa_Behavior_Time_duration
                                          (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A0
                                          (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                                    (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                                       inst_3
                                       inst_19
                                       tsk))
                                 (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                                    inst_3
                                    inst_19
                                    tsk_o))))
                        _UU0394_)))))
         A ->
       Exists Nat
         (fun F : Nat =>
          And
            (LE_le_inst1 Nat instLENat
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                  (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                     (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                        inst_3
                        inst_10
                        inst_16 tsk
                        (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                           A (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                     (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                        Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                        (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                           inst_3
                           inst_10 tsk)
                        (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                           inst_3
                           inst_13 tsk)))
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                     (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) (priority_inversion_bound A)
                     (Prosa_Util_Sum_sumFiltered Task ts
                        (fun tsk_o : Task =>
                         Decidable_decide (Ne Task tsk_o tsk)
                           (instDecidableNot (@eq Task tsk_o tsk)
                              (inst_3
                                 tsk_o tsk)))
                        (fun tsk_o : Task =>
                         Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                           inst_3
                           inst_10
                           inst_16 tsk_o
                           (Min_min_inst1 Prosa_Behavior_Time_duration instMinNat
                              (Int_natAbs
                                 (Max_max_inst1 Int Int_instMax (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
                                    (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int
                                       (instHSub_inst1 Int Int_instSub)
                                       (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int
                                          (instHAdd_inst1 Int Int_instAdd)
                                          (Nat_cast_inst1 Int instNatCastInt
                                             (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A
                                                (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                                          (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                                             inst_3
                                             inst_19
                                             tsk))
                                       (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                                          inst_3
                                          inst_19
                                          tsk_o))))
                              (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A F))))))
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A F))
            (LE_le_inst1 Nat instLENat
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) F
                  (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                     Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                     (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                        inst_3
                        inst_10 tsk)
                     (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                        inst_3
                        inst_13 tsk)))
               R))
```
