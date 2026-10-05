# `correct_search_space`

- Kind (Rocq): Corollary
- Rocq: `prosa.results.rta.ideal.edf.bounded_pi.correct_search_space`
- Lean: `Prosa.Results.Rta.Ideal.Edf.BoundedPi.correct_search_space`
- Certificate: `correct_search_space_correspondence`

## Official Rocq

```coq
correct_search_space :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskDeadline Task}
  {H1 : TaskRunToCompletionThreshold Task} (ts : seq (Equality.sort Task)) {H5 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H5) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall (priority_inversion_bound : duration -> duration) (L : duration),
is_true (0 < L) ->
L = @total_request_bound_function Task H H5 ts L ->
forall R : duration,
(forall A : duration,
 is_true (@is_in_search_space Task H H0 ts H5 tsk priority_inversion_bound L A) ->
 exists F : duration,
   is_true
     (priority_inversion_bound A +
      (@task_request_bound_function Task H H5 tsk (A + 1) - (@task_cost Task H tsk - @task_rtct Task H1 tsk)) +
      @bound_on_athep_workload Task H H0 H5 ts tsk A (A + F) <= A + F) /\
   is_true (F + (@task_cost Task H tsk - @task_rtct Task H1 tsk) <= R)) ->
is_true (0 < @task_cost Task H tsk) ->
is_true (0 < @max_arrivals Task H5 tsk 1) ->
forall A : duration,
search_space.is_in_search_space L
  (fun A0 Δ : duration =>
   @task_request_bound_function Task H H5 tsk (A0 + 1) - @task_cost Task H tsk +
   (fun A1 R0 : duration => priority_inversion_bound A1 + @bound_on_athep_workload Task H H0 H5 ts tsk A1 R0)
     A0 Δ)
  A ->
exists F : nat,
  is_true
    (@task_request_bound_function Task H H5 tsk (A + 1) - (@task_cost Task H tsk - @task_rtct Task H1 tsk) +
     (fun A0 R0 : duration =>
      priority_inversion_bound A0 + @bound_on_athep_workload Task H H0 H5 ts tsk A0 R0) A 
       (A + F) <=
     A + F) /\
  is_true (F + (@task_cost Task H tsk - @task_rtct Task H1 tsk) <= R)

correct_search_space is not universe polymorphic
Arguments correct_search_space {Task H H0 H1} ts%seq_scope {H5} H_valid_arrival_curve 
  tsk H_tsk_in_ts priority_inversion_bound%function_scope L H_L_positive H_fixed_point 
  R H_R_is_maximum%function_scope H_task_cost_pos H_arrival_curve_pos A H_A_is_in_abstract_search_space
correct_search_space is opaque
Expands to: Constant prosa.results.rta.ideal.edf.bounded_pi.correct_search_space
Declared in library prosa.results.rta.ideal.edf.bounded_pi, line 304, characters 14-34
@correct_search_space
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task)
         (H1 : TaskRunToCompletionThreshold Task) (ts : seq (Equality.sort Task)) 
         (H5 : MaxArrivals Task),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H5) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall (priority_inversion_bound : duration -> duration) (L : duration),
       is_true (0 < L) ->
       L = @total_request_bound_function Task H H5 ts L ->
       forall R : duration,
       (forall A : duration,
        is_true (@is_in_search_space Task H H0 ts H5 tsk priority_inversion_bound L A) ->
        exists F : duration,
          is_true
            (priority_inversion_bound A +
             (@task_request_bound_function Task H H5 tsk (A + 1) -
              (@task_cost Task H tsk - @task_rtct Task H1 tsk)) +
             @bound_on_athep_workload Task H H0 H5 ts tsk A (A + F) <= A + F) /\
          is_true (F + (@task_cost Task H tsk - @task_rtct Task H1 tsk) <= R)) ->
       is_true (0 < @task_cost Task H tsk) ->
       is_true (0 < @max_arrivals Task H5 tsk 1) ->
       forall A : duration,
       search_space.is_in_search_space L
         (fun A0 Δ : duration =>
          @task_request_bound_function Task H H5 tsk (A0 + 1) - @task_cost Task H tsk +
          (priority_inversion_bound A0 + @bound_on_athep_workload Task H H0 H5 ts tsk A0 Δ))
         A ->
       exists F : nat,
         is_true
           (@task_request_bound_function Task H H5 tsk (A + 1) -
            (@task_cost Task H tsk - @task_rtct Task H1 tsk) +
            (priority_inversion_bound A + @bound_on_athep_workload Task H H0 H5 ts tsk A (A + F)) <= 
            A + F) /\
         is_true (F + (@task_cost Task H tsk - @task_rtct Task H1 tsk) <= R)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Edf.BoundedPi.correct_search_space : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskDeadline Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] (ts : List Task)
  [inst_4 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (priority_inversion_bound : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration)
          (L : Prosa.Behavior.Time.duration),
          0 < L →
            L = Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts L →
              ∀ (R : Prosa.Behavior.Time.duration),
                (∀ (A : Prosa.Behavior.Time.duration),
                    Prosa.Results.Rta.Ideal.Edf.BoundedPi.is_in_search_space ts tsk priority_inversion_bound L A =
                        true →
                      ∃ F,
                        priority_inversion_bound A +
                                (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk
                                    (A + 1) -
                                  (Prosa.Model.Task.Concept.task_cost tsk -
                                    Prosa.Model.Task.Preemption.Parameters.task_rtct tsk)) +
                              Prosa.Analysis.Definitions.Workload.EdfAthepBound.bound_on_athep_workload ts tsk A
                                (A + F) ≤
                            A + F ∧
                          F +
                              (Prosa.Model.Task.Concept.task_cost tsk -
                                Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                            R) →
                  0 < Prosa.Model.Task.Concept.task_cost tsk →
                    0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
                      ∀ (A : Prosa.Behavior.Time.duration),
                        Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                            (fun A0 Δ =>
                              Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A0 + 1) -
                                  Prosa.Model.Task.Concept.task_cost tsk +
                                (priority_inversion_bound A0 +
                                  Prosa.Analysis.Definitions.Workload.EdfAthepBound.bound_on_athep_workload ts tsk A0
                                    Δ))
                            A →
                          ∃ F,
                            Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1) -
                                    (Prosa.Model.Task.Concept.task_cost tsk -
                                      Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) +
                                  (priority_inversion_bound A +
                                    Prosa.Analysis.Definitions.Workload.EdfAthepBound.bound_on_athep_workload ts tsk A
                                      (A + F)) ≤
                                A + F ∧
                              F +
                                  (Prosa.Model.Task.Concept.task_cost tsk -
                                    Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                                R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Edf_BoundedPi_correct_search_space
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_3)
         (inst_16 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
            inst_3)
         (ts : List Task)
         (inst_21 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_21) ->
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
       @eq Prosa_Behavior_Time_duration L
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
            inst_3
            inst_10
            inst_21 ts L) ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Prosa_Behavior_Time_duration,
        @eq Bool
          (Prosa_Results_Rta_Ideal_Edf_BoundedPi_is_in_search_space Task
             inst_3
             inst_10
             inst_13 ts
             inst_21 tsk
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
                            inst_21 tsk
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
                               inst_16
                               tsk))))
                   (Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload Task
                      inst_3
                      inst_10
                      inst_13
                      inst_21 ts tsk A
                      (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                         Prosa_Behavior_Time_duration
                         (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F)))
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
                         inst_16 tsk)))
                R))) ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_3
            inst_10 tsk) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_21 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))) ->
       forall A : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
         (fun A0 _UU0394_ : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
            (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
               (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                  inst_3
                  inst_10
                  inst_21 tsk
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A0
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
               (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                  inst_3
                  inst_10 tsk))
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
               (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) (priority_inversion_bound A0)
               (Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload Task
                  inst_3
                  inst_10
                  inst_13
                  inst_21 ts tsk A0
                  _UU0394_)))
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
                        inst_21 tsk
                        (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                           Prosa_Behavior_Time_duration
                           (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                           (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                     (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                        Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                        (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                           inst_3
                           inst_10 tsk)
                        (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                           inst_3
                           inst_16 tsk)))
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                     (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) (priority_inversion_bound A)
                     (Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload Task
                        inst_3
                        inst_10
                        inst_13
                        inst_21 ts tsk A
                        (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                           (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F))))
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                  (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F))
            (LE_le_inst1 Nat instLENat
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) F
                  (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                     Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                     (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                        inst_3
                        inst_10 tsk)
                     (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                        inst_3
                        inst_16 tsk)))
               R))
```
