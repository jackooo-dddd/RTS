# `response_time_recurrence_solution_exists`

- Kind (Rocq): Corollary
- Rocq: `prosa.results.rta.ideal.elf.bounded_pi.response_time_recurrence_solution_exists`
- Lean: `Prosa.Results.Rta.Ideal.Elf.BoundedPi.response_time_recurrence_solution_exists`
- Certificate: `response_time_recurrence_solution_exists_correspondence`

## Official Rocq

```coq
response_time_recurrence_solution_exists :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {H2 : MaxArrivals Task} {H3 : PriorityPoint Task} (ts : seq (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H2) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall (FP : FP_policy Task) (priority_inversion_lp_tasks_bound : duration)
  (priority_inversion_ep_tasks_bound : duration -> duration) (L : duration),
is_true (0 < L) ->
forall R : duration,
(forall A : duration,
 is_true
   (@is_in_search_space Task H H2 H3 ts tsk FP priority_inversion_lp_tasks_bound
      priority_inversion_ep_tasks_bound L A) ->
 exists F : duration,
   is_true
     (priority_inversion_bound priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A +
      @bound_on_total_ep_workload Task H H2 H3 ts tsk FP A (A + F) +
      @total_hp_rbf Task H H2 ts tsk FP (A + F) +
      (@task_request_bound_function Task H H2 tsk (A + 1) - (@task_cost Task H tsk - @task_rtct Task H0 tsk)) <=
      A + F) /\
   is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
is_true (0 < @task_cost Task H tsk) ->
is_true (0 < @max_arrivals Task H2 tsk 1) ->
forall A : nat,
search_space.is_in_search_space L
  (fun A0 Δ : duration =>
   @task_request_bound_function Task H H2 tsk (A0 + 1) - @task_cost Task H tsk +
   @task_IBF Task H H2 H3 ts tsk FP priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A0 Δ)
  A ->
exists F : nat,
  is_true
    (@task_request_bound_function Task H H2 tsk (A + 1) - (@task_cost Task H tsk - @task_rtct Task H0 tsk) +
     @task_IBF Task H H2 H3 ts tsk FP priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A
       (A + F) <=
     A + F) /\
  is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)

response_time_recurrence_solution_exists is not universe polymorphic
Arguments response_time_recurrence_solution_exists {Task H H0 H2 H3} ts%seq_scope 
  H_valid_arrival_curve tsk H_tsk_in_ts FP priority_inversion_lp_tasks_bound
  priority_inversion_ep_tasks_bound%function_scope L H_L_positive R H_R_is_maximum%function_scope
  H_task_cost_pos H_arrival_curve_pos A%nat_scope _
response_time_recurrence_solution_exists is opaque
Expands to: Constant prosa.results.rta.ideal.elf.bounded_pi.response_time_recurrence_solution_exists
Declared in library prosa.results.rta.ideal.elf.bounded_pi, line 648, characters 14-54
@response_time_recurrence_solution_exists
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task)
         (H2 : MaxArrivals Task) (H3 : PriorityPoint Task) (ts : seq (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H2) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall (FP : FP_policy Task) (priority_inversion_lp_tasks_bound : duration)
         (priority_inversion_ep_tasks_bound : duration -> duration) (L : duration),
       is_true (0 < L) ->
       forall R : duration,
       (forall A : duration,
        is_true
          (@is_in_search_space Task H H2 H3 ts tsk FP priority_inversion_lp_tasks_bound
             priority_inversion_ep_tasks_bound L A) ->
        exists F : duration,
          is_true
            (priority_inversion_bound priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A +
             @bound_on_total_ep_workload Task H H2 H3 ts tsk FP A (A + F) +
             @total_hp_rbf Task H H2 ts tsk FP (A + F) +
             (@task_request_bound_function Task H H2 tsk (A + 1) -
              (@task_cost Task H tsk - @task_rtct Task H0 tsk)) <=
             A + F) /\
          is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
       is_true (0 < @task_cost Task H tsk) ->
       is_true (0 < @max_arrivals Task H2 tsk 1) ->
       forall A : nat,
       search_space.is_in_search_space L
         (fun A0 Δ : duration =>
          @task_request_bound_function Task H H2 tsk (A0 + 1) - @task_cost Task H tsk +
          @task_IBF Task H H2 H3 ts tsk FP priority_inversion_lp_tasks_bound
            priority_inversion_ep_tasks_bound A0 Δ)
         A ->
       exists F : nat,
         is_true
           (@task_request_bound_function Task H H2 tsk (A + 1) -
            (@task_cost Task H tsk - @task_rtct Task H0 tsk) +
            @task_IBF Task H H2 H3 ts tsk FP priority_inversion_lp_tasks_bound
              priority_inversion_ep_tasks_bound A (A + F) <=
            A + F) /\
         is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Elf.BoundedPi.response_time_recurrence_solution_exists : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [inst_4 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  (ts : List Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task)
          (priority_inversion_lp_tasks_bound : Prosa.Behavior.Time.duration)
          (priority_inversion_ep_tasks_bound : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration)
          (L : Prosa.Behavior.Time.duration),
          0 < L →
            ∀ (R : Prosa.Behavior.Time.duration),
              (∀ (A : Prosa.Behavior.Time.duration),
                  Prosa.Results.Rta.Ideal.Elf.BoundedPi.is_in_search_space ts tsk FP priority_inversion_lp_tasks_bound
                        priority_inversion_ep_tasks_bound L A =
                      true →
                    ∃ F,
                      Prosa.Results.Rta.Ideal.Elf.BoundedPi.priority_inversion_bound priority_inversion_lp_tasks_bound
                                  priority_inversion_ep_tasks_bound A +
                                Prosa.Results.Rta.Ideal.Elf.BoundedPi.bound_on_total_ep_workload ts tsk FP A (A + F) +
                              Prosa.Results.Rta.Ideal.Elf.BoundedPi.total_hp_rbf ts tsk FP (A + F) +
                            (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1) -
                              (Prosa.Model.Task.Concept.task_cost tsk -
                                Prosa.Model.Task.Preemption.Parameters.task_rtct tsk)) ≤
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
                              Prosa.Results.Rta.Ideal.Elf.BoundedPi.task_IBF ts tsk FP priority_inversion_lp_tasks_bound
                                priority_inversion_ep_tasks_bound A0 Δ)
                          A →
                        ∃ F,
                          Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1) -
                                  (Prosa.Model.Task.Concept.task_cost tsk -
                                    Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) +
                                Prosa.Results.Rta.Ideal.Elf.BoundedPi.task_IBF ts tsk FP
                                  priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A (A + F) ≤
                              A + F ∧
                            F +
                                (Prosa.Model.Task.Concept.task_cost tsk -
                                  Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                              R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_response_time_recurrence_solution_exists
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
       forall
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (priority_inversion_lp_tasks_bound : Prosa_Behavior_Time_duration)
         (priority_inversion_ep_tasks_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
         (L : Prosa_Behavior_Time_duration),
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Prosa_Behavior_Time_duration,
        @eq Bool
          (Prosa_Results_Rta_Ideal_Elf_BoundedPi_is_in_search_space Task
             inst_3
             inst_10
             inst_16
             inst_19 ts tsk FP
             priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound L A)
          Bool_true ->
        Exists Prosa_Behavior_Time_duration
          (fun F : Prosa_Behavior_Time_duration =>
           And
             (LE_le_inst1 Nat instLENat
                (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                   (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                      (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                         (Prosa_Results_Rta_Ideal_Elf_BoundedPi_priority_inversion_bound
                            priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A)
                         (Prosa_Results_Rta_Ideal_Elf_BoundedPi_bound_on_total_ep_workload Task
                            inst_3
                            inst_10
                            inst_16
                            inst_19 ts
                            tsk FP A
                            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                               Prosa_Behavior_Time_duration
                               (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F)))
                      (Prosa_Results_Rta_Ideal_Elf_BoundedPi_total_hp_rbf Task
                         inst_3
                         inst_10
                         inst_16 ts tsk
                         FP
                         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                            Prosa_Behavior_Time_duration
                            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F)))
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
                            inst_10 tsk)
                         (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                            inst_3
                            inst_13 tsk))))
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
          HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
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
            (Prosa_Results_Rta_Ideal_Elf_BoundedPi_task_IBF Task
               inst_3
               inst_10
               inst_16
               inst_19 ts tsk FP
               priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A0 _UU0394_))
         A ->
       Exists Nat
         (fun F : Nat =>
          And
            (LE_le_inst1 Nat instLENat
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
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
                  (Prosa_Results_Rta_Ideal_Elf_BoundedPi_task_IBF Task
                     inst_3
                     inst_10
                     inst_16
                     inst_19 ts tsk FP
                     priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A
                     (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A F)))
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
