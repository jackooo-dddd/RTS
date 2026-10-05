# `A_is_in_concrete_search_space`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.fp.nonseq.bounded_pi.A_is_in_concrete_search_space`
- Lean: `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.A_is_in_concrete_search_space`
- Certificate: `A_is_in_concrete_search_space_correspondence`

## Official Rocq

```coq
A_is_in_concrete_search_space :
forall {Task : TaskType} {H : TaskCost Task} {MaxArrivals0 : MaxArrivals Task} {FP : FP_policy Task}
  (ts : seq (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task MaxArrivals0) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall priority_inversion_bound L : duration,
is_true (0 < L) ->
L = priority_inversion_bound + @total_hep_request_bound_function_FP Task H MaxArrivals0 ts FP tsk L ->
is_true (0 < @task_cost Task H tsk) ->
is_true (0 < @max_arrivals Task MaxArrivals0 tsk 1) ->
forall A : duration,
is_true (@is_in_concrete_search_space Task H MaxArrivals0 tsk L A)

A_is_in_concrete_search_space is not universe polymorphic
Arguments A_is_in_concrete_search_space {Task H MaxArrivals0 FP} ts%seq_scope H_valid_arrival_curve 
  tsk H_tsk_in_ts priority_inversion_bound L H_L_positive H_fixed_point H_task_cost_pos 
  H_arrival_curve_pos A H_A_is_in_abstract_search_space
A_is_in_concrete_search_space is opaque
Expands to: Constant prosa.results.rta.ideal.fp.nonseq.bounded_pi.A_is_in_concrete_search_space
Declared in library prosa.results.rta.ideal.fp.nonseq.bounded_pi, line 334, characters 10-39
@A_is_in_concrete_search_space
     : forall (Task : TaskType) (H : TaskCost Task) (MaxArrivals0 : MaxArrivals Task) 
         (FP : FP_policy Task) (ts : seq (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task MaxArrivals0) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall priority_inversion_bound L : duration,
       is_true (0 < L) ->
       L = priority_inversion_bound + @total_hep_request_bound_function_FP Task H MaxArrivals0 ts FP tsk L ->
       is_true (0 < @task_cost Task H tsk) ->
       is_true (0 < @max_arrivals Task MaxArrivals0 tsk 1) ->
       forall A : duration,
       is_in_search_space L (@IBF Task H MaxArrivals0 FP ts tsk priority_inversion_bound) A ->
       is_true (@is_in_concrete_search_space Task H MaxArrivals0 tsk L A)
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.A_is_in_concrete_search_space : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [FP : Prosa.Model.Priority.Definitions.FP_policy Task]
  (ts : List Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (priority_inversion_bound L : Prosa.Behavior.Time.duration),
          0 < L →
            L =
                priority_inversion_bound +
                  Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP ts tsk L →
              0 < Prosa.Model.Task.Concept.task_cost tsk →
                0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
                  ∀ (A : Prosa.Behavior.Time.duration),
                    Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                        (Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.IBF ts tsk priority_inversion_bound) A →
                      Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.is_in_concrete_search_space tsk L A = true
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_A_is_in_concrete_search_space
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (ts : List Task),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_13) ->
       forall tsk : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       forall priority_inversion_bound L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) priority_inversion_bound
            (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
               inst_3
               inst_10
               inst_13 ts FP tsk L)) ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_3
            inst_10 tsk) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_13 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))) ->
       forall A : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
         (Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_IBF Task
            inst_3
            inst_10
            inst_13 FP ts tsk
            priority_inversion_bound)
         A ->
       @eq Bool
         (Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_is_in_concrete_search_space Task
            inst_3
            inst_10
            inst_13 tsk L A)
         Bool_true
```
