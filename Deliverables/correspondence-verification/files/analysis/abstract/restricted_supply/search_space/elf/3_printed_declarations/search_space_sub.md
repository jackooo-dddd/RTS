# `search_space_sub`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.search_space.elf.search_space_sub`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Elf.search_space_sub`
- Certificate: `search_space_sub_correspondence`

## Official Rocq

```coq
search_space_sub :
forall {Task : TaskType} {H : TaskCost Task} {H1 : TaskMaxNonpreemptiveSegment Task}
  {H2 : PriorityPoint Task} (ts : seq (Equality.sort Task)) {H3 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H3) ->
forall {FP : FP_policy Task} (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall L : duration,
is_true (0 < L) ->
is_true (0 < @task_cost Task H tsk) ->
is_true (0 < @max_arrivals Task H3 tsk 1) ->
forall A : nat,
search_space.is_in_search_space L
  (fun A0 F : duration =>
   @task_request_bound_function Task H H3 tsk (A0 + 1) - @task_cost Task H tsk +
   (@blocking_bound Task H H1 H2 ts H3 FP tsk A0 + @bound_on_athep_workload Task H H3 H2 ts FP tsk A0 F))
  A ->
is_true (@is_in_search_space Task H H1 H2 ts H3 FP tsk L A)

search_space_sub is not universe polymorphic
Arguments search_space_sub {Task H H1 H2} ts%seq_scope {H3} H_valid_arrival_curve 
  {FP} tsk H_tsk_in_ts L H_L_positive H_task_cost_pos H_arrival_curve_pos A%nat_scope 
  _
search_space_sub is opaque
Expands to: Constant prosa.analysis.abstract.restricted_supply.search_space.elf.search_space_sub
Declared in library prosa.analysis.abstract.restricted_supply.search_space.elf, line 94, characters 8-24
@search_space_sub
     : forall (Task : TaskType) (H : TaskCost Task) (H1 : TaskMaxNonpreemptiveSegment Task)
         (H2 : PriorityPoint Task) (ts : seq (Equality.sort Task)) (H3 : MaxArrivals Task),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H3) ->
       forall (FP : FP_policy Task) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall L : duration,
       is_true (0 < L) ->
       is_true (0 < @task_cost Task H tsk) ->
       is_true (0 < @max_arrivals Task H3 tsk 1) ->
       forall A : nat,
       search_space.is_in_search_space L
         (fun A0 F : duration =>
          @task_request_bound_function Task H H3 tsk (A0 + 1) - @task_cost Task H tsk +
          (@blocking_bound Task H H1 H2 ts H3 FP tsk A0 +
           @bound_on_athep_workload Task H H3 H2 ts FP tsk A0 F))
         A ->
       is_true (@is_in_search_space Task H H1 H2 ts H3 FP tsk L A)
New coercion path [GRing.subring_closedM; GRing.smulr_closedN] : GRing.subring_closed >-> GRing.oppr_closed is ambiguous with existing 
New coercion path [GRing.subring_closed_semi; GRing.semiring_closedM] : GRing.subring_closed >-> GRing.mulr_closed is ambiguous with existing 
New coercion path [GRing.subring_closed_semi; GRing.semiring_closedD] : GRing.subring_closed >-> GRing.addr_closed is ambiguous with existing 
New coercion path [GRing.submod_closed_semi; GRing.subsemimod_closedD] : GRing.submod_closed >-> GRing.addr_closed is ambiguous with existing 
New coercion path [GRing.subalg_closedBM; GRing.subring_closedB] : GRing.subalg_closed >-> GRing.zmod_closed is ambiguous with existing 
New coercion path [GRing.sdivr_closedM; GRing.smulr_closedM] : GRing.sdivr_closed >-> GRing.mulr_closed is ambiguous with existing 
New coercion path [GRing.divring_closed_div; GRing.sdivr_closedM] : GRing.divring_closed >-> GRing.smulr_closed is ambiguous with existing 
New coercion path [GRing.divalg_closedZ; GRing.subalg_closedBM] : GRing.divalg_closed >-> GRing.subring_closed is ambiguous with existing
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Elf.search_space_sub : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
  [inst_3 : Prosa.Model.Priority.Gel.PriorityPoint Task] (ts : List Task)
  [inst_4 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (L : Prosa.Behavior.Time.duration),
          0 < L →
            0 < Prosa.Model.Task.Concept.task_cost tsk →
              0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
                ∀ (A : ℕ),
                  Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                      (fun A0 F =>
                        Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A0 + 1) -
                            Prosa.Model.Task.Concept.task_cost tsk +
                          (Prosa.Analysis.Definitions.BlockingBound.Elf.blocking_bound ts tsk A0 +
                            Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_athep_workload ts tsk A0 F))
                      A →
                    Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Elf.is_in_search_space ts tsk L A = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Elf_search_space_sub
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_3)
         (inst_12 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (ts : List Task)
         (inst_17 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_17) ->
       forall
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
            inst_3
            inst_6 tsk) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_17 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))) ->
       forall A : Nat,
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
         (fun A0 F : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
               (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                  inst_3
                  inst_6
                  inst_17
                  tsk
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A0
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
               (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                  inst_3
                  inst_6
                  tsk))
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
               (Prosa_Analysis_Definitions_BlockingBound_Elf_blocking_bound Task
                  inst_3
                  inst_6
                  inst_9
                  inst_12
                  ts
                  inst_17
                  FP tsk A0)
               (Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_athep_workload Task
                  inst_3
                  inst_6
                  inst_17
                  inst_12
                  ts FP tsk A0 F)))
         A ->
       @eq Bool
         (Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Elf_is_in_search_space Task
            inst_3
            inst_6
            inst_9
            inst_12 ts
            inst_17 FP
            tsk L A)
         Bool_true
```
