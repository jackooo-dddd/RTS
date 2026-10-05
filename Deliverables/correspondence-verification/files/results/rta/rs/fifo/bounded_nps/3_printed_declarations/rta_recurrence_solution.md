# `rta_recurrence_solution`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.rs.fifo.bounded_nps.rta_recurrence_solution`
- Lean: `Prosa.Results.Rta.Rs.Fifo.BoundedNps.rta_recurrence_solution`
- Certificate: `rta_recurrence_solution_correspondence`

## Official Rocq

```coq
rta_recurrence_solution :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task -> seq (Equality.sort Task) -> SupplyBoundFunction -> duration -> nat -> Prop

rta_recurrence_solution is not universe polymorphic
Arguments rta_recurrence_solution {Task H H0} ts%seq_scope {SBF} L R%nat_scope
rta_recurrence_solution is transparent
Expands to: Constant prosa.results.rta.rs.fifo.bounded_nps.rta_recurrence_solution
Declared in library prosa.results.rta.rs.fifo.bounded_nps, line 171, characters 13-36
@rta_recurrence_solution
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task -> seq (Equality.sort Task) -> SupplyBoundFunction -> duration -> nat -> Prop
```

Body:

```coq
rta_recurrence_solution =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (ts : seq (Equality.sort Task))
  (SBF : SupplyBoundFunction) (L : duration) (R : nat) =>
forall A : duration,
is_true (@is_in_search_space Task H ts H0 L A) ->
exists F : duration,
  is_true (@total_request_bound_function Task H H0 ts (A + 1) <= SBF F) /\ is_true (F <= A + R)
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task -> seq (Equality.sort Task) -> SupplyBoundFunction -> duration -> nat -> Prop

Arguments rta_recurrence_solution {Task H H0} ts%seq_scope {SBF} L R%nat_scope
```

## Lean

```lean
@Prosa.Results.Rta.Rs.Fifo.BoundedNps.rta_recurrence_solution : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction → Prosa.Behavior.Time.duration → ℕ → Prop
```

Body:

```lean
def Prosa.Results.Rta.Rs.Fifo.BoundedNps.rta_recurrence_solution.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task → Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction → Prosa.Behavior.Time.duration → ℕ → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts SBF L R =>
  ∀ (A : Prosa.Behavior.Time.duration),
    Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo.is_in_search_space ts L A = true →
      ∃ F,
        Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts (A + 1) ≤
            Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function F ∧
          F ≤ A + R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Rs_Fifo_BoundedNps_rta_recurrence_solution
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> Prosa_Behavior_Time_duration -> Nat -> SProp
```

Body:

```coq
Prosa_Results_Rta_Rs_Fifo_BoundedNps_rta_recurrence_solution@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
  (inst_9 : Prosa_Model_Task_Arrival_Curves_MaxArrivals
                                                                                Task
                                                                                inst_3)
  (ts : List Task) (SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction)
  (L : Prosa_Behavior_Time_duration) (R : Nat) =>
forall A : Prosa_Behavior_Time_duration,
@eq Bool
  (Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Fifo_is_in_search_space Task
     inst_3
     inst_6 ts
     inst_9 L A)
  Bool_true ->
Exists Prosa_Behavior_Time_duration
  (fun F : Prosa_Behavior_Time_duration =>
   And
     (LE_le_inst1 Nat instLENat
        (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
           inst_3
           inst_6
           inst_9 ts
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
              Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
              (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
        (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F))
     (LE_le_inst1 Prosa_Behavior_Time_duration instLENat F
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
           (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> Prosa_Behavior_Time_duration -> Nat -> SProp

Arguments Prosa_Results_Rta_Rs_Fifo_BoundedNps_rta_recurrence_solution Task
  inst_3
  inst_6
  inst_9 ts SBF 
  L x____at___Init_Prelude3715277255__hygCtx13_Init_Prelude3715277255__hygCtx__hyg24%_Nat_scope
```
