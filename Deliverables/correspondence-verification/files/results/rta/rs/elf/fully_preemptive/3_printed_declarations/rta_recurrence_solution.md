# `rta_recurrence_solution`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.rs.elf.fully_preemptive.rta_recurrence_solution`
- Lean: `Prosa.Results.Rta.Rs.Elf.FullyPreemptive.rta_recurrence_solution`
- Certificate: `rta_recurrence_solution_correspondence`

## Official Rocq

```coq
rta_recurrence_solution :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task ->
PriorityPoint Task ->
seq (Equality.sort Task) ->
Equality.sort Task -> FP_policy Task -> SupplyBoundFunction -> duration -> nat -> Prop

rta_recurrence_solution is not universe polymorphic
Arguments rta_recurrence_solution {Task H H0 H1} ts%seq_scope tsk FP {SBF} L R%nat_scope
rta_recurrence_solution is transparent
Expands to: Constant prosa.results.rta.rs.elf.fully_preemptive.rta_recurrence_solution
Declared in library prosa.results.rta.rs.elf.fully_preemptive, line 173, characters 13-36
@rta_recurrence_solution
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       PriorityPoint Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task -> FP_policy Task -> SupplyBoundFunction -> duration -> nat -> Prop
```

Body:

```coq
rta_recurrence_solution =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (H1 : PriorityPoint Task)
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (FP : FP_policy Task)
  (SBF : SupplyBoundFunction) (L : duration) (R : nat) =>
forall A : duration,
is_true (@is_in_search_space Task H (@fully_preemptive_task_model Task) H1 ts H0 FP tsk L A) ->
exists F : duration,
  is_true
    (@task_request_bound_function Task H H0 tsk (A + 1) + @bound_on_athep_workload Task H H0 H1 ts FP tsk A F <=
     SBF F) /\
  is_true (F <= A + R)
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       PriorityPoint Task ->
       seq (Equality.sort Task) ->
       Equality.sort Task -> FP_policy Task -> SupplyBoundFunction -> duration -> nat -> Prop

Arguments rta_recurrence_solution {Task H H0 H1} ts%seq_scope tsk FP {SBF} L R%nat_scope
```

## Lean

```lean
@Prosa.Results.Rta.Rs.Elf.FullyPreemptive.rta_recurrence_solution : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          List Task →
            Task →
              [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
                Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction → Prosa.Behavior.Time.duration → ℕ → Prop
```

Body:

```lean
def Prosa.Results.Rta.Rs.Elf.FullyPreemptive.rta_recurrence_solution.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          List Task →
            Task →
              [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
                Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction → Prosa.Behavior.Time.duration → ℕ → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [Prosa.Model.Priority.Gel.PriorityPoint Task] ts tsk
    [Prosa.Model.Priority.Definitions.FP_policy Task] SBF L R =>
  ∀ (A : Prosa.Behavior.Time.duration),
    Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Elf.is_in_search_space ts tsk L A = true →
      ∃ F,
        Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1) +
              Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_athep_workload ts tsk A F ≤
            Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function F ∧
          F ≤ A + R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Rs_Elf_FullyPreemptive_rta_recurrence_solution
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> Prosa_Behavior_Time_duration -> Nat -> SProp
```

Body:

```coq
Prosa_Results_Rta_Rs_Elf_FullyPreemptive_rta_recurrence_solution@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (inst_12 : 
   Prosa_Model_Priority_Gel_PriorityPoint Task
     inst_3)
  (ts : List Task) (tsk : Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) (L : Prosa_Behavior_Time_duration) 
  (R : Nat) =>
forall A : Prosa_Behavior_Time_duration,
@eq Bool
  (Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Elf_is_in_search_space Task
     inst_3
     inst_6
     (Prosa_Model_Task_Preemption_FullyPreemptive_fully_preemptive_task_model Task
        inst_3)
     inst_12 ts
     inst_9 FP tsk L A)
  Bool_true ->
Exists Prosa_Behavior_Time_duration
  (fun F : Prosa_Behavior_Time_duration =>
   And
     (LE_le_inst1 Nat instLENat
        (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
           (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
              inst_3
              inst_6
              inst_9 tsk
              (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                 Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
           (Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_athep_workload Task
              inst_3
              inst_6
              inst_9
              inst_12 ts FP tsk A F))
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
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> Prosa_Behavior_Time_duration -> Nat -> SProp

Arguments Prosa_Results_Rta_Rs_Elf_FullyPreemptive_rta_recurrence_solution Task
  inst_3
  inst_6
  inst_9
  inst_12 ts 
  tsk FP SBF L x____at___Init_Prelude3715277255__hygCtx13_Init_Prelude3715277255__hygCtx__hyg24%_Nat_scope
```
