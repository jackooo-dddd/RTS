# `bound_on_total_ep_workload_changes_at`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload_changes_at`
- Lean: `Prosa.Results.Rta.Ideal.Elf.BoundedPi.bound_on_total_ep_workload_changes_at`
- Certificate: `bound_on_total_ep_workload_changes_at_correspondence`

## Official Rocq

```coq
bound_on_total_ep_workload_changes_at :
forall {Task : TaskType},
PriorityPoint Task -> seq (Equality.sort Task) -> Equality.sort Task -> FP_policy Task -> nat -> bool

bound_on_total_ep_workload_changes_at is not universe polymorphic
Arguments bound_on_total_ep_workload_changes_at {Task H3} ts%seq_scope tsk FP A%nat_scope
bound_on_total_ep_workload_changes_at is transparent
Expands to: Constant prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload_changes_at
Declared in library prosa.results.rta.ideal.elf.bounded_pi, line 553, characters 13-50
@bound_on_total_ep_workload_changes_at
     : forall Task : TaskType,
       PriorityPoint Task -> seq (Equality.sort Task) -> Equality.sort Task -> FP_policy Task -> nat -> bool
```

Body:

```coq
bound_on_total_ep_workload_changes_at =
fun (Task : TaskType) (H3 : PriorityPoint Task) (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task)
  (FP : FP_policy Task) (A : nat) =>
let any_task_bound_changes :=
  fun tsk_o : Equality.sort Task =>
  @ep_task Task FP tsk tsk_o && (tsk_o != tsk) &&
  (@ep_task_intf_interval Task H3 tsk tsk_o (A - 1) != @ep_task_intf_interval Task H3 tsk tsk_o A) in
@has (Equality.sort Task) any_task_bound_changes ts
     : forall {Task : TaskType},
       PriorityPoint Task -> seq (Equality.sort Task) -> Equality.sort Task -> FP_policy Task -> nat -> bool

Arguments bound_on_total_ep_workload_changes_at {Task H3} ts%seq_scope tsk FP A%nat_scope
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Elf.BoundedPi.bound_on_total_ep_workload_changes_at : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Priority.Gel.PriorityPoint Task] →
      List Task → Task → Prosa.Model.Priority.Definitions.FP_policy Task → ℕ → Bool
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Elf.BoundedPi.bound_on_total_ep_workload_changes_at.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Priority.Gel.PriorityPoint Task] →
      List Task → Task → Prosa.Model.Priority.Definitions.FP_policy Task → ℕ → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Priority.Gel.PriorityPoint Task] ts tsk FP A =>
  ts.any fun tsk_o =>
    Prosa.Model.Priority.Definitions.ep_task tsk tsk_o && decide (tsk_o ≠ tsk) &&
      decide
        (Prosa.Results.Rta.Ideal.Elf.BoundedPi.ep_task_intf_interval tsk tsk_o (A - 1) ≠
          Prosa.Results.Rta.Ideal.Elf.BoundedPi.ep_task_intf_interval tsk tsk_o A)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_bound_on_total_ep_workload_changes_at
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Nat -> Bool
```

Body:

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_bound_on_total_ep_workload_changes_at@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_10 : 
   Prosa_Model_Priority_Gel_PriorityPoint Task
     inst_3)
  (ts : List Task) (tsk : Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (A : Nat) =>
List_any Task ts
  (fun tsk_o : Task =>
   Bool_and
     (Bool_and
        (Prosa_Model_Priority_Definitions_ep_task Task
           inst_3 FP tsk tsk_o)
        (Decidable_decide (Ne Task tsk_o tsk)
           (instDecidableNot (@eq Task tsk_o tsk)
              (inst_3 tsk_o tsk))))
     (Decidable_decide
        (Ne Int
           (Prosa_Results_Rta_Ideal_Elf_BoundedPi_ep_task_intf_interval Task
              inst_3
              inst_10 tsk tsk_o
              (HSub_hSub_inst7 Nat Prosa_Behavior_Time_instant Nat (instHSub_inst1 Nat instSubNat) A
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
           (Prosa_Results_Rta_Ideal_Elf_BoundedPi_ep_task_intf_interval Task
              inst_3
              inst_10 tsk tsk_o A))
        (instDecidableNot
           (@eq Int
              (Prosa_Results_Rta_Ideal_Elf_BoundedPi_ep_task_intf_interval Task
                 inst_3
                 inst_10 tsk tsk_o
                 (HSub_hSub_inst7 Nat Prosa_Behavior_Time_instant Nat (instHSub_inst1 Nat instSubNat) A
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
              (Prosa_Results_Rta_Ideal_Elf_BoundedPi_ep_task_intf_interval Task
                 inst_3
                 inst_10 tsk tsk_o A))
           (Int_instDecidableEq
              (Prosa_Results_Rta_Ideal_Elf_BoundedPi_ep_task_intf_interval Task
                 inst_3
                 inst_10 tsk tsk_o
                 (HSub_hSub_inst7 Nat Prosa_Behavior_Time_instant Nat (instHSub_inst1 Nat instSubNat) A
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
              (Prosa_Results_Rta_Ideal_Elf_BoundedPi_ep_task_intf_interval Task
                 inst_3
                 inst_10 tsk tsk_o A)))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       List Task ->
       Task ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Nat -> Bool

Arguments Prosa_Results_Rta_Ideal_Elf_BoundedPi_bound_on_total_ep_workload_changes_at 
  Task inst_3
  inst_10 ts 
  tsk FP x____at___Init_Prelude2408276647__hygCtx__hyg14%_Nat_scope
```
