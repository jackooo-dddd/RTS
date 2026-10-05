# `check_point_FP`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.fast_search_space.check_point_FP`
- Lean: `Prosa.Implementation.Refinements.FP.FastSearchSpace.check_point_FP`
- Certificate: `check_point_FP_correspondence`

## Official Rocq

```coq
check_point_FP : seq (Equality.sort Task) -> Equality.sort Task -> nat -> nat * nat -> bool

check_point_FP is not universe polymorphic
Arguments check_point_FP ts%_seq_scope tsk R%_nat_scope P
check_point_FP is transparent
Expands to: Constant prosa.implementation.refinements.FP.fast_search_space.check_point_FP
Declared in library prosa.implementation.refinements.FP.fast_search_space, line 22, characters 11-25
check_point_FP
     : seq (Equality.sort Task) -> Equality.sort Task -> nat -> nat * nat -> bool
```

Body:

```coq
check_point_FP =
fun (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (R : nat) (P : nat * nat) =>
(task_rbf tsk (P.1 + 1) + total_ohep_rbf ts tsk (P.1 + P.2) <= P.1 + P.2) && (P.2 <= R)
     : seq (Equality.sort Task) -> Equality.sort Task -> nat -> nat * nat -> bool

Arguments check_point_FP ts%_seq_scope tsk R%_nat_scope P
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.FastSearchSpace.check_point_FP : List Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → ℕ → ℕ × ℕ → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.FastSearchSpace.check_point_FP : List
    Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → ℕ → ℕ × ℕ → Bool :=
fun ts tsk R P =>
  decide
      (Prosa.Implementation.Refinements.ArrivalCurve.task_rbf tsk (P.1 + 1) +
          Prosa.Implementation.Refinements.FP.FastSearchSpace.total_ohep_rbf ts tsk (P.1 + P.2) ≤
        P.1 + P.2) &&
    decide (P.2 ≤ R)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_check_point_FP
     : List_inst1 Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_Task -> Nat -> Prod_inst3 Nat Nat -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_check_point_FP@{} =
fun (ts : List_inst1 Prosa_Implementation_Refinements_Task_Task)
  (tsk : Prosa_Implementation_Refinements_Task_Task) (R : Nat) (P : Prod_inst3 Nat Nat) =>
Bool_and
  (Decidable_decide
     (LE_le_inst1 Nat instLENat
        (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
           (Prosa_Implementation_Refinements_ArrivalCurve_task_rbf tsk
              (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                 (Prod_fst_inst3 Nat Nat P)
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
           (Prosa_Implementation_Refinements_FP_FastSearchSpace_total_ohep_rbf ts tsk
              (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (Prod_fst_inst3 Nat Nat P)
                 (Prod_snd_inst3 Nat Nat P))))
        (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (Prod_fst_inst3 Nat Nat P)
           (Prod_snd_inst3 Nat Nat P)))
     (Nat_decLe
        (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
           (Prosa_Implementation_Refinements_ArrivalCurve_task_rbf tsk
              (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                 (Prod_fst_inst3 Nat Nat P)
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
           (Prosa_Implementation_Refinements_FP_FastSearchSpace_total_ohep_rbf ts tsk
              (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (Prod_fst_inst3 Nat Nat P)
                 (Prod_snd_inst3 Nat Nat P))))
        (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (Prod_fst_inst3 Nat Nat P)
           (Prod_snd_inst3 Nat Nat P))))
  (Decidable_decide (LE_le_inst1 Nat instLENat (Prod_snd_inst3 Nat Nat P) R)
     (Nat_decLe (Prod_snd_inst3 Nat Nat P) R))
     : List_inst1 Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_Task -> Nat -> Prod_inst3 Nat Nat -> Bool

Arguments Prosa_Implementation_Refinements_FP_FastSearchSpace_check_point_FP ts tsk R%_Nat_scope P
```
