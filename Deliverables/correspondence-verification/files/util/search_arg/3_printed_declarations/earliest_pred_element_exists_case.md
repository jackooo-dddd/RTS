# `earliest_pred_element_exists_case`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.search_arg.earliest_pred_element_exists_case`
- Lean: `Prosa.Util.SearchArg.earliest_pred_element_exists_case`
- Certificate: `earliest_pred_element_exists_case_statement_certificate`

## Official Rocq

```coq
earliest_pred_element_exists_case :
forall (P : pred nat) (t1 t2 : nat),
(forall t : nat, is_true (t1 <= t < t2) -> is_true (~~ P t)) \/
(exists t : nat,
   is_true (t1 <= t < t2) /\
   is_true (P t) /\ (forall t' : nat, is_true (t1 <= t') -> is_true (P t') -> is_true (t <= t')))

earliest_pred_element_exists_case is not universe polymorphic
Arguments earliest_pred_element_exists_case P (t1 t2)%nat_scope
earliest_pred_element_exists_case is opaque
Expands to: Constant prosa.util.search_arg.earliest_pred_element_exists_case
Declared in library prosa.util.search_arg, line 23, characters 6-39
earliest_pred_element_exists_case
     : forall (P : pred nat) (t1 t2 : nat),
       (forall t : nat, is_true (t1 <= t < t2) -> is_true (~~ P t)) \/
       (exists t : nat,
          is_true (t1 <= t < t2) /\
          is_true (P t) /\ (forall t' : nat, is_true (t1 <= t') -> is_true (P t') -> is_true (t <= t')))
```

## Lean

```lean
Prosa.Util.SearchArg.earliest_pred_element_exists_case : ∀ (P : ℕ → Bool) (t1 t2 : ℕ),
  (∀ (t : ℕ), t1 ≤ t ∧ t < t2 → P t = false) ∨
    ∃ t, (t1 ≤ t ∧ t < t2) ∧ P t = true ∧ ∀ (t' : ℕ), t1 ≤ t' → P t' = true → t ≤ t'
```

## Lean, imported into Rocq

```coq
Prosa_Util_SearchArg_earliest_pred_element_exists_case
     : forall (P : Nat -> Bool) (t1 t2 : Nat),
       Or
         (forall t : Nat,
          And (LE_le_inst1 Nat instLENat t1 t) (LT_lt_inst1 Nat instLTNat t t2) -> @eq Bool (P t) Bool_false)
         (Exists Nat
            (fun t : Nat =>
             And (And (LE_le_inst1 Nat instLENat t1 t) (LT_lt_inst1 Nat instLTNat t t2))
               (And (@eq Bool (P t) Bool_true)
                  (forall t' : Nat,
                   LE_le_inst1 Nat instLENat t1 t' ->
                   @eq Bool (P t') Bool_true -> LE_le_inst1 Nat instLENat t t'))))
```
