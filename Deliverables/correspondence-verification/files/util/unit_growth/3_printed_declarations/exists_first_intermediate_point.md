# `exists_first_intermediate_point`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.unit_growth.exists_first_intermediate_point`
- Lean: `Prosa.Util.UnitGrowth.exists_first_intermediate_point`
- Certificate: `exists_first_intermediate_point_statement_certificate`

## Official Rocq

```coq
exists_first_intermediate_point :
forall (P : nat -> bool) (t1 t2 : nat),
is_true (t1 <= t2) ->
is_true (~~ P t1) ->
is_true (P t2) ->
exists t : nat,
  is_true (t1 < t <= t2) /\ (forall x : nat, is_true (t1 <= x < t) -> is_true (~~ P x)) /\ is_true (P t)

exists_first_intermediate_point is not universe polymorphic
Arguments exists_first_intermediate_point P%function_scope (t1 t2)%nat_scope H_t1_le_t2 
  H_not_P_at_t1 H_P_at_t2
exists_first_intermediate_point is opaque
Expands to: Constant prosa.util.unit_growth.exists_first_intermediate_point
Declared in library prosa.util.unit_growth, line 141, characters 10-41
exists_first_intermediate_point
     : forall (P : nat -> bool) (t1 t2 : nat),
       is_true (t1 <= t2) ->
       is_true (~~ P t1) ->
       is_true (P t2) ->
       exists t : nat,
         is_true (t1 < t <= t2) /\
         (forall x : nat, is_true (t1 <= x < t) -> is_true (~~ P x)) /\ is_true (P t)
```

## Lean

```lean
Prosa.Util.UnitGrowth.exists_first_intermediate_point : ∀ (P : ℕ → Bool) (t1 t2 : ℕ),
  t1 ≤ t2 → P t1 = false → P t2 = true → ∃ t, (t1 < t ∧ t ≤ t2) ∧ (∀ (x : ℕ), t1 ≤ x ∧ x < t → P x = false) ∧ P t = true
```

## Lean, imported into Rocq

```coq
Prosa_Util_UnitGrowth_exists_first_intermediate_point
     : forall (P : Nat -> Bool) (t1 t2 : Nat),
       LE_le_inst1 Nat instLENat t1 t2 ->
       @eq Bool (P t1) Bool_false ->
       @eq Bool (P t2) Bool_true ->
       Exists Nat
         (fun t : Nat =>
          And (And (LT_lt_inst1 Nat instLTNat t1 t) (LE_le_inst1 Nat instLENat t t2))
            (And
               (forall x : Nat,
                And (LE_le_inst1 Nat instLENat t1 x) (LT_lt_inst1 Nat instLTNat x t) ->
                @eq Bool (P x) Bool_false)
               (@eq Bool (P t) Bool_true)))
```
