# `index_iota_filter_eqx`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.index_iota_filter_eqx`
- Lean: `Prosa.Util.List.index_iota_filter_eqx`
- Certificate: `index_iota_filter_eqx_statement_certificate`

## Official Rocq

```coq
index_iota_filter_eqx :
forall x a b : nat, is_true (a <= x < b) -> [seq ρ <- bigop.index_iota a b | ρ == x] = [:: x]

index_iota_filter_eqx is not universe polymorphic
Arguments index_iota_filter_eqx (x a b)%nat_scope _
index_iota_filter_eqx is opaque
Expands to: Constant prosa.util.list.index_iota_filter_eqx
Declared in library prosa.util.list, line 686, characters 6-27
index_iota_filter_eqx
     : forall x a b : nat, is_true (a <= x < b) -> [seq ρ <- bigop.index_iota a b | ρ == x] = [:: x]
```

## Lean

```lean
Prosa.Util.List.index_iota_filter_eqx : ∀ (x a b : ℕ),
  a ≤ x ∧ x < b → List.filter (fun ρ => decide (ρ = x)) (Prosa.Util.List.index_iota a b) = [x]
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_index_iota_filter_eqx
     : forall x a b : Nat,
       And (LE_le_inst1 Nat instLENat a x) (LT_lt_inst1 Nat instLTNat x b) ->
       @eq (List_inst1 Nat)
         (List_filter_inst1 Nat
            (fun _UU03c1_ : Nat => Decidable_decide (@eq Nat _UU03c1_ x) (instDecidableEqNat _UU03c1_ x))
            (Prosa_Util_List_index_iota a b))
         (List_cons_inst1 Nat x (List_nil_inst1 Nat))
```
