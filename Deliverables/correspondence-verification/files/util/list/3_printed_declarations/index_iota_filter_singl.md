# `index_iota_filter_singl`

- Kind (Rocq): Corollary
- Rocq: `prosa.util.list.index_iota_filter_singl`
- Lean: `Prosa.Util.List.index_iota_filter_singl`
- Certificate: `index_iota_filter_singl_statement_certificate`

## Official Rocq

```coq
index_iota_filter_singl :
forall x a b : nat, is_true (a <= x < b) -> [seq ρ <- bigop.index_iota a b | ρ \in [:: x]] = [:: x]

index_iota_filter_singl is not universe polymorphic
Arguments index_iota_filter_singl (x a b)%nat_scope _
index_iota_filter_singl is opaque
Expands to: Constant prosa.util.list.index_iota_filter_singl
Declared in library prosa.util.list, line 718, characters 10-33
index_iota_filter_singl
     : forall x a b : nat, is_true (a <= x < b) -> [seq ρ <- bigop.index_iota a b | ρ \in [:: x]] = [:: x]
```

## Lean

```lean
Prosa.Util.List.index_iota_filter_singl : ∀ (x a b : ℕ),
  a ≤ x ∧ x < b → List.filter (fun ρ => decide (ρ ∈ [x])) (Prosa.Util.List.index_iota a b) = [x]
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_index_iota_filter_singl
     : forall x a b : Nat,
       And (LE_le_inst1 Nat instLENat a x) (LT_lt_inst1 Nat instLTNat x b) ->
       @eq (List_inst1 Nat)
         (List_filter_inst1 Nat
            (fun _UU03c1_ : Nat =>
             Decidable_decide
               (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat)
                  (List_cons_inst1 Nat x (List_nil_inst1 Nat)) _UU03c1_)
               (List_instDecidableMemOfLawfulBEq_inst1 Nat
                  (instBEqOfDecidableEq_inst1 Nat instDecidableEqNat) Nat_instLawfulBEq _UU03c1_
                  (List_cons_inst1 Nat x (List_nil_inst1 Nat))))
            (Prosa_Util_List_index_iota a b))
         (List_cons_inst1 Nat x (List_nil_inst1 Nat))
```
