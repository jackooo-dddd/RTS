# `all_pos_implies_lcml_pos`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.lcmseq.all_pos_implies_lcml_pos`
- Lean: `Prosa.Util.Lcmseq.all_pos_implies_lcml_pos`
- Certificate: `all_pos_implies_lcml_pos_correspondence`

## Official Rocq

```coq
all_pos_implies_lcml_pos :
forall xs : seq nat,
(forall x : Equality.sort Datatypes_nat__canonical__eqtype_Equality, is_true (x \in xs) -> is_true (0 < x)) ->
is_true (0 < lcml xs)

all_pos_implies_lcml_pos is not universe polymorphic
Arguments all_pos_implies_lcml_pos xs%seq_scope _%function_scope
all_pos_implies_lcml_pos is opaque
Expands to: Constant prosa.util.lcmseq.all_pos_implies_lcml_pos
Declared in library prosa.util.lcmseq, line 46, characters 6-30
all_pos_implies_lcml_pos
     : forall xs : seq nat,
       (forall x : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
        is_true (x \in xs) -> is_true (0 < x)) ->
       is_true (0 < lcml xs)
```

## Lean

```lean
Prosa.Util.Lcmseq.all_pos_implies_lcml_pos : ∀ (xs : List ℕ), (∀ x ∈ xs, 0 < x) → 0 < Prosa.Util.Lcmseq.lcml xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_Lcmseq_all_pos_implies_lcml_pos
     : forall xs : List_inst1 Nat,
       (forall x : Nat,
        Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) xs x ->
        LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) x) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) (Prosa_Util_Lcmseq_lcml xs)
```
