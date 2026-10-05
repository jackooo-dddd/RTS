# `bigcat_nat_uniq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigcat.bigcat_nat_uniq`
- Lean: `Prosa.Util.Bigcat.bigcat_nat_uniq`
- Certificate: `bigcat_nat_uniq_statement_certificate`

## Official Rocq

```coq
bigcat_nat_uniq :
forall (T : eqType) (f : nat -> seq (Equality.sort T)),
(forall i : nat, is_true (@uniq T (f i))) ->
(forall (x : Equality.sort T) (i1 i2 : nat), is_true (x \in f i1) -> is_true (x \in f i2) -> i1 = i2) ->
forall n1 n2 : nat, is_true (@uniq T (\cat_(n1<=i<n2)f i))

bigcat_nat_uniq is not universe polymorphic
Arguments bigcat_nat_uniq T (f H_uniq_seq H_no_elements_in_common)%function_scope (n1 n2)%nat_scope
bigcat_nat_uniq is opaque
Expands to: Constant prosa.util.bigcat.bigcat_nat_uniq
Declared in library prosa.util.bigcat, line 82, characters 10-25
bigcat_nat_uniq
     : forall (T : eqType) (f : nat -> seq (Equality.sort T)),
       (forall i : nat, is_true (@uniq T (f i))) ->
       (forall (x : Equality.sort T) (i1 i2 : nat), is_true (x \in f i1) -> is_true (x \in f i2) -> i1 = i2) ->
       forall n1 n2 : nat, is_true (@uniq T (\cat_(n1<=i<n2)f i))
```

## Lean

```lean
@Prosa.Util.Bigcat.bigcat_nat_uniq : ∀ {T : Type u_1} [DecidableEq T] (f : ℕ → List T),
  (∀ (i : ℕ), (f i).Nodup) →
    (∀ (x : T) (i₁ i₂ : ℕ), x ∈ f i₁ → x ∈ f i₂ → i₁ = i₂) → ∀ (n₁ n₂ : ℕ), (Prosa.Util.Notation.bigCat n₁ n₂ f).Nodup
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigcat_bigcat_nat_uniq
     : forall T : Type,
       DecidableEq T ->
       forall f : Nat -> List T,
       (forall i : Nat, List_Nodup T (f i)) ->
       (forall (x : T) (i_UU2081_ i_UU2082_ : Nat),
        Membership_mem T (List T) (List_instMembership T) (f i_UU2081_) x ->
        Membership_mem T (List T) (List_instMembership T) (f i_UU2082_) x -> @eq Nat i_UU2081_ i_UU2082_) ->
       forall n_UU2081_ n_UU2082_ : Nat, List_Nodup T (Prosa_Util_Notation_bigCat T n_UU2081_ n_UU2082_ f)
```
