# `mem_bigcat_ord`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigcat.mem_bigcat_ord`
- Lean: `Prosa.Util.Bigcat.mem_bigcat_ord`
- Certificate: `mem_bigcat_ord_statement_certificate`

## Official Rocq

```coq
mem_bigcat_ord :
forall (T : eqType) (x : Equality.sort T) (n : nat) (j : fintype.ordinal n)
  (f : fintype.ordinal n -> seq (Equality.sort T)),
is_true (@fintype.nat_of_ord n j < n) -> is_true (x \in f j) -> is_true (x \in \cat_(i<n)f i)

mem_bigcat_ord is not universe polymorphic
Arguments mem_bigcat_ord T x n%nat_scope j f%function_scope _ _
mem_bigcat_ord is opaque
Expands to: Constant prosa.util.bigcat.mem_bigcat_ord
Declared in library prosa.util.bigcat, line 54, characters 8-22
mem_bigcat_ord
     : forall (T : eqType) (x : Equality.sort T) (n : nat) (j : fintype.ordinal n)
         (f : fintype.ordinal n -> seq (Equality.sort T)),
       is_true (@fintype.nat_of_ord n j < n) -> is_true (x \in f j) -> is_true (x \in \cat_(i<n)f i)
```

## Lean

```lean
@Prosa.Util.Bigcat.mem_bigcat_ord : ∀ {T : Type u_1} [DecidableEq T] (x : T) (n : ℕ) (j : Fin n) (g : Fin n → List T),
  ↑j < n → x ∈ g j → x ∈ Prosa.Util.Bigcat.bigCatFin g
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigcat_mem_bigcat_ord
     : forall T : Type,
       DecidableEq T ->
       forall (x : T) (n : Nat) (j : Fin n) (g : Fin n -> List T),
       LT_lt_inst1 Nat instLTNat (Fin_val n j) n ->
       Membership_mem T (List T) (List_instMembership T) (g j) x ->
       Membership_mem T (List T) (List_instMembership T) (Prosa_Util_Bigcat_bigCatFin T n g) x
```
