# `mem_bigcat_nat`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigcat.mem_bigcat_nat`
- Lean: `Prosa.Util.Bigcat.mem_bigcat_nat`
- Certificate: `mem_bigcat_nat_statement_certificate`

## Official Rocq

```coq
mem_bigcat_nat :
forall (T : eqType) (f : nat -> seq (Equality.sort T)) (x : Equality.sort T) (m n j : nat),
is_true (m <= j < n) -> is_true (x \in f j) -> is_true (x \in \cat_(m<=i<n)f i)

mem_bigcat_nat is not universe polymorphic
Arguments mem_bigcat_nat T f%function_scope x (m n j)%nat_scope _ _
mem_bigcat_nat is opaque
Expands to: Constant prosa.util.bigcat.mem_bigcat_nat
Declared in library prosa.util.bigcat, line 19, characters 8-22
mem_bigcat_nat
     : forall (T : eqType) (f : nat -> seq (Equality.sort T)) (x : Equality.sort T) (m n j : nat),
       is_true (m <= j < n) -> is_true (x \in f j) -> is_true (x \in \cat_(m<=i<n)f i)
```

## Lean

```lean
@Prosa.Util.Bigcat.mem_bigcat_nat : ∀ {T : Type u_1} [DecidableEq T] (f : ℕ → List T) (x : T) (m n j : ℕ),
  m ≤ j ∧ j < n → x ∈ f j → x ∈ Prosa.Util.Notation.bigCat m n f
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigcat_mem_bigcat_nat
     : forall T : Type,
       DecidableEq T ->
       forall (f : Nat -> List T) (x : T) (m n j : Nat),
       And (LE_le_inst1 Nat instLENat m j) (LT_lt_inst1 Nat instLTNat j n) ->
       Membership_mem T (List T) (List_instMembership T) (f j) x ->
       Membership_mem T (List T) (List_instMembership T) (Prosa_Util_Notation_bigCat T m n f) x
```
