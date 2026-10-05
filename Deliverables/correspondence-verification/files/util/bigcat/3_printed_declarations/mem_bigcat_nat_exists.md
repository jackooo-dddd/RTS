# `mem_bigcat_nat_exists`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigcat.mem_bigcat_nat_exists`
- Lean: `Prosa.Util.Bigcat.mem_bigcat_nat_exists`
- Certificate: `mem_bigcat_nat_exists_statement_certificate`

## Official Rocq

```coq
mem_bigcat_nat_exists :
forall (T : eqType) (f : nat -> seq (Equality.sort T)) (x : Equality.sort T) (m n : nat),
is_true (x \in \cat_(m<=i<n)f i) -> exists i : nat, is_true (x \in f i) /\ is_true (m <= i < n)

mem_bigcat_nat_exists is not universe polymorphic
Arguments mem_bigcat_nat_exists T f%function_scope x (m n)%nat_scope _
mem_bigcat_nat_exists is opaque
Expands to: Constant prosa.util.bigcat.mem_bigcat_nat_exists
Declared in library prosa.util.bigcat, line 35, characters 8-29
mem_bigcat_nat_exists
     : forall (T : eqType) (f : nat -> seq (Equality.sort T)) (x : Equality.sort T) (m n : nat),
       is_true (x \in \cat_(m<=i<n)f i) -> exists i : nat, is_true (x \in f i) /\ is_true (m <= i < n)
```

## Lean

```lean
@Prosa.Util.Bigcat.mem_bigcat_nat_exists : ∀ {T : Type u_1} [DecidableEq T] (f : ℕ → List T) (x : T) (m n : ℕ),
  x ∈ Prosa.Util.Notation.bigCat m n f → ∃ i, x ∈ f i ∧ m ≤ i ∧ i < n
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigcat_mem_bigcat_nat_exists
     : forall T : Type,
       DecidableEq T ->
       forall (f : Nat -> List T) (x : T) (m n : Nat),
       Membership_mem T (List T) (List_instMembership T) (Prosa_Util_Notation_bigCat T m n f) x ->
       Exists Nat
         (fun i : Nat =>
          And (Membership_mem T (List T) (List_instMembership T) (f i) x)
            (And (LE_le_inst1 Nat instLENat m i) (LT_lt_inst1 Nat instLTNat i n)))
```
