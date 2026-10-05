# `bigmax_leq_seqP`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.minmax.bigmax_leq_seqP`
- Lean: `Prosa.Util.Minmax.bigmax_leq_seqP`
- Certificate: `bigmax_leq_seqP_statement_certificate`

## Official Rocq

```coq
bigmax_leq_seqP :
forall {X : eqType} (F : Equality.sort X -> nat) (P : pred (Equality.sort X)) (xs : seq (Equality.sort X))
  (m : nat),
reflect (forall x : Equality.sort X, is_true (x \in xs) -> is_true (P x) -> is_true (F x <= m))
  (@bigop.bigop.body nat (Equality.sort X) 0 xs
     (fun x : Equality.sort X => @bigop.BigBody nat (Equality.sort X) x maxn (P x) (F x)) <=
   m)

bigmax_leq_seqP is not universe polymorphic
Arguments bigmax_leq_seqP {X} F%function_scope P xs%seq_scope m%nat_scope
bigmax_leq_seqP is opaque
Expands to: Constant prosa.util.minmax.bigmax_leq_seqP
Declared in library prosa.util.minmax, line 29, characters 6-21
@bigmax_leq_seqP
     : forall (X : eqType) (F : Equality.sort X -> nat) (P : pred (Equality.sort X))
         (xs : seq (Equality.sort X)) (m : nat),
       reflect (forall x : Equality.sort X, is_true (x \in xs) -> is_true (P x) -> is_true (F x <= m))
         (@bigop.bigop.body nat (Equality.sort X) 0 xs
            (fun x : Equality.sort X => @bigop.BigBody nat (Equality.sort X) x maxn (P x) (F x)) <=
          m)
```

## Lean

```lean
@Prosa.Util.Minmax.bigmax_leq_seqP : ∀ {X : Type u_1} [DecidableEq X] (F : X → ℕ) (P : X → Bool) (xs : List X) (m : ℕ),
  Prosa.Util.Minmax.bigMaxListCond xs P F ≤ m ↔ ∀ x ∈ xs, P x = true → F x ≤ m
```

## Lean, imported into Rocq

```coq
Prosa_Util_Minmax_bigmax_leq_seqP
     : forall X : Type,
       DecidableEq X ->
       forall (F : X -> Nat) (P : X -> Bool) (xs : List X) (m : Nat),
       Iff (LE_le_inst1 Nat instLENat (Prosa_Util_Minmax_bigMaxListCond X xs P F) m)
         (forall x : X,
          Membership_mem X (List X) (List_instMembership X) xs x ->
          @eq Bool (P x) Bool_true -> LE_le_inst1 Nat instLENat (F x) m)
```
