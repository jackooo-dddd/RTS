# `leq_bigmax_sup`

- Kind (Rocq): Corollary
- Rocq: `prosa.util.minmax.leq_bigmax_sup`
- Lean: `Prosa.Util.Minmax.leq_bigmax_sup`
- Certificate: `leq_bigmax_sup_statement_certificate`

## Official Rocq

```coq
leq_bigmax_sup :
forall {X : eqType} (P : pred (Equality.sort X)) (F : Equality.sort X -> nat) (xs : seq (Equality.sort X))
  (n : nat),
(exists x : Equality.sort X, is_true (x \in xs) /\ is_true (P x) /\ is_true (n <= F x)) ->
is_true
  (n <=
   @bigop.bigop.body nat (Equality.sort X) 0 xs
     (fun x : Equality.sort X => @bigop.BigBody nat (Equality.sort X) x maxn (P x) (F x)))

leq_bigmax_sup is not universe polymorphic
Arguments leq_bigmax_sup {X} P F%function_scope xs%seq_scope n%nat_scope _
leq_bigmax_sup is opaque
Expands to: Constant prosa.util.minmax.leq_bigmax_sup
Declared in library prosa.util.minmax, line 17, characters 10-24
@leq_bigmax_sup
     : forall (X : eqType) (P : pred (Equality.sort X)) (F : Equality.sort X -> nat)
         (xs : seq (Equality.sort X)) (n : nat),
       (exists x : Equality.sort X, is_true (x \in xs) /\ is_true (P x) /\ is_true (n <= F x)) ->
       is_true
         (n <=
          @bigop.bigop.body nat (Equality.sort X) 0 xs
            (fun x : Equality.sort X => @bigop.BigBody nat (Equality.sort X) x maxn (P x) (F x)))
```

## Lean

```lean
@Prosa.Util.Minmax.leq_bigmax_sup : ∀ {X : Type u_1} [DecidableEq X] (P : X → Bool) (F : X → ℕ) (xs : List X) (n : ℕ),
  (∃ x ∈ xs, P x = true ∧ n ≤ F x) → n ≤ Prosa.Util.Minmax.bigMaxListCond xs P F
```

## Lean, imported into Rocq

```coq
Prosa_Util_Minmax_leq_bigmax_sup
     : forall X : Type,
       DecidableEq X ->
       forall (P : X -> Bool) (F : X -> Nat) (xs : List X) (n : Nat),
       Exists X
         (fun x : X =>
          And (Membership_mem X (List X) (List_instMembership X) xs x)
            (And (@eq Bool (P x) Bool_true) (LE_le_inst1 Nat instLENat n (F x)))) ->
       LE_le_inst1 Nat instLENat n (Prosa_Util_Minmax_bigMaxListCond X xs P F)
```
