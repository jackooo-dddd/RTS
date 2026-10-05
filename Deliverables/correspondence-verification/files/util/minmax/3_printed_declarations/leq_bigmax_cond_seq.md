# `leq_bigmax_cond_seq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.minmax.leq_bigmax_cond_seq`
- Lean: `Prosa.Util.Minmax.leq_bigmax_cond_seq`
- Certificate: `leq_bigmax_cond_seq_statement_certificate`

## Official Rocq

```coq
leq_bigmax_cond_seq :
forall {X : eqType} (F : Equality.sort X -> nat) (P : pred (Equality.sort X)) (xs : seq (Equality.sort X))
  (x : Equality.sort X),
is_true (x \in xs) ->
is_true (P x) ->
is_true
  (F x <=
   @bigop.bigop.body nat (Equality.sort X) 0 xs
     (fun i : Equality.sort X => @bigop.BigBody nat (Equality.sort X) i maxn (P i) (F i)))

leq_bigmax_cond_seq is not universe polymorphic
Arguments leq_bigmax_cond_seq {X} F%function_scope P xs%seq_scope x _ _
leq_bigmax_cond_seq is opaque
Expands to: Constant prosa.util.minmax.leq_bigmax_cond_seq
Declared in library prosa.util.minmax, line 9, characters 6-25
@leq_bigmax_cond_seq
     : forall (X : eqType) (F : Equality.sort X -> nat) (P : pred (Equality.sort X))
         (xs : seq (Equality.sort X)) (x : Equality.sort X),
       is_true (x \in xs) ->
       is_true (P x) ->
       is_true
         (F x <=
          @bigop.bigop.body nat (Equality.sort X) 0 xs
            (fun i : Equality.sort X => @bigop.BigBody nat (Equality.sort X) i maxn (P i) (F i)))
```

## Lean

```lean
@Prosa.Util.Minmax.leq_bigmax_cond_seq : ∀ {X : Type u_1} [DecidableEq X] (F : X → ℕ) (P : X → Bool) (xs : List X),
  ∀ x ∈ xs, P x = true → F x ≤ Prosa.Util.Minmax.bigMaxListCond xs P F
```

## Lean, imported into Rocq

```coq
Prosa_Util_Minmax_leq_bigmax_cond_seq
     : forall X : Type,
       DecidableEq X ->
       forall (F : X -> Nat) (P : X -> Bool) (xs : List X) (x : X),
       Membership_mem X (List X) (List_instMembership X) xs x ->
       @eq Bool (P x) Bool_true ->
       LE_le_inst1 Nat instLENat (F x) (Prosa_Util_Minmax_bigMaxListCond X xs P F)
```
