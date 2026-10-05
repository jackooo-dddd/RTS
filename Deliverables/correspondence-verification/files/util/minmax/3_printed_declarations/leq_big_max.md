# `leq_big_max`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.minmax.leq_big_max`
- Lean: `Prosa.Util.Minmax.leq_big_max`
- Certificate: `leq_big_max_statement_certificate`

## Official Rocq

```coq
leq_big_max :
forall {X : eqType} (F1 F2 : Equality.sort X -> nat) (P : pred (Equality.sort X))
  (xs : seq (Equality.sort X)),
(forall x : Equality.sort X, is_true (x \in xs) -> is_true (P x) -> is_true (F1 x <= F2 x)) ->
is_true
  (@bigop.bigop.body nat (Equality.sort X) 0 xs
     (fun x : Equality.sort X => @bigop.BigBody nat (Equality.sort X) x maxn (P x) (F1 x)) <=
   @bigop.bigop.body nat (Equality.sort X) 0 xs
     (fun x : Equality.sort X => @bigop.BigBody nat (Equality.sort X) x maxn (P x) (F2 x)))

leq_big_max is not universe polymorphic
Arguments leq_big_max {X} (F1 F2)%function_scope P xs%seq_scope _%function_scope
leq_big_max is opaque
Expands to: Constant prosa.util.minmax.leq_big_max
Declared in library prosa.util.minmax, line 46, characters 6-17
@leq_big_max
     : forall (X : eqType) (F1 F2 : Equality.sort X -> nat) (P : pred (Equality.sort X))
         (xs : seq (Equality.sort X)),
       (forall x : Equality.sort X, is_true (x \in xs) -> is_true (P x) -> is_true (F1 x <= F2 x)) ->
       is_true
         (@bigop.bigop.body nat (Equality.sort X) 0 xs
            (fun x : Equality.sort X => @bigop.BigBody nat (Equality.sort X) x maxn (P x) (F1 x)) <=
          @bigop.bigop.body nat (Equality.sort X) 0 xs
            (fun x : Equality.sort X => @bigop.BigBody nat (Equality.sort X) x maxn (P x) (F2 x)))
```

## Lean

```lean
@Prosa.Util.Minmax.leq_big_max : ∀ {X : Type u_1} [DecidableEq X] (F₁ F₂ : X → ℕ) (P : X → Bool) (xs : List X),
  (∀ x ∈ xs, P x = true → F₁ x ≤ F₂ x) →
    Prosa.Util.Minmax.bigMaxListCond xs P F₁ ≤ Prosa.Util.Minmax.bigMaxListCond xs P F₂
```

## Lean, imported into Rocq

```coq
Prosa_Util_Minmax_leq_big_max
     : forall X : Type,
       DecidableEq X ->
       forall (F_UU2081_ F_UU2082_ : X -> Nat) (P : X -> Bool) (xs : List X),
       (forall x : X,
        Membership_mem X (List X) (List_instMembership X) xs x ->
        @eq Bool (P x) Bool_true -> LE_le_inst1 Nat instLENat (F_UU2081_ x) (F_UU2082_ x)) ->
       LE_le_inst1 Nat instLENat (Prosa_Util_Minmax_bigMaxListCond X xs P F_UU2081_)
         (Prosa_Util_Minmax_bigMaxListCond X xs P F_UU2082_)
```
