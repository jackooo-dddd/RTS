# `bigmax_subset`

- Kind (Rocq): Corollary
- Rocq: `prosa.util.minmax.bigmax_subset`
- Lean: `Prosa.Util.Minmax.bigmax_subset`
- Certificate: `bigmax_subset_statement_certificate`

## Official Rocq

```coq
bigmax_subset :
forall {T : eqType} {xs : seq (Equality.sort T)} {P1 P2 : pred (Equality.sort T)}
  {F : Equality.sort T -> nat},
(forall x : Equality.sort T, is_true (x \in xs) -> is_true (P1 x) -> is_true (P2 x)) ->
is_true
  (@bigop.bigop.body nat (Equality.sort T) 0 xs
     (fun x : Equality.sort T => @bigop.BigBody nat (Equality.sort T) x maxn (P1 x) (F x)) <=
   @bigop.bigop.body nat (Equality.sort T) 0 xs
     (fun x : Equality.sort T => @bigop.BigBody nat (Equality.sort T) x maxn (P2 x) (F x)))

bigmax_subset is not universe polymorphic
Arguments bigmax_subset {T} {xs}%seq_scope {P1 P2} {F}%function_scope _%function_scope
bigmax_subset is opaque
Expands to: Constant prosa.util.minmax.bigmax_subset
Declared in library prosa.util.minmax, line 184, characters 10-23
@bigmax_subset
     : forall (T : eqType) (xs : seq (Equality.sort T)) (P1 P2 : pred (Equality.sort T))
         (F : Equality.sort T -> nat),
       (forall x : Equality.sort T, is_true (x \in xs) -> is_true (P1 x) -> is_true (P2 x)) ->
       is_true
         (@bigop.bigop.body nat (Equality.sort T) 0 xs
            (fun x : Equality.sort T => @bigop.BigBody nat (Equality.sort T) x maxn (P1 x) (F x)) <=
          @bigop.bigop.body nat (Equality.sort T) 0 xs
            (fun x : Equality.sort T => @bigop.BigBody nat (Equality.sort T) x maxn (P2 x) (F x)))
```

## Lean

```lean
@Prosa.Util.Minmax.bigmax_subset : ∀ {X : Type u_1} [DecidableEq X] {xs : List X} {P₁ P₂ : X → Bool} {F : X → ℕ},
  (∀ x ∈ xs, P₁ x = true → P₂ x = true) →
    Prosa.Util.Minmax.bigMaxListCond xs P₁ F ≤ Prosa.Util.Minmax.bigMaxListCond xs P₂ F
```

## Lean, imported into Rocq

```coq
Prosa_Util_Minmax_bigmax_subset
     : forall X : Type,
       DecidableEq X ->
       forall (xs : List X) (P_UU2081_ P_UU2082_ : X -> Bool) (F : X -> Nat),
       (forall x : X,
        Membership_mem X (List X) (List_instMembership X) xs x ->
        @eq Bool (P_UU2081_ x) Bool_true -> @eq Bool (P_UU2082_ x) Bool_true) ->
       LE_le_inst1 Nat instLENat (Prosa_Util_Minmax_bigMaxListCond X xs P_UU2081_ F)
         (Prosa_Util_Minmax_bigMaxListCond X xs P_UU2082_ F)
```
