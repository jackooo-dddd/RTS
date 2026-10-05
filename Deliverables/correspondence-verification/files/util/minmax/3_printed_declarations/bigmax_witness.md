# `bigmax_witness`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.minmax.bigmax_witness`
- Lean: `Prosa.Util.Minmax.bigmax_witness`
- Certificate: `bigmax_witness_statement_certificate`

## Official Rocq

```coq
bigmax_witness :
forall {T : eqType} {xs : seq (Equality.sort T)} {P : pred (Equality.sort T)} (F : Equality.sort T -> nat),
is_true (@has (Equality.sort T) P xs) ->
exists x : Equality.sort T,
  is_true (x \in xs) /\
  is_true (P x) /\
  F x =
  @bigop.bigop.body nat (Equality.sort T) 0 xs
    (fun x0 : Equality.sort T => @bigop.BigBody nat (Equality.sort T) x0 maxn (P x0) (F x0))

bigmax_witness is not universe polymorphic
Arguments bigmax_witness {T} {xs}%seq_scope {P} F%function_scope _
bigmax_witness is opaque
Expands to: Constant prosa.util.minmax.bigmax_witness
Declared in library prosa.util.minmax, line 129, characters 6-20
@bigmax_witness
     : forall (T : eqType) (xs : seq (Equality.sort T)) (P : pred (Equality.sort T))
         (F : Equality.sort T -> nat),
       is_true (@has (Equality.sort T) P xs) ->
       exists x : Equality.sort T,
         is_true (x \in xs) /\
         is_true (P x) /\
         F x =
         @bigop.bigop.body nat (Equality.sort T) 0 xs
           (fun x0 : Equality.sort T => @bigop.BigBody nat (Equality.sort T) x0 maxn (P x0) (F x0))
```

## Lean

```lean
@Prosa.Util.Minmax.bigmax_witness : ∀ {X : Type u_1} [DecidableEq X] {xs : List X} {P : X → Bool} (F : X → ℕ),
  xs.any P = true → ∃ x ∈ xs, P x = true ∧ F x = Prosa.Util.Minmax.bigMaxListCond xs P F
```

## Lean, imported into Rocq

```coq
Prosa_Util_Minmax_bigmax_witness
     : forall X : Type,
       DecidableEq X ->
       forall (xs : List X) (P : X -> Bool) (F : X -> Nat),
       @eq Bool (List_any X xs P) Bool_true ->
       Exists X
         (fun x : X =>
          And (Membership_mem X (List X) (List_instMembership X) xs x)
            (And (@eq Bool (P x) Bool_true) (@eq Nat (F x) (Prosa_Util_Minmax_bigMaxListCond X xs P F))))
```
