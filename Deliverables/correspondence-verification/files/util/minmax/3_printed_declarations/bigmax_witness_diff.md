# `bigmax_witness_diff`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.minmax.bigmax_witness_diff`
- Lean: `Prosa.Util.Minmax.bigmax_witness_diff`
- Certificate: `bigmax_witness_diff_statement_certificate`

## Official Rocq

```coq
bigmax_witness_diff :
forall {T : eqType} {xs : seq (Equality.sort T)} {P1 P2 : Equality.sort T -> bool}
  {F : Equality.sort T -> nat},
is_true
  (@bigop.bigop.body nat (Equality.sort T) 0 xs
     (fun x : Equality.sort T => @bigop.BigBody nat (Equality.sort T) x maxn (P1 x) (F x)) <
   @bigop.bigop.body nat (Equality.sort T) 0 xs
     (fun x : Equality.sort T => @bigop.BigBody nat (Equality.sort T) x maxn (P2 x) (F x))) ->
exists x : Equality.sort T, is_true (x \in xs) /\ is_true (~~ P1 x) /\ is_true (P2 x)

bigmax_witness_diff is not universe polymorphic
Arguments bigmax_witness_diff {T} {xs}%seq_scope {P1 P2 F}%function_scope _
bigmax_witness_diff is opaque
Expands to: Constant prosa.util.minmax.bigmax_witness_diff
Declared in library prosa.util.minmax, line 161, characters 6-25
@bigmax_witness_diff
     : forall (T : eqType) (xs : seq (Equality.sort T)) (P1 P2 : Equality.sort T -> bool)
         (F : Equality.sort T -> nat),
       is_true
         (@bigop.bigop.body nat (Equality.sort T) 0 xs
            (fun x : Equality.sort T => @bigop.BigBody nat (Equality.sort T) x maxn (P1 x) (F x)) <
          @bigop.bigop.body nat (Equality.sort T) 0 xs
            (fun x : Equality.sort T => @bigop.BigBody nat (Equality.sort T) x maxn (P2 x) (F x))) ->
       exists x : Equality.sort T, is_true (x \in xs) /\ is_true (~~ P1 x) /\ is_true (P2 x)
```

## Lean

```lean
@Prosa.Util.Minmax.bigmax_witness_diff : ∀ {X : Type u_1} [DecidableEq X] {xs : List X} {P₁ P₂ : X → Bool} {F : X → ℕ},
  Prosa.Util.Minmax.bigMaxListCond xs P₁ F < Prosa.Util.Minmax.bigMaxListCond xs P₂ F →
    ∃ x ∈ xs, P₁ x = false ∧ P₂ x = true
```

## Lean, imported into Rocq

```coq
Prosa_Util_Minmax_bigmax_witness_diff
     : forall X : Type,
       DecidableEq X ->
       forall (xs : List X) (P_UU2081_ P_UU2082_ : X -> Bool) (F : X -> Nat),
       LT_lt_inst1 Nat instLTNat (Prosa_Util_Minmax_bigMaxListCond X xs P_UU2081_ F)
         (Prosa_Util_Minmax_bigMaxListCond X xs P_UU2082_ F) ->
       Exists X
         (fun x : X =>
          And (Membership_mem X (List X) (List_instMembership X) xs x)
            (And (@eq Bool (P_UU2081_ x) Bool_false) (@eq Bool (P_UU2082_ x) Bool_true)))
```
