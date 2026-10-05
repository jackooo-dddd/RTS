# `neqP`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.tactics.neqP`
- Lean: `Prosa.Util.Tactics.neqP`
- Certificate: `neqP_statement_correspondence_certificate`

## Official Rocq

```coq
neqP : forall (T : eqType) (x y : Equality.sort T), reflect (x <> y) (x != y)

neqP is not universe polymorphic
Arguments neqP T x y
neqP is opaque
Expands to: Constant prosa.util.tactics.neqP
Declared in library prosa.util.tactics, line 5, characters 6-10
neqP
     : forall (T : eqType) (x y : Equality.sort T), reflect (x <> y) (x != y)
```

## Lean

```lean
@Prosa.Util.Tactics.neqP : ∀ {T : Type u_1} [inst : DecidableEq T] (x y : T), decide (x ≠ y) = true ↔ x ≠ y
```

## Lean, imported into Rocq

```coq
Prosa_Util_Tactics_neqP
     : forall (T : Type) (inst_3 : DecidableEq T) (x y : T),
       Iff
         (@eq Bool
            (Decidable_decide (Ne T x y)
               (instDecidableNot (@eq T x y) (inst_3 x y)))
            Bool_true)
         (Ne T x y)
```
