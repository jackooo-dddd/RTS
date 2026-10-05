# `bigcat_nat_filter_eq_filter_bigcat_nat`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigcat.bigcat_nat_filter_eq_filter_bigcat_nat`
- Lean: `Prosa.Util.Bigcat.bigcat_nat_filter_eq_filter_bigcat_nat`
- Certificate: `bigcat_nat_filter_eq_filter_bigcat_nat_statement_certificate`

## Official Rocq

```coq
bigcat_nat_filter_eq_filter_bigcat_nat :
forall {X : Type} (F : nat -> seq X) (P : X -> bool) (t1 t2 : nat),

bigcat_nat_filter_eq_filter_bigcat_nat is not universe polymorphic
Arguments bigcat_nat_filter_eq_filter_bigcat_nat {X}%type_scope (F P)%function_scope (t1 t2)%nat_scope
bigcat_nat_filter_eq_filter_bigcat_nat is opaque
Expands to: Constant prosa.util.bigcat.bigcat_nat_filter_eq_filter_bigcat_nat
Declared in library prosa.util.bigcat, line 107, characters 8-46
@bigcat_nat_filter_eq_filter_bigcat_nat
     : forall (X : Type) (F : nat -> seq X) (P : X -> bool) (t1 t2 : nat),
       [seq x <- \cat_(t1<=t<t2)F t | P x] = \cat_(t1<=t<t2)[seq x <- F t | P x]
```

## Lean

```lean
@Prosa.Util.Bigcat.bigcat_nat_filter_eq_filter_bigcat_nat : ∀ {X : Type u_1} (F : ℕ → List X) (P : X → Bool)
  (t₁ t₂ : ℕ),
  List.filter P (Prosa.Util.Notation.bigCat t₁ t₂ F) = Prosa.Util.Notation.bigCat t₁ t₂ fun t => List.filter P (F t)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigcat_bigcat_nat_filter_eq_filter_bigcat_nat
     : forall (X : Type) (F : Nat -> List X) (P : X -> Bool) (t_UU2081_ t_UU2082_ : Nat),
       @eq (List X) (List_filter X P (Prosa_Util_Notation_bigCat X t_UU2081_ t_UU2082_ F))
         (Prosa_Util_Notation_bigCat X t_UU2081_ t_UU2082_ (fun t : Nat => List_filter X P (F t)))
```
