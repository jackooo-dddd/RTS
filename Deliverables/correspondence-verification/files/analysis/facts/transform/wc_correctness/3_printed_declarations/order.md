# `order`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.transform.wc_correctness.order`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.order`
- Certificate: `order_correspondence`

## Official Rocq

```coq
order : nat -> nat -> bool

order is not universe polymorphic
Arguments order (_ _)%nat_scope
order is transparent
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.order
Declared in library prosa.analysis.facts.transform.wc_correctness, line 231, characters 17-22
order
     : nat -> nat -> bool
```

Body:

```coq
order = fun=> xpred0
     : nat -> nat -> bool

Arguments order (_ _)%nat_scope
```

## Lean

```lean
Prosa.Analysis.Facts.Transform.WcCorrectness.order : ℕ → ℕ → Bool
```

Body:

```lean
def Prosa.Analysis.Facts.Transform.WcCorrectness.order : ℕ → ℕ → Bool :=
fun x x_1 => false
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_order
     : Nat -> Nat -> Bool
```

Body:

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_order@{} = fun _ _ : Nat => Bool_false
     : Nat -> Nat -> Bool

Arguments Prosa_Analysis_Facts_Transform_WcCorrectness_order
  (x____at___Prosa_Analysis_Facts_Transform_WcCorrectness3638836085__hygCtx__hyg6
   x____at___Init_Prelude2408276647__hygCtx__hyg14)%_Nat_scope
```
