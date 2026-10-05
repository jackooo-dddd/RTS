# `seq_different_elements_nil`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigcat.seq_different_elements_nil`
- Lean: `Prosa.Util.Bigcat.seq_different_elements_nil`
- Certificate: `seq_different_elements_nil_statement_certificate`

## Official Rocq

```coq
seq_different_elements_nil :
forall (X Y : eqType) (f : Equality.sort X -> seq (Equality.sort Y)) (g : Equality.sort Y -> Equality.sort X),
(forall (x : Equality.sort X) (y : Equality.sort Y), is_true (y \in f x) -> g y = x) ->
forall x1 x2 : Equality.sort X, is_true (x1 != x2) -> [seq x <- f x1 | g x == x2] = [::]

seq_different_elements_nil is not universe polymorphic
Arguments seq_different_elements_nil X Y (f g H_g_cancels_f)%function_scope x1 x2 _
seq_different_elements_nil is opaque
Expands to: Constant prosa.util.bigcat.seq_different_elements_nil
Declared in library prosa.util.bigcat, line 258, characters 10-36
seq_different_elements_nil
     : forall (X Y : eqType) (f : Equality.sort X -> seq (Equality.sort Y))
         (g : Equality.sort Y -> Equality.sort X),
       (forall (x : Equality.sort X) (y : Equality.sort Y), is_true (y \in f x) -> g y = x) ->
       forall x1 x2 : Equality.sort X, is_true (x1 != x2) -> [seq x <- f x1 | g x == x2] = [::]
```

## Lean

```lean
@Prosa.Util.Bigcat.seq_different_elements_nil : ∀ {X : Type u_1} {Y : Type u_2} [inst : DecidableEq X] [DecidableEq Y]
  (f : X → List Y) (g : Y → X),
  (∀ (x : X), ∀ y ∈ f x, g y = x) → ∀ (x₁ x₂ : X), x₁ ≠ x₂ → List.filter (fun x => decide (g x = x₂)) (f x₁) = []
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigcat_seq_different_elements_nil
     : forall (X Y : Type) (inst_4 : DecidableEq X),
       DecidableEq Y ->
       forall (f : X -> List Y) (g : Y -> X),
       (forall (x : X) (y : Y), Membership_mem Y (List Y) (List_instMembership Y) (f x) y -> @eq X (g y) x) ->
       forall x_UU2081_ x_UU2082_ : X,
       Ne X x_UU2081_ x_UU2082_ ->
       @eq (List Y)
         (List_filter Y
            (fun x : Y =>
             Decidable_decide (@eq X (g x) x_UU2082_)
               (inst_4 (g x) x_UU2082_))
            (f x_UU2081_))
         (List_nil Y)
```
