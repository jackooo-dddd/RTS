# `total_over_list`

- Kind (Rocq): Definition
- Rocq: `prosa.util.rel.total_over_list`
- Lean: `Prosa.Util.Rel.total_over_list`
- Certificate: `total_over_list_correspondence_certificate`

## Official Rocq

```coq
total_over_list :
forall {T : eqType}, (Equality.sort T -> Equality.sort T -> bool) -> seq (Equality.sort T) -> Prop

total_over_list is not universe polymorphic
Arguments total_over_list {T} R%function_scope xs%seq_scope
total_over_list is transparent
Expands to: Constant prosa.util.rel.total_over_list
Declared in library prosa.util.rel, line 30, characters 13-28
@total_over_list
     : forall T : eqType, (Equality.sort T -> Equality.sort T -> bool) -> seq (Equality.sort T) -> Prop
```

Body:

```coq
total_over_list =
fun (T : eqType) (R : Equality.sort T -> Equality.sort T -> bool) (xs : seq (Equality.sort T)) =>
forall x1 x2 : Equality.sort T,
is_true (x1 \in xs) -> is_true (x2 \in xs) -> is_true (R x1 x2) \/ is_true (R x2 x1)
     : forall {T : eqType}, (Equality.sort T -> Equality.sort T -> bool) -> seq (Equality.sort T) -> Prop

Arguments total_over_list {T} R%function_scope xs%seq_scope
```

## Lean

```lean
@Prosa.Util.Rel.total_over_list : {T : Type u_1} → [DecidableEq T] → (T → T → Bool) → List T → Prop
def Prosa.Util.Rel.total_over_list.{u} : {T : Type u} → [DecidableEq T] → (T → T → Bool) → List T → Prop :=
fun {T} [DecidableEq T] R xs => ∀ (x₁ x₂ : T), x₁ ∈ xs → x₂ ∈ xs → R x₁ x₂ = true ∨ R x₂ x₁ = true
```

## Lean, imported into Rocq

```coq
Prosa_Util_Rel_total_over_list
     : forall T : Type, DecidableEq T -> (T -> T -> Bool) -> List T -> SProp
```

Body:

```coq
Prosa_Util_Rel_total_over_list@{u Lean.u+1.0 Lean.u+2.0} =
fun (T : Type) (_ : DecidableEq T) (R : T -> T -> Bool) (xs : List T) =>
forall x_UU2081_ x_UU2082_ : T,
Membership_mem T (List T) (List_instMembership T) xs x_UU2081_ ->
Membership_mem T (List T) (List_instMembership T) xs x_UU2082_ ->
Or (@eq Bool (R x_UU2081_ x_UU2082_) Bool_true) (@eq Bool (R x_UU2082_ x_UU2081_) Bool_true)
     : forall T : Type, DecidableEq T -> (T -> T -> Bool) -> List T -> SProp

Arguments Prosa_Util_Rel_total_over_list T%_type_scope inst_3
  R%_function_scope xs
```
