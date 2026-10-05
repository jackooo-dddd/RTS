# `monotone`

- Kind (Rocq): Definition
- Rocq: `prosa.util.rel.monotone`
- Lean: `Prosa.Util.Rel.monotone`
- Certificate: `monotone_correspondence_certificate`

## Official Rocq

```coq
monotone : forall {T : Type}, rel T -> (T -> T) -> Prop

monotone is not universe polymorphic
Arguments monotone {T}%type_scope R f%function_scope
monotone is transparent
Expands to: Constant prosa.util.rel.monotone
Declared in library prosa.util.rel, line 14, characters 13-21
@monotone
     : forall T : Type, rel T -> (T -> T) -> Prop
```

Body:

```coq
monotone =
fun (T : Type) (R : rel T) (f : T -> T) => forall x y : T, is_true (R x y) -> is_true (R (f x) (f y))
     : forall {T : Type}, rel T -> (T -> T) -> Prop

Arguments monotone {T}%type_scope R f%function_scope
```

## Lean

```lean
@Prosa.Util.Rel.monotone : {T : Type u_1} → (T → T → Bool) → (T → T) → Prop
def Prosa.Util.Rel.monotone.{u} : {T : Type u} → (T → T → Bool) → (T → T) → Prop :=
fun {T} R f => ∀ (x y : T), R x y = true → R (f x) (f y) = true
```

## Lean, imported into Rocq

```coq
Prosa_Util_Rel_monotone
     : forall T : Type, (T -> T -> Bool) -> (T -> T) -> SProp
```

Body:

```coq
Prosa_Util_Rel_monotone@{u Lean.u+1.0} =
fun (T : Type) (R : T -> T -> Bool) (f : T -> T) =>
forall x y : T, @eq Bool (R x y) Bool_true -> @eq Bool (R (f x) (f y)) Bool_true
     : forall T : Type, (T -> T -> Bool) -> (T -> T) -> SProp

Arguments Prosa_Util_Rel_monotone T%_type_scope (R f)%_function_scope
```
