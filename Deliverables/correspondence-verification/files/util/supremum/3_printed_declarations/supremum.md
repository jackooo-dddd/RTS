# `supremum`

- Kind (Rocq): Definition
- Rocq: `prosa.util.supremum.supremum`
- Lean: `Prosa.Util.Supremum.supremum`
- Certificate: `supremum_correspondence_certificate`

## Official Rocq

```coq
supremum : forall {T : eqType}, rel (Equality.sort T) -> seq (Equality.sort T) -> option (Equality.sort T)

supremum is not universe polymorphic
Arguments supremum {T} R s%seq_scope
supremum is transparent
Expands to: Constant prosa.util.supremum.supremum
Declared in library prosa.util.supremum, line 29, characters 13-21
@supremum
     : forall T : eqType, rel (Equality.sort T) -> seq (Equality.sort T) -> option (Equality.sort T)
```

Body:

```coq
supremum =
fun (T : eqType) (R : rel (Equality.sort T)) =>
     : forall {T : eqType}, rel (Equality.sort T) -> seq (Equality.sort T) -> option (Equality.sort T)

Arguments supremum {T} R s%seq_scope
```

## Lean

```lean
@Prosa.Util.Supremum.supremum : {T : Type u_1} → (T → T → Bool) → List T → Option T
def Prosa.Util.Supremum.supremum.{u} : {T : Type u} → (T → T → Bool) → List T → Option T :=
fun {T} R s => List.foldr (Prosa.Util.Supremum.choose_superior R) none s
```

## Lean, imported into Rocq

```coq
Prosa_Util_Supremum_supremum
     : forall T : Type, (T -> T -> Bool) -> List T -> Option T
```

Body:

```coq
Prosa_Util_Supremum_supremum@{u Lean.u+1.0 Lean.u+2.0} =
fun (T : Type) (R : T -> T -> Bool) (s : List T) =>
List_foldr T (Option T) (Prosa_Util_Supremum_choose_superior T R) (Option_none T) s
     : forall T : Type, (T -> T -> Bool) -> List T -> Option T

Arguments Prosa_Util_Supremum_supremum T%_type_scope R%_function_scope s
```
