# `strict_prefix_of`

- Kind (Rocq): Definition
- Rocq: `prosa.util.list.strict_prefix_of`
- Lean: `Prosa.Util.List.strict_prefix_of`
- Certificate: `strict_prefix_of_definition_certificate`

## Official Rocq

```coq
strict_prefix_of : forall {T : eqType}, seq (Equality.sort T) -> seq (Equality.sort T) -> Prop

strict_prefix_of is not universe polymorphic
Arguments strict_prefix_of {T} (xs ys)%seq_scope
strict_prefix_of is transparent
Expands to: Constant prosa.util.list.strict_prefix_of
Declared in library prosa.util.list, line 876, characters 11-27
@strict_prefix_of
     : forall T : eqType, seq (Equality.sort T) -> seq (Equality.sort T) -> Prop
```

Body:

```coq
strict_prefix_of =
fun (T : eqType) (xs ys : seq (Equality.sort T)) =>
exists xs_tail : seq (Equality.sort T), xs_tail <> [::] /\ xs ++ xs_tail = ys
     : forall {T : eqType}, seq (Equality.sort T) -> seq (Equality.sort T) -> Prop

Arguments strict_prefix_of {T} (xs ys)%seq_scope
```

## Lean

```lean
@Prosa.Util.List.strict_prefix_of : {T : Type u_1} → [DecidableEq T] → List T → List T → Prop
def Prosa.Util.List.strict_prefix_of.{u} : {T : Type u} → [DecidableEq T] → List T → List T → Prop :=
fun {T} [DecidableEq T] xs ys => ∃ xsTail, xsTail ≠ [] ∧ xs ++ xsTail = ys
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_strict_prefix_of
     : forall T : Type, DecidableEq T -> List T -> List T -> SProp
```

Body:

```coq
Prosa_Util_List_strict_prefix_of@{u Lean.u+1.0 Lean.u+2.0} =
fun (T : Type) (_ : DecidableEq T) (xs ys : List T) =>
Exists (List T)
  (fun xsTail : List T =>
   And (Ne (List T) xsTail (List_nil T))
     (@eq (List T)
        (HAppend_hAppend (List T) (List T) (List T) (instHAppendOfAppend (List T) (List_instAppend T)) xs
           xsTail)
        ys))
     : forall T : Type, DecidableEq T -> List T -> List T -> SProp

Arguments Prosa_Util_List_strict_prefix_of T%_type_scope inst_3
  xs ys
```
