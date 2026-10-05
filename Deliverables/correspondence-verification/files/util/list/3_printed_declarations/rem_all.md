# `rem_all`

- Kind (Rocq): Fixpoint
- Rocq: `prosa.util.list.rem_all`
- Lean: `Prosa.Util.List.rem_all`
- Certificate: `rem_all_recursive_certificate`

## Official Rocq

```coq
rem_all : forall {X : eqType}, Equality.sort X -> seq (Equality.sort X) -> seq (Equality.sort X)

rem_all is not universe polymorphic
Arguments rem_all {X} x xs%seq_scope
rem_all is transparent
Expands to: Constant prosa.util.list.rem_all
Declared in library prosa.util.list, line 578, characters 0-163
@rem_all
     : forall X : eqType, Equality.sort X -> seq (Equality.sort X) -> seq (Equality.sort X)
```

Body:

```coq
rem_all =
fix rem_all (X : eqType) (x : Equality.sort X) (xs : seq (Equality.sort X)) {struct xs} :
    seq (Equality.sort X) :=
  match xs with
  | [::] => [::]
  | a :: xs0 => if a == x then rem_all X x xs0 else a :: rem_all X x xs0
  end
     : forall {X : eqType}, Equality.sort X -> seq (Equality.sort X) -> seq (Equality.sort X)

Arguments rem_all {X} x xs%seq_scope
```

## Lean

```lean
@Prosa.Util.List.rem_all : {T : Type u_1} → [DecidableEq T] → T → List T → List T
def Prosa.Util.List.rem_all.{u_1} : {T : Type u_1} → [DecidableEq T] → T → List T → List T :=
fun {T} [DecidableEq T] x x_1 => List.brecOn x_1 (Prosa.Util.List.rem_all._f x)
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_rem_all
     : forall T : Type, DecidableEq T -> T -> List T -> List T
```

Body:

```coq
Prosa_Util_List_rem_all@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (T : Type) (inst_3 : DecidableEq T) 
  (x : T) (x____at___Prosa_Util_List2990169706__hygCtx__hyg12 : List T) =>
List_brecOn T (fun _ : List T => List T) x____at___Prosa_Util_List2990169706__hygCtx__hyg12
  (Prosa_Util_List_rem_all__f T inst_3 x)
     : forall T : Type, DecidableEq T -> T -> List T -> List T

Arguments Prosa_Util_List_rem_all T%_type_scope inst_3 
  x x____at___Init_Prelude4042049376__hygCtx__hyg13
```
