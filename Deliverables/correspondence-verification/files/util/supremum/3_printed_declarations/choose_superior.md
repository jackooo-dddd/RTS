# `choose_superior`

- Kind (Rocq): Definition
- Rocq: `prosa.util.supremum.choose_superior`
- Lean: `Prosa.Util.Supremum.choose_superior`
- Certificate: `choose_superior_correspondence_certificate`

## Official Rocq

```coq
choose_superior :
forall {T : eqType},
rel (Equality.sort T) -> Equality.sort T -> option (Equality.sort T) -> option (Equality.sort T)

choose_superior is not universe polymorphic
Arguments choose_superior {T} R x maybe_y
choose_superior is transparent
Expands to: Constant prosa.util.supremum.choose_superior
Declared in library prosa.util.supremum, line 21, characters 13-28
@choose_superior
     : forall T : eqType,
       rel (Equality.sort T) -> Equality.sort T -> option (Equality.sort T) -> option (Equality.sort T)
```

Body:

```coq
choose_superior =
fun (T : eqType) (R : rel (Equality.sort T)) (x : Equality.sort T) (maybe_y : option (Equality.sort T)) =>
match maybe_y with
| @Some _ y => if R x y then @Some (Equality.sort T) x else @Some (Equality.sort T) y
| @None _ => @Some (Equality.sort T) x
end
     : forall {T : eqType},
       rel (Equality.sort T) -> Equality.sort T -> option (Equality.sort T) -> option (Equality.sort T)

Arguments choose_superior {T} R x maybe_y
```

## Lean

```lean
@Prosa.Util.Supremum.choose_superior : {T : Type u_1} → (T → T → Bool) → T → Option T → Option T
def Prosa.Util.Supremum.choose_superior.{u} : {T : Type u} → (T → T → Bool) → T → Option T → Option T :=
fun {T} R x maybeY =>
  match maybeY with
  | some y => if R x y = true then some x else some y
  | none => some x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Supremum_choose_superior
     : forall T : Type, (T -> T -> Bool) -> T -> Option T -> Option T
```

Body:

```coq
Prosa_Util_Supremum_choose_superior@{u Lean.u+1.0} =
fun (T : Type) (R : T -> T -> Bool) (x : T) (maybeY : Option T) =>
Prosa_Util_Supremum_choose_superior_match_1 T (fun _ : Option T => Option T) maybeY
  (fun y : T =>
   ite (Option T) (@eq Bool (R x y) Bool_true) (instDecidableEqBool (R x y) Bool_true) 
     (Option_some T x) (Option_some T y))
  (fun _ : Unit => Option_some T x)
     : forall T : Type, (T -> T -> Bool) -> T -> Option T -> Option T

Arguments Prosa_Util_Supremum_choose_superior T%_type_scope R%_function_scope x maybeY
```
