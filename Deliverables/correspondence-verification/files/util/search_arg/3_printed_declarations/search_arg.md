# `search_arg`

- Kind (Rocq): Fixpoint
- Rocq: `prosa.util.search_arg.search_arg`
- Lean: `Prosa.Util.SearchArg.search_arg`
- Certificate: `search_arg_definition_certificate`

## Official Rocq

```coq
search_arg : forall {T : Type}, (nat -> T) -> pred T -> rel T -> nat -> nat -> option nat

search_arg is not universe polymorphic
Arguments search_arg {T}%type_scope f%function_scope P R (a b)%nat_scope
search_arg is transparent
Expands to: Constant prosa.util.search_arg.search_arg
Declared in library prosa.util.search_arg, line 60, characters 2-336
@search_arg
     : forall T : Type, (nat -> T) -> pred T -> rel T -> nat -> nat -> option nat
```

Body:

```coq
search_arg =
fun (T : Type) (f : nat -> T) (P : pred T) (R : rel T) =>
fix search_arg (a b : nat) {struct b} : option nat :=
  if a < b
  then
   match b with
   | 0 => @None nat
   | b'.+1 =>
       match search_arg a b' with
       | @Some _ x => if P (f b') && R (f b') (f x) then @Some nat b' else @Some nat x
       | @None _ => if P (f b') then @Some nat b' else @None nat
       end
   end
  else @None nat
     : forall {T : Type}, (nat -> T) -> pred T -> rel T -> nat -> nat -> option nat

Arguments search_arg {T}%type_scope f%function_scope P R (a b)%nat_scope
```

## Lean

```lean
@Prosa.Util.SearchArg.search_arg : {T : Type u_1} → (ℕ → T) → (T → Bool) → (T → T → Bool) → ℕ → ℕ → Option ℕ
def Prosa.Util.SearchArg.search_arg.{u_1} : {T : Type u_1} → (ℕ → T) → (T → Bool) → (T → T → Bool) → ℕ → ℕ → Option ℕ :=
fun {T} f P R a b => Nat.brecOn b (Prosa.Util.SearchArg.search_arg._f f P R a)
```

## Lean, imported into Rocq

```coq
Prosa_Util_SearchArg_search_arg
     : forall T : Type, (Nat -> T) -> (T -> Bool) -> (T -> T -> Bool) -> Nat -> Nat -> Option_inst1 Nat
```

Body:

```coq
Prosa_Util_SearchArg_search_arg@{u_1 Lean.u_1+1.0} =
fun (T : Type) (f : Nat -> T) (P : T -> Bool) (R : T -> T -> Bool) (a b : Nat) =>
Nat_brecOn (fun _ : Nat => Option_inst1 Nat) b (Prosa_Util_SearchArg_search_arg__f T f P R a)
     : forall T : Type, (Nat -> T) -> (T -> Bool) -> (T -> T -> Bool) -> Nat -> Nat -> Option_inst1 Nat

Arguments Prosa_Util_SearchArg_search_arg T%_type_scope (f P R)%_function_scope (a b)%_Nat_scope
```
