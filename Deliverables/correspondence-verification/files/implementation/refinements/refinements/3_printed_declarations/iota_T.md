# `iota_T`

- Kind (Rocq): Fixpoint
- Rocq: `prosa.implementation.refinements.refinements.iota_T`
- Lean: `Prosa.Implementation.Refinements.Refinements.iota_T`
- Certificate: `iota_T_correspondence`

## Official Rocq

```coq
iota_T : forall {T : Type}, one_of T -> add_of T -> T -> nat -> seq T

iota_T is not universe polymorphic
Arguments iota_T {T}%_type_scope {one_of0 add_of0} a b%_nat_scope
iota_T is transparent
Expands to: Constant prosa.implementation.refinements.refinements.iota_T
Declared in library prosa.implementation.refinements.refinements, line 233, characters 11-17
@iota_T
     : forall T : Type, one_of T -> add_of T -> T -> nat -> seq T
```

Body:

```coq
iota_T =
fun (T : Type) (one_of0 : one_of T) (add_of0 : add_of T) =>
fix iota_T (a : T) (b : nat) {struct b} : seq T :=
  match b with
  | 0 => [::]
  | b'.+1 => a :: iota_T (a + 1)%C b'
  end
     : forall {T : Type}, one_of T -> add_of T -> T -> nat -> seq T

Arguments iota_T {T}%_type_scope {one_of0 add_of0} a b%_nat_scope
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.iota_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] →
    [Prosa.Implementation.Refinements.Refinements.add_of T] → T → ℕ → List T
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.iota_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] →
    [Prosa.Implementation.Refinements.Refinements.add_of T] → T → ℕ → List T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.one_of T] [Prosa.Implementation.Refinements.Refinements.add_of T]
    x x_1 =>
  Nat.brecOn (motive := fun x => T → List T) x_1 Prosa.Implementation.Refinements.Refinements.iota_T._f x
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_iota_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T -> T -> Nat -> List_inst1 T
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_iota_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_one_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_add_of T)
  (x____at___Prosa_Implementation_Refinements_Refinements3064849274__hygCtx__hyg15 : T)
  (x____at___Prosa_Implementation_Refinements_Refinements3064849274__hygCtx__hyg16 : Nat) =>
Nat_brecOn (fun _ : Nat => T -> List_inst1 T)
  x____at___Prosa_Implementation_Refinements_Refinements3064849274__hygCtx__hyg16
  (Prosa_Implementation_Refinements_Refinements_iota_T__f T
     inst_3
     inst_6)
  x____at___Prosa_Implementation_Refinements_Refinements3064849274__hygCtx__hyg15
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T -> T -> Nat -> List_inst1 T

Arguments Prosa_Implementation_Refinements_Refinements_iota_T T%_type_scope
  inst_3
  inst_6 
  a____at____internal__hyg0 a____at____internal__hyg0%_Nat_scope
```
