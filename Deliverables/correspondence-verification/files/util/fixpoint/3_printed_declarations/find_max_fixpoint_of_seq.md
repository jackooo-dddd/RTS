# `find_max_fixpoint_of_seq`

- Kind (Rocq): Definition
- Rocq: `prosa.util.fixpoint.find_max_fixpoint_of_seq`
- Lean: `Prosa.Util.Fixpoint.find_max_fixpoint_of_seq`
- Certificate: `fixpoint_max_of_seq_correspondence`

## Official Rocq

```coq
find_max_fixpoint_of_seq : (nat -> nat -> nat) -> seq nat -> nat -> option nat

find_max_fixpoint_of_seq is not universe polymorphic
Arguments find_max_fixpoint_of_seq f%function_scope sp%seq_scope h%nat_scope
find_max_fixpoint_of_seq is transparent
Expands to: Constant prosa.util.fixpoint.find_max_fixpoint_of_seq
Declared in library prosa.util.fixpoint, line 202, characters 11-35
find_max_fixpoint_of_seq
     : (nat -> nat -> nat) -> seq nat -> nat -> option nat
```

Body:

```coq
find_max_fixpoint_of_seq =
fun (f : nat -> nat -> nat) (sp : seq nat) (h : nat) =>
let is_some :=
  fun
    opt : Equality.sort
            (Datatypes_option__canonical__eqtype_Equality Datatypes_nat__canonical__eqtype_Equality) =>
  opt != @None (Equality.sort Datatypes_nat__canonical__eqtype_Equality) in
let fixpoints := [seq find_fixpoint (f s) h | s <- sp] in
let max :=
  @bigop.bigop.body nat (option nat) 0 fixpoints
    (fun fp : option nat => @bigop.BigBody nat (option nat) fp maxn (is_some fp) (odflt 0 fp))
  in
if
 @all
   (Equality.sort (Datatypes_option__canonical__eqtype_Equality Datatypes_nat__canonical__eqtype_Equality))
   is_some fixpoints
then @Some nat max
else @None nat
     : (nat -> nat -> nat) -> seq nat -> nat -> option nat

Arguments find_max_fixpoint_of_seq f%function_scope sp%seq_scope h%nat_scope
```

## Lean

```lean
Prosa.Util.Fixpoint.find_max_fixpoint_of_seq : (ℕ → ℕ → ℕ) → List ℕ → ℕ → Option ℕ
```

Body:

```lean
def Prosa.Util.Fixpoint.find_max_fixpoint_of_seq : (ℕ → ℕ → ℕ) → List ℕ → ℕ → Option ℕ :=
fun f sp h =>
  have fixpoints := List.map (fun s => Prosa.Util.Fixpoint.find_fixpoint (f s) h) sp;
  have max := Prosa.Util.Minmax.bigMaxListCond fixpoints Option.isSome fun fp => fp.getD 0;
  if fixpoints.all Option.isSome = true then some max else none
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_find_max_fixpoint_of_seq
     : (Nat -> Nat -> Nat) -> List_inst1 Nat -> Nat -> Option_inst1 Nat
```

Body:

```coq
Prosa_Util_Fixpoint_find_max_fixpoint_of_seq@{} =
fun (f : Nat -> Nat -> Nat) (sp : List_inst1 Nat) (h : Nat) =>
let fixpoints :=
  List_map_inst3 Nat (Option_inst1 Nat) (fun s : Nat => Prosa_Util_Fixpoint_find_fixpoint (f s) h) sp in
let max :=
  Prosa_Util_Minmax_bigMaxListCond_inst1 (Option_inst1 Nat) fixpoints (Option_isSome_inst1 Nat)
    (fun fp : Option_inst1 Nat => Option_getD_inst1 Nat fp (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
  in
ite (Option_inst1 Nat)
  (@eq Bool (List_all_inst1 (Option_inst1 Nat) fixpoints (Option_isSome_inst1 Nat)) Bool_true)
  (instDecidableEqBool (List_all_inst1 (Option_inst1 Nat) fixpoints (Option_isSome_inst1 Nat)) Bool_true)
  (Option_some_inst1 Nat max) (Option_none_inst1 Nat)
     : (Nat -> Nat -> Nat) -> List_inst1 Nat -> Nat -> Option_inst1 Nat

Arguments Prosa_Util_Fixpoint_find_max_fixpoint_of_seq f%_function_scope sp x%_Nat_scope
```
