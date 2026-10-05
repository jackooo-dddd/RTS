# `fmfs_finds_fixpoint`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.fixpoint.fmfs_finds_fixpoint`
- Lean: `Prosa.Util.Fixpoint.fmfs_finds_fixpoint`
- Certificate: `fixpoint_fmfs_finds_statement_certificate`

## Official Rocq

```coq
fmfs_finds_fixpoint :
forall (f : nat -> nat -> nat) (sp : seq nat) (h x : nat),
is_true (~~ @nilp nat sp) ->
find_max_fixpoint_of_seq f sp h = @Some nat x ->
exists2 a : Equality.sort Datatypes_nat__canonical__eqtype_Equality, is_true (a \in sp) & x = f a x

fmfs_finds_fixpoint is not universe polymorphic
Arguments fmfs_finds_fixpoint f%function_scope sp%seq_scope (h x)%nat_scope _ _
fmfs_finds_fixpoint is opaque
Expands to: Constant prosa.util.fixpoint.fmfs_finds_fixpoint
Declared in library prosa.util.fixpoint, line 211, characters 6-25
fmfs_finds_fixpoint
     : forall (f : nat -> nat -> nat) (sp : seq nat) (h x : nat),
       is_true (~~ @nilp nat sp) ->
       find_max_fixpoint_of_seq f sp h = @Some nat x ->
       exists2 a : Equality.sort Datatypes_nat__canonical__eqtype_Equality, is_true (a \in sp) & x = f a x
```

## Lean

```lean
Prosa.Util.Fixpoint.fmfs_finds_fixpoint : ∀ (f : ℕ → ℕ → ℕ) (sp : List ℕ) (h x : ℕ),
  sp ≠ [] → Prosa.Util.Fixpoint.find_max_fixpoint_of_seq f sp h = some x → ∃ a ∈ sp, x = f a x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_fmfs_finds_fixpoint
     : forall (f : Nat -> Nat -> Nat) (sp : List_inst1 Nat) (h x : Nat),
       Ne (List_inst1 Nat) sp (List_nil_inst1 Nat) ->
       @eq (Option_inst1 Nat) (Prosa_Util_Fixpoint_find_max_fixpoint_of_seq f sp h) (Option_some_inst1 Nat x) ->
       Exists Nat
         (fun a : Nat =>
          And (Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) sp a)
            (@eq Nat x (f a x)))
```
