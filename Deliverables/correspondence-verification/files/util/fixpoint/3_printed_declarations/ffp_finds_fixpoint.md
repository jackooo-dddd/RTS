# `ffp_finds_fixpoint`

- Kind (Rocq): Corollary
- Rocq: `prosa.util.fixpoint.ffp_finds_fixpoint`
- Lean: `Prosa.Util.Fixpoint.ffp_finds_fixpoint`
- Certificate: `fixpoint_ffp_statement_certificate`

## Official Rocq

```coq
ffp_finds_fixpoint : forall (f : nat -> nat) (h x : nat), find_fixpoint f h = @Some nat x -> x = f x

ffp_finds_fixpoint is not universe polymorphic
Arguments ffp_finds_fixpoint f%function_scope (h x)%nat_scope _
ffp_finds_fixpoint is opaque
Expands to: Constant prosa.util.fixpoint.ffp_finds_fixpoint
Declared in library prosa.util.fixpoint, line 56, characters 12-30
ffp_finds_fixpoint
     : forall (f : nat -> nat) (h x : nat), find_fixpoint f h = @Some nat x -> x = f x
```

## Lean

```lean
Prosa.Util.Fixpoint.ffp_finds_fixpoint : ∀ (f : ℕ → ℕ) (h x : ℕ),
  Prosa.Util.Fixpoint.find_fixpoint f h = some x → x = f x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_ffp_finds_fixpoint
     : forall (f : Nat -> Nat) (h x : Nat),
       @eq (Option_inst1 Nat) (Prosa_Util_Fixpoint_find_fixpoint f h) (Option_some_inst1 Nat x) ->
       @eq Nat x (f x)
```
