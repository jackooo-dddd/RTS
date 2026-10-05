# `ffpf_finds_fixpoint`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.fixpoint.ffpf_finds_fixpoint`
- Lean: `Prosa.Util.Fixpoint.ffpf_finds_fixpoint`
- Certificate: `fixpoint_ffpf_statement_certificate`

## Official Rocq

```coq
ffpf_finds_fixpoint :
forall (f : nat -> nat) (h s x fuel : nat), find_fixpoint_from f s h fuel = @Some nat x -> x = f x

ffpf_finds_fixpoint is not universe polymorphic
Arguments ffpf_finds_fixpoint f%function_scope (h s x fuel)%nat_scope _
ffpf_finds_fixpoint is opaque
Expands to: Constant prosa.util.fixpoint.ffpf_finds_fixpoint
Declared in library prosa.util.fixpoint, line 41, characters 8-27
ffpf_finds_fixpoint
     : forall (f : nat -> nat) (h s x fuel : nat), find_fixpoint_from f s h fuel = @Some nat x -> x = f x
```

## Lean

```lean
Prosa.Util.Fixpoint.ffpf_finds_fixpoint : ∀ (f : ℕ → ℕ) (h s x fuel : ℕ),
  Prosa.Util.Fixpoint.find_fixpoint_from f s h fuel = some x → x = f x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_ffpf_finds_fixpoint
     : forall (f : Nat -> Nat) (h s x fuel : Nat),
       @eq (Option_inst1 Nat) (Prosa_Util_Fixpoint_find_fixpoint_from f s h fuel) (Option_some_inst1 Nat x) ->
       @eq Nat x (f x)
```
