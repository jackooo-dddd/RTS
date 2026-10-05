# `fmf_finds_fixpoint`

- Kind (Rocq): Corollary
- Rocq: `prosa.util.fixpoint.fmf_finds_fixpoint`
- Lean: `Prosa.Util.Fixpoint.fmf_finds_fixpoint`
- Certificate: `fixpoint_fmf_finds_statement_certificate`

## Official Rocq

```coq
fmf_finds_fixpoint :
forall (L : nat) (P : pred nat) (f : nat -> nat -> nat) (h x : nat),
find_max_fixpoint L P f h = @Some nat x ->
exists2 a : nat, is_true ((fun A : nat => (A < L) && P A) a) & x = f a x

fmf_finds_fixpoint is not universe polymorphic
Arguments fmf_finds_fixpoint L%nat_scope P f%function_scope (h x)%nat_scope _
fmf_finds_fixpoint is opaque
Expands to: Constant prosa.util.fixpoint.fmf_finds_fixpoint
Declared in library prosa.util.fixpoint, line 287, characters 12-30
fmf_finds_fixpoint
     : forall (L : nat) (P : pred nat) (f : nat -> nat -> nat) (h x : nat),
       find_max_fixpoint L P f h = @Some nat x -> exists2 a : nat, is_true ((a < L) && P a) & x = f a x
```

## Lean

```lean
Prosa.Util.Fixpoint.fmf_finds_fixpoint : ∀ (L : ℕ) (P : ℕ → Bool) (f : ℕ → ℕ → ℕ) (h x : ℕ),
  Prosa.Util.Fixpoint.find_max_fixpoint L P f h = some x → ∃ a, (a < L ∧ P a = true) ∧ x = f a x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_fmf_finds_fixpoint
     : forall (L : Nat) (P : Nat -> Bool) (f : Nat -> Nat -> Nat) (h x : Nat),
       @eq (Option_inst1 Nat) (Prosa_Util_Fixpoint_find_max_fixpoint L P f h) (Option_some_inst1 Nat x) ->
       Exists Nat
         (fun a : Nat =>
          And (And (LT_lt_inst1 Nat instLTNat a L) (@eq Bool (P a) Bool_true)) (@eq Nat x (f a x)))
```
