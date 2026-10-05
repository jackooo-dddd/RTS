# `ffpf_finds_least_fixpoint`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.fixpoint.ffpf_finds_least_fixpoint`
- Lean: `Prosa.Util.Fixpoint.ffpf_finds_least_fixpoint`
- Certificate: `fixpoint_ffpf_least_statement_certificate`

## Official Rocq

```coq
ffpf_finds_least_fixpoint :
forall (f : nat -> nat) (h : nat),
@monotone nat leq f ->
is_true (0 < f 1) ->
forall y s fuel : nat,
find_fixpoint_from f s h fuel = @Some nat y -> forall x : nat, is_true (s <= x < y) -> is_true (x != f x)

ffpf_finds_least_fixpoint is not universe polymorphic
Arguments ffpf_finds_least_fixpoint f%function_scope h%nat_scope H_f_mono F1 (y s fuel)%nat_scope 
  _ x%nat_scope _
ffpf_finds_least_fixpoint is opaque
Expands to: Constant prosa.util.fixpoint.ffpf_finds_least_fixpoint
Declared in library prosa.util.fixpoint, line 88, characters 10-35
ffpf_finds_least_fixpoint
     : forall (f : nat -> nat) (h : nat),
       @monotone nat leq f ->
       is_true (0 < f 1) ->
       forall y s fuel : nat,
       find_fixpoint_from f s h fuel = @Some nat y ->
       forall x : nat, is_true (s <= x < y) -> is_true (x != f x)
```

## Lean

```lean
Prosa.Util.Fixpoint.ffpf_finds_least_fixpoint : ∀ (f : ℕ → ℕ) (h : ℕ),
  Prosa.Util.Rel.monotone (fun a b => decide (a ≤ b)) f →
    0 < f 1 →
      ∀ (y s fuel : ℕ), Prosa.Util.Fixpoint.find_fixpoint_from f s h fuel = some y → ∀ (x : ℕ), s ≤ x ∧ x < y → x ≠ f x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_ffpf_finds_least_fixpoint
     : forall (f : Nat -> Nat) (h : Nat),
       Prosa_Util_Rel_monotone_inst1 Nat
         (fun a b : Nat => Decidable_decide (LE_le_inst1 Nat instLENat a b) (Nat_decLe a b)) f ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (f (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))) ->
       forall y s fuel : Nat,
       @eq (Option_inst1 Nat) (Prosa_Util_Fixpoint_find_fixpoint_from f s h fuel) (Option_some_inst1 Nat y) ->
       forall x : Nat, And (LE_le_inst1 Nat instLENat s x) (LT_lt_inst1 Nat instLTNat x y) -> Ne Nat x (f x)
```
