# `ffp_finds_least_fixpoint`

- Kind (Rocq): Corollary
- Rocq: `prosa.util.fixpoint.ffp_finds_least_fixpoint`
- Lean: `Prosa.Util.Fixpoint.ffp_finds_least_fixpoint`
- Certificate: `fixpoint_ffp_least_statement_certificate`

## Official Rocq

```coq
ffp_finds_least_fixpoint :
forall (f : nat -> nat) (h : nat),
@monotone nat leq f ->
is_true (0 < f 1) ->
forall x y : nat, is_true (0 < x < y) -> find_fixpoint f h = @Some nat y -> is_true (x != f x)

ffp_finds_least_fixpoint is not universe polymorphic
Arguments ffp_finds_least_fixpoint f%function_scope h%nat_scope H_f_mono F1 (x y)%nat_scope _ _
ffp_finds_least_fixpoint is opaque
Expands to: Constant prosa.util.fixpoint.ffp_finds_least_fixpoint
Declared in library prosa.util.fixpoint, line 111, characters 14-38
ffp_finds_least_fixpoint
     : forall (f : nat -> nat) (h : nat),
       @monotone nat leq f ->
       is_true (0 < f 1) ->
       forall x y : nat, is_true (0 < x < y) -> find_fixpoint f h = @Some nat y -> is_true (x != f x)
```

## Lean

```lean
Prosa.Util.Fixpoint.ffp_finds_least_fixpoint : ∀ (f : ℕ → ℕ) (h : ℕ),
  Prosa.Util.Rel.monotone (fun a b => decide (a ≤ b)) f →
    0 < f 1 → ∀ (x y : ℕ), 0 < x ∧ x < y → Prosa.Util.Fixpoint.find_fixpoint f h = some y → x ≠ f x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_ffp_finds_least_fixpoint
     : forall (f : Nat -> Nat) (h : Nat),
       Prosa_Util_Rel_monotone_inst1 Nat
         (fun a b : Nat => Decidable_decide (LE_le_inst1 Nat instLENat a b) (Nat_decLe a b)) f ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (f (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))) ->
       forall x y : Nat,
       And (LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) x)
         (LT_lt_inst1 Nat instLTNat x y) ->
       @eq (Option_inst1 Nat) (Prosa_Util_Fixpoint_find_fixpoint f h) (Option_some_inst1 Nat y) ->
       Ne Nat x (f x)
```
