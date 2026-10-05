# `ffp_finds_none`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.fixpoint.ffp_finds_none`
- Lean: `Prosa.Util.Fixpoint.ffp_finds_none`
- Certificate: `fixpoint_ffp_none_statement_certificate`

## Official Rocq

```coq
ffp_finds_none :
forall (f : nat -> nat) (h : nat),
@monotone nat leq f ->
is_true (0 < f 1) ->
find_fixpoint f h = @None nat -> forall x : nat, is_true (0 < x < h) -> is_true (x != f x)

ffp_finds_none is not universe polymorphic
Arguments ffp_finds_none f%function_scope h%nat_scope H_f_mono F1 _ x%nat_scope _
ffp_finds_none is opaque
Expands to: Constant prosa.util.fixpoint.ffp_finds_none
Declared in library prosa.util.fixpoint, line 178, characters 10-24
ffp_finds_none
     : forall (f : nat -> nat) (h : nat),
       @monotone nat leq f ->
       is_true (0 < f 1) ->
       find_fixpoint f h = @None nat -> forall x : nat, is_true (0 < x < h) -> is_true (x != f x)
```

## Lean

```lean
Prosa.Util.Fixpoint.ffp_finds_none : ∀ (f : ℕ → ℕ) (h : ℕ),
  Prosa.Util.Rel.monotone (fun a b => decide (a ≤ b)) f →
    0 < f 1 → Prosa.Util.Fixpoint.find_fixpoint f h = none → ∀ (x : ℕ), 0 < x ∧ x < h → x ≠ f x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_ffp_finds_none
     : forall (f : Nat -> Nat) (h : Nat),
       Prosa_Util_Rel_monotone_inst1 Nat
         (fun a b : Nat => Decidable_decide (LE_le_inst1 Nat instLENat a b) (Nat_decLe a b)) f ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (f (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))) ->
       @eq (Option_inst1 Nat) (Prosa_Util_Fixpoint_find_fixpoint f h) (Option_none_inst1 Nat) ->
       forall x : Nat,
       And (LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) x)
         (LT_lt_inst1 Nat instLTNat x h) ->
       Ne Nat x (f x)
```
