# `ffpf_finds_none`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.fixpoint.ffpf_finds_none`
- Lean: `Prosa.Util.Fixpoint.ffpf_finds_none`
- Certificate: `fixpoint_ffpf_none_statement_certificate`

## Official Rocq

```coq
ffpf_finds_none :
forall (f : nat -> nat) (h : nat),
@monotone nat leq f ->
is_true (0 < f 1) ->
forall s fuel : nat,
is_true (s <= f s) ->
is_true (h - s <= fuel) ->
find_fixpoint_from f s h fuel = @None nat -> forall x : nat, is_true (s <= x < h) -> is_true (x != f x)

ffpf_finds_none is not universe polymorphic
Arguments ffpf_finds_none f%function_scope h%nat_scope H_f_mono F1 (s fuel)%nat_scope _ _ _ x%nat_scope _
ffpf_finds_none is opaque
Expands to: Constant prosa.util.fixpoint.ffpf_finds_none
Declared in library prosa.util.fixpoint, line 149, characters 10-25
ffpf_finds_none
     : forall (f : nat -> nat) (h : nat),
       @monotone nat leq f ->
       is_true (0 < f 1) ->
       forall s fuel : nat,
       is_true (s <= f s) ->
       is_true (h - s <= fuel) ->
       find_fixpoint_from f s h fuel = @None nat ->
       forall x : nat, is_true (s <= x < h) -> is_true (x != f x)
```

## Lean

```lean
Prosa.Util.Fixpoint.ffpf_finds_none : ∀ (f : ℕ → ℕ) (h : ℕ),
  Prosa.Util.Rel.monotone (fun a b => decide (a ≤ b)) f →
    0 < f 1 →
      ∀ (s fuel : ℕ),
        s ≤ f s →
          h - s ≤ fuel → Prosa.Util.Fixpoint.find_fixpoint_from f s h fuel = none → ∀ (x : ℕ), s ≤ x ∧ x < h → x ≠ f x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_ffpf_finds_none
     : forall (f : Nat -> Nat) (h : Nat),
       Prosa_Util_Rel_monotone_inst1 Nat
         (fun a b : Nat => Decidable_decide (LE_le_inst1 Nat instLENat a b) (Nat_decLe a b)) f ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (f (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))) ->
       forall s fuel : Nat,
       LE_le_inst1 Nat instLENat s (f s) ->
       LE_le_inst1 Nat instLENat (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) h s) fuel ->
       @eq (Option_inst1 Nat) (Prosa_Util_Fixpoint_find_fixpoint_from f s h fuel) (Option_none_inst1 Nat) ->
       forall x : Nat, And (LE_le_inst1 Nat instLENat s x) (LT_lt_inst1 Nat instLTNat x h) -> Ne Nat x (f x)
```
