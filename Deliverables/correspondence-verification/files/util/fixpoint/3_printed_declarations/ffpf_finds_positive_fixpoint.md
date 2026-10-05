# `ffpf_finds_positive_fixpoint`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.fixpoint.ffpf_finds_positive_fixpoint`
- Lean: `Prosa.Util.Fixpoint.ffpf_finds_positive_fixpoint`
- Certificate: `fixpoint_ffpf_positive_statement_certificate`

## Official Rocq

```coq
ffpf_finds_positive_fixpoint :
forall (f : nat -> nat) (h : nat),
@monotone nat leq f ->
is_true (0 < f 1) ->
forall s fuel x : nat, @Some nat x = find_fixpoint_from f s h fuel -> is_true (0 < s) -> is_true (0 < x)

ffpf_finds_positive_fixpoint is not universe polymorphic
Arguments ffpf_finds_positive_fixpoint f%function_scope h%nat_scope H_f_mono F1 (s fuel x)%nat_scope _ _
ffpf_finds_positive_fixpoint is opaque
Expands to: Constant prosa.util.fixpoint.ffpf_finds_positive_fixpoint
Declared in library prosa.util.fixpoint, line 120, characters 10-38
ffpf_finds_positive_fixpoint
     : forall (f : nat -> nat) (h : nat),
       @monotone nat leq f ->
       is_true (0 < f 1) ->
       forall s fuel x : nat,
       @Some nat x = find_fixpoint_from f s h fuel -> is_true (0 < s) -> is_true (0 < x)
```

## Lean

```lean
Prosa.Util.Fixpoint.ffpf_finds_positive_fixpoint : ∀ (f : ℕ → ℕ) (h : ℕ),
  Prosa.Util.Rel.monotone (fun a b => decide (a ≤ b)) f →
    0 < f 1 → ∀ (s fuel x : ℕ), some x = Prosa.Util.Fixpoint.find_fixpoint_from f s h fuel → 0 < s → 0 < x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_ffpf_finds_positive_fixpoint
     : forall (f : Nat -> Nat) (h : Nat),
       Prosa_Util_Rel_monotone_inst1 Nat
         (fun a b : Nat => Decidable_decide (LE_le_inst1 Nat instLENat a b) (Nat_decLe a b)) f ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (f (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))) ->
       forall s fuel x : Nat,
       @eq (Option_inst1 Nat) (Option_some_inst1 Nat x) (Prosa_Util_Fixpoint_find_fixpoint_from f s h fuel) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) s ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) x
```
