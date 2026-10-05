# `fmf_is_maximum`

- Kind (Rocq): Corollary
- Rocq: `prosa.util.fixpoint.fmf_is_maximum`
- Lean: `Prosa.Util.Fixpoint.fmf_is_maximum`
- Certificate: `fixpoint_fmf_maximum_statement_certificate`

## Official Rocq

```coq
fmf_is_maximum :
forall (L : nat) (P : pred nat) {f : nat -> nat -> nat} {h s r : nat},
@Some nat r = find_max_fixpoint L P f h ->
is_true ((fun A : nat => (A < L) && P A) s) ->
exists2 v : nat, @Some nat v = find_fixpoint (f s) h & is_true (v <= r)

fmf_is_maximum is not universe polymorphic
Arguments fmf_is_maximum L%nat_scope P {f}%function_scope {h s r}%nat_scope _ _
fmf_is_maximum is opaque
Expands to: Constant prosa.util.fixpoint.fmf_is_maximum
Declared in library prosa.util.fixpoint, line 311, characters 12-26
fmf_is_maximum
     : forall (L : nat) (P : pred nat) (f : nat -> nat -> nat) (h s r : nat),
       @Some nat r = find_max_fixpoint L P f h ->
       is_true ((s < L) && P s) -> exists2 v : nat, @Some nat v = find_fixpoint (f s) h & is_true (v <= r)
```

## Lean

```lean
Prosa.Util.Fixpoint.fmf_is_maximum : ∀ (L : ℕ) (P : ℕ → Bool) (f : ℕ → ℕ → ℕ) (h s r : ℕ),
  some r = Prosa.Util.Fixpoint.find_max_fixpoint L P f h →
    s < L ∧ P s = true → ∃ v, some v = Prosa.Util.Fixpoint.find_fixpoint (f s) h ∧ v ≤ r
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_fmf_is_maximum
     : forall (L : Nat) (P : Nat -> Bool) (f : Nat -> Nat -> Nat) (h s r : Nat),
       @eq (Option_inst1 Nat) (Option_some_inst1 Nat r) (Prosa_Util_Fixpoint_find_max_fixpoint L P f h) ->
       And (LT_lt_inst1 Nat instLTNat s L) (@eq Bool (P s) Bool_true) ->
       Exists Nat
         (fun v : Nat =>
          And (@eq (Option_inst1 Nat) (Option_some_inst1 Nat v) (Prosa_Util_Fixpoint_find_fixpoint (f s) h))
            (LE_le_inst1 Nat instLENat v r))
```
