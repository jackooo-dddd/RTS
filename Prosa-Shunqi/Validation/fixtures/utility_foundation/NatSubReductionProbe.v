From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedNat.

Definition probe_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedNat.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedNat.instHSub_inst1 Lean.Nat ImportedNat.instSubNat) a b.

Lemma probe_sub_zero (a : Lean.Nat) :
  Lean.eq (probe_sub a Lean.Nat_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma probe_sub_succ (a b : Lean.Nat) :
  Lean.eq (probe_sub a (Lean.Nat_succ b))
    (ImportedNat.Nat_pred (probe_sub a b)).
Proof. exact (@Lean.eq_refl Lean.Nat (ImportedNat.Nat_pred (probe_sub a b))). Qed.

Lemma probe_pred_zero :
  Lean.eq (ImportedNat.Nat_pred Lean.Nat_zero) Lean.Nat_zero.
Proof. exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero). Qed.

Lemma probe_pred_succ (a : Lean.Nat) :
  Lean.eq (ImportedNat.Nat_pred (Lean.Nat_succ a)) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.
