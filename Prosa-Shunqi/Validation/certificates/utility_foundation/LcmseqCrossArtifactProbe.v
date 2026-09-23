From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedDivMod ImportedLcmseq.

Definition probe_div_divmod (a b : Lean.Nat) : Lean.Nat :=
  ImportedDivMod.HDiv_hDiv_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedDivMod.instHDiv_inst1 Lean.Nat ImportedDivMod.Nat_instDiv) a b.

Definition probe_div_lcmseq (a b : Lean.Nat) : Lean.Nat :=
  ImportedLcmseq.HDiv_hDiv_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedLcmseq.instHDiv_inst1 Lean.Nat ImportedLcmseq.Nat_instDiv) a b.

Definition probe_mod_divmod (a b : Lean.Nat) : Lean.Nat :=
  ImportedDivMod.HMod_hMod_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedDivMod.instHMod_inst1 Lean.Nat ImportedDivMod.Nat_instMod) a b.

Definition probe_mod_lcmseq (a b : Lean.Nat) : Lean.Nat :=
  ImportedLcmseq.HMod_hMod_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedLcmseq.instHMod_inst1 Lean.Nat ImportedLcmseq.Nat_instMod) a b.

Lemma probe_div_cross_artifact (a b : Lean.Nat) :
  Lean.eq (probe_div_divmod a b) (probe_div_lcmseq a b).
Proof. exact (@Lean.eq_refl Lean.Nat (probe_div_lcmseq a b)). Qed.

Lemma probe_mod_cross_artifact (a b : Lean.Nat) :
  Lean.eq (probe_mod_divmod a b) (probe_mod_lcmseq a b).
Proof. exact (@Lean.eq_refl Lean.Nat (probe_mod_lcmseq a b)). Qed.
