From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBigcat ImportedSumSequence.

Definition bigcat_sumseq_list_identity (T : Type)
    (xs : ImportedBigcat.List T) : ImportedSumSequence.List T := xs.

Definition bigcat_sumseq_bool_identity
    (b : ImportedBigcat.Bool) : ImportedSumSequence.Bool := b.

Definition bigcat_lean_nat_identity (n : Lean.Nat) : Lean.Nat := n.
