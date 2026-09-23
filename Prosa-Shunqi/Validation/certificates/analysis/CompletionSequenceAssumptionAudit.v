From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
Require Import OfficialCompletionSequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedCompletionSequenceCombined.
From FoundationCertificates Require Import CompletionSequenceCorrespondence.

(** Exact declaration/type binding is also checked by the certificate's
    elaborated type: it mentions the official source constant and the actual
    imported compiled Lean constant, never a validation-only target model. *)
Check @OfficialCompletionSequence.completion_sequence.
Check ImportedCompletionSequenceCombined.Prosa_Analysis_Definitions_CompletionSequence_completion_sequence.
Check @completion_sequence_correspondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN completion_sequence". exact I. Qed.
Print Assumptions completion_sequence_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END completion_sequence". exact I. Qed.
