From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From prosa Require Import GeneratedLcmseqSource.
From FoundationImported Require Import ImportedLcmseq.
From FoundationCertificates Require Import LcmseqCertificate.

Check GeneratedLcmseqSource.statement_int_divides_lcm_in_seq.
Check GeneratedLcmseqSource.statement_lcm_seq_divides_lcm_super.
Check GeneratedLcmseqSource.statement_lcm_seq_is_mult_of_all_ints.
Check GeneratedLcmseqSource.statement_all_pos_implies_lcml_pos.

(** The target theorem constants are used only in these exact-type guards.
    LcmseqCertificate does not import this module or use their proof bodies. *)
Definition lcmt_int_divides_exact_type : lcmt_int_divides_statement :=
  ImportedLcmseq.Prosa_Util_Lcmseq_int_divides_lcm_in_seq.

Definition lcmt_super_divides_exact_type : lcmt_super_divides_statement :=
  ImportedLcmseq.Prosa_Util_Lcmseq_lcm_seq_divides_lcm_super.

Definition lcmt_member_divides_exact_type : lcmt_member_divides_statement :=
  ImportedLcmseq.Prosa_Util_Lcmseq_lcm_seq_is_mult_of_all_ints.

Definition lcmt_all_pos_exact_type : lcmt_all_pos_statement :=
  ImportedLcmseq.Prosa_Util_Lcmseq_all_pos_implies_lcml_pos.
