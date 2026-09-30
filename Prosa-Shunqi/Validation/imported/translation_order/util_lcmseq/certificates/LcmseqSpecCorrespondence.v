From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From prosa Require Import LcmseqSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedLcmseqSpec.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  LcmseqBaseAdapter LcmseqDivModAdapter LcmseqCorrespondence LcmseqCertificate.

Module I := ImportedLcmseqSpec.
Module S := LcmseqSemanticSource.LcmseqSemanticSource.

(** The per-declaration certificates of [util/lcmseq.v] under the names the
    publisher expects.  Each is stated against the extracted source
    declaration and the type of the actual imported Lean constant (so each is
    also an exact-type guard), and is proved by the corresponding certificate
    of the chain. *)

Ltac type_of_term t := let T := type of t in exact T.

Theorem lcml_correspondence xsR xsL :
  LcmoNatListRel xsR xsL -> SubNatRel (S.lcml xsR) (I.Prosa_Util_Lcmseq_lcml xsL).
Proof. exact (lcmo_lcml_correspondence xsR xsL). Qed.

Definition tgt_int_divides_lcm_in_seq : SProp :=
  ltac:(type_of_term I.Prosa_Util_Lcmseq_int_divides_lcm_in_seq).
Theorem int_divides_lcm_in_seq_correspondence :
  PropSPropRel S.statement_int_divides_lcm_in_seq tgt_int_divides_lcm_in_seq.
Proof. exact lcmt_int_divides_certificate. Qed.

Definition tgt_lcm_seq_divides_lcm_super : SProp :=
  ltac:(type_of_term I.Prosa_Util_Lcmseq_lcm_seq_divides_lcm_super).
Theorem lcm_seq_divides_lcm_super_correspondence :
  PropSPropRel S.statement_lcm_seq_divides_lcm_super tgt_lcm_seq_divides_lcm_super.
Proof. exact lcmt_super_divides_certificate. Qed.

Definition tgt_lcm_seq_is_mult_of_all_ints : SProp :=
  ltac:(type_of_term I.Prosa_Util_Lcmseq_lcm_seq_is_mult_of_all_ints).
Theorem lcm_seq_is_mult_of_all_ints_correspondence :
  PropSPropRel S.statement_lcm_seq_is_mult_of_all_ints tgt_lcm_seq_is_mult_of_all_ints.
Proof. exact lcmt_member_divides_certificate. Qed.

Definition tgt_all_pos_implies_lcml_pos : SProp :=
  ltac:(type_of_term I.Prosa_Util_Lcmseq_all_pos_implies_lcml_pos).
Theorem all_pos_implies_lcml_pos_correspondence :
  PropSPropRel S.statement_all_pos_implies_lcml_pos tgt_all_pos_implies_lcml_pos.
Proof. exact lcmt_all_pos_certificate. Qed.
