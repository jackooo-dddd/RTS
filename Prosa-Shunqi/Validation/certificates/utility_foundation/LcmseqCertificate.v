From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From prosa Require Import GeneratedLcmseqSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedLcmseq.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  LcmseqDivModAdapter LcmseqCorrespondence.

(** These target propositions use the exact imported operations. Separate
    guards will typecheck the actual imported theorem constants against them;
    the correspondence proofs below never use those theorem constants. *)

Definition lcmt_int_divides_statement : SProp :=
  forall (x : Lean.Nat) (xs : ImportedLcmseq.List_inst1 Lean.Nat),
  lcmseqdm_imported_dvd x
    (lcmo_target_lcml (ImportedLcmseq.List_cons_inst1 Lean.Nat x xs)).

Definition lcmt_super_divides_statement : SProp :=
  forall (x : Lean.Nat) (xs : ImportedLcmseq.List_inst1 Lean.Nat),
  lcmseqdm_imported_dvd (lcmo_target_lcml xs)
    (lcmo_target_lcml (ImportedLcmseq.List_cons_inst1 Lean.Nat x xs)).

Definition lcmt_member_divides_statement : SProp :=
  forall (x : Lean.Nat) (xs : ImportedLcmseq.List_inst1 Lean.Nat),
  lcmo_target_mem x xs ->
  lcmseqdm_imported_dvd x (lcmo_target_lcml xs).

Definition lcmt_all_pos_statement : SProp :=
  forall (xs : ImportedLcmseq.List_inst1 Lean.Nat),
  (forall x : Lean.Nat,
    lcmo_target_mem x xs ->
    lcmseqdm_imported_lt lcmseqdm_imported_zero x) ->
  lcmseqdm_imported_lt lcmseqdm_imported_zero (lcmo_target_lcml xs).

Theorem lcmt_int_divides_certificate :
  PropSPropRel GeneratedLcmseqSource.statement_int_divides_lcm_in_seq
    lcmt_int_divides_statement.
Proof.
  unfold GeneratedLcmseqSource.statement_int_divides_lcm_in_seq,
    lcmt_int_divides_statement.
  apply prop_sprop_rel_intro.
  - intros H xL xsL.
    set (xR := sub_nat_to_rocq xL).
    set (xsR := lcmo_nat_list_to_rocq xsL).
    apply (prop_to_sprop _ _
      (lcmseqdm_dvd_correspondence
        (GeneratedLcmseqSource.lcml (xR :: xsR))
        (lcmo_target_lcml (ImportedLcmseq.List_cons_inst1 Lean.Nat xL xsL))
        xR xL
        (lcmo_lcml_correspondence _ _
          (lcmo_nat_list_cons_related _ _ _ _
            (sub_nat_rel_surjective xL)
            (lcmo_nat_list_rel_surjective xsL)))
        (sub_nat_rel_surjective xL))).
    exact (H xR xsR).
  - intro H. apply strictly_inhabits. intros xR xsR.
    exact (sprop_to_prop _ _
      (lcmseqdm_dvd_correspondence
        (GeneratedLcmseqSource.lcml (xR :: xsR))
        (lcmo_target_lcml
          (ImportedLcmseq.List_cons_inst1 Lean.Nat
            (sub_nat_to_imported xR) (lcmo_nat_list_to_imported xsR)))
        xR (sub_nat_to_imported xR)
        (lcmo_lcml_correspondence _ _
          (lcmo_nat_list_cons_related _ _ _ _
            (sub_nat_rel_canonical xR)
            (lcmo_nat_list_rel_canonical xsR)))
        (sub_nat_rel_canonical xR))
      (H (sub_nat_to_imported xR) (lcmo_nat_list_to_imported xsR))).
Qed.

Theorem lcmt_all_pos_certificate :
  PropSPropRel GeneratedLcmseqSource.statement_all_pos_implies_lcml_pos
    lcmt_all_pos_statement.
Proof.
  unfold GeneratedLcmseqSource.statement_all_pos_implies_lcml_pos,
    lcmt_all_pos_statement.
  apply prop_sprop_rel_intro.
  - intros H xsL HposL.
    set (xsR := lcmo_nat_list_to_rocq xsL).
    apply (prop_to_sprop _ _
      (lcmseqdm_lt_correspondence 0 lcmseqdm_imported_zero
        (GeneratedLcmseqSource.lcml xsR) (lcmo_target_lcml xsL)
        (sub_nat_rel_canonical 0)
        (lcmo_lcml_correspondence _ _
          (lcmo_nat_list_rel_surjective xsL)))).
    apply H. intros xR HmemR.
    exact (sprop_to_prop _ _
      (lcmseqdm_lt_correspondence 0 lcmseqdm_imported_zero
        xR (sub_nat_to_imported xR)
        (sub_nat_rel_canonical 0) (sub_nat_rel_canonical xR))
      (HposL (sub_nat_to_imported xR)
        (prop_to_sprop _ _
          (lcmo_membership_correspondence xR (sub_nat_to_imported xR)
            xsR xsL (sub_nat_rel_canonical xR)
            (lcmo_nat_list_rel_surjective xsL)) HmemR))).
  - intro H. apply strictly_inhabits. intros xsR HposR.
    exact (sprop_to_prop _ _
      (lcmseqdm_lt_correspondence 0 lcmseqdm_imported_zero
        (GeneratedLcmseqSource.lcml xsR)
        (lcmo_target_lcml (lcmo_nat_list_to_imported xsR))
        (sub_nat_rel_canonical 0)
        (lcmo_lcml_correspondence _ _
          (lcmo_nat_list_rel_canonical xsR)))
      (H (lcmo_nat_list_to_imported xsR)
        (fun xL HmemL =>
          prop_to_sprop _ _
            (lcmseqdm_lt_correspondence 0 lcmseqdm_imported_zero
              (sub_nat_to_rocq xL) xL
              (sub_nat_rel_canonical 0)
              (sub_nat_rel_surjective xL))
            (HposR (sub_nat_to_rocq xL)
              (sprop_to_prop _ _
                (lcmo_membership_correspondence
                  (sub_nat_to_rocq xL) xL xsR
                  (lcmo_nat_list_to_imported xsR)
                  (sub_nat_rel_surjective xL)
                  (lcmo_nat_list_rel_canonical xsR)) HmemL))))).
Qed.

Theorem lcmt_member_divides_certificate :
  PropSPropRel GeneratedLcmseqSource.statement_lcm_seq_is_mult_of_all_ints
    lcmt_member_divides_statement.
Proof.
  unfold GeneratedLcmseqSource.statement_lcm_seq_is_mult_of_all_ints,
    lcmt_member_divides_statement.
  apply prop_sprop_rel_intro.
  - intros H xL xsL HmemL.
    set (xR := sub_nat_to_rocq xL).
    set (xsR := lcmo_nat_list_to_rocq xsL).
    apply (prop_to_sprop _ _
      (lcmseqdm_dvd_correspondence
        (GeneratedLcmseqSource.lcml xsR) (lcmo_target_lcml xsL)
        xR xL
        (lcmo_lcml_correspondence _ _
          (lcmo_nat_list_rel_surjective xsL))
        (sub_nat_rel_surjective xL))).
    apply H.
    exact (sprop_to_prop _ _
      (lcmo_membership_correspondence xR xL xsR xsL
        (sub_nat_rel_surjective xL)
        (lcmo_nat_list_rel_surjective xsL)) HmemL).
  - intro H. apply strictly_inhabits. intros xR xsR HmemR.
    exact (sprop_to_prop _ _
      (lcmseqdm_dvd_correspondence
        (GeneratedLcmseqSource.lcml xsR)
        (lcmo_target_lcml (lcmo_nat_list_to_imported xsR))
        xR (sub_nat_to_imported xR)
        (lcmo_lcml_correspondence _ _
          (lcmo_nat_list_rel_canonical xsR))
        (sub_nat_rel_canonical xR))
      (H (sub_nat_to_imported xR) (lcmo_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (lcmo_membership_correspondence xR (sub_nat_to_imported xR)
            xsR (lcmo_nat_list_to_imported xsR)
            (sub_nat_rel_canonical xR)
            (lcmo_nat_list_rel_canonical xsR)) HmemR))).
Qed.

Theorem lcmt_super_divides_certificate :
  PropSPropRel GeneratedLcmseqSource.statement_lcm_seq_divides_lcm_super
    lcmt_super_divides_statement.
Proof.
  unfold GeneratedLcmseqSource.statement_lcm_seq_divides_lcm_super,
    lcmt_super_divides_statement.
  apply prop_sprop_rel_intro.
  - intros H xL xsL.
    set (xR := sub_nat_to_rocq xL).
    set (xsR := lcmo_nat_list_to_rocq xsL).
    apply (prop_to_sprop _ _
      (lcmseqdm_dvd_correspondence
        (GeneratedLcmseqSource.lcml (xR :: xsR))
        (lcmo_target_lcml (ImportedLcmseq.List_cons_inst1 Lean.Nat xL xsL))
        (GeneratedLcmseqSource.lcml xsR) (lcmo_target_lcml xsL)
        (lcmo_lcml_correspondence _ _
          (lcmo_nat_list_cons_related _ _ _ _
            (sub_nat_rel_surjective xL)
            (lcmo_nat_list_rel_surjective xsL)))
        (lcmo_lcml_correspondence _ _
          (lcmo_nat_list_rel_surjective xsL)))).
    exact (H xR xsR).
  - intro H. apply strictly_inhabits. intros xR xsR.
    exact (sprop_to_prop _ _
      (lcmseqdm_dvd_correspondence
        (GeneratedLcmseqSource.lcml (xR :: xsR))
        (lcmo_target_lcml
          (ImportedLcmseq.List_cons_inst1 Lean.Nat
            (sub_nat_to_imported xR) (lcmo_nat_list_to_imported xsR)))
        (GeneratedLcmseqSource.lcml xsR)
        (lcmo_target_lcml (lcmo_nat_list_to_imported xsR))
        (lcmo_lcml_correspondence _ _
          (lcmo_nat_list_cons_related _ _ _ _
            (sub_nat_rel_canonical xR)
            (lcmo_nat_list_rel_canonical xsR)))
        (lcmo_lcml_correspondence _ _
          (lcmo_nat_list_rel_canonical xsR)))
      (H (sub_nat_to_imported xR) (lcmo_nat_list_to_imported xsR))).
Qed.

Print Assumptions lcmt_int_divides_certificate.
Print Assumptions lcmt_super_divides_certificate.
Print Assumptions lcmt_member_divides_certificate.
Print Assumptions lcmt_all_pos_certificate.
