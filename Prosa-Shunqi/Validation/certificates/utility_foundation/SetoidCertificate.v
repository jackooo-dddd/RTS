From Stdlib Require Import Basics Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSetoid.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  SetoidCorrespondence.
Require Import prosa.util.setoid.

(** Exact semantic statement exposed by the source theorem.  It is kept
    separate from the source proof constant so the correspondence proof
    cannot prove equivalence merely by applying that theorem. *)
Definition st_source_leb_eq_statement : Prop :=
  forall a b : bool, prosa.util.setoid.leb a b <->
    (is_true a -> is_true b).

(** Exact semantic statement exposed by the actual imported Lean theorem. *)
Definition st_target_leb_eq_statement : SProp :=
  forall a b : ImportedSetoid.Bool,
    ImportedSetoid.Iff
      (st_target_leb a b)
      (Lean.eq a ImportedSetoid.Bool_true ->
       Lean.eq b ImportedSetoid.Bool_true).

Lemma st_leb_eq_instance_correspondence aR aL bR bL :
  StBoolRel aR aL -> StBoolRel bR bL ->
  PropSPropRel
    (prosa.util.setoid.leb aR bR <->
      (is_true aR -> is_true bR))
    (ImportedSetoid.Iff
      (st_target_leb aL bL)
      (Lean.eq aL ImportedSetoid.Bool_true ->
       Lean.eq bL ImportedSetoid.Bool_true)).
Proof.
  intros Ha Hb. apply st_iff_correspondence.
  - exact (st_leb_correspondence aR aL bR bL Ha Hb).
  - apply st_imp_correspondence.
    + exact (st_bool_truth_correspondence aR aL Ha).
    + exact (st_bool_truth_correspondence bR bL Hb).
Qed.

(** Public inductive correspondence.  This observes the constructor payload,
    rather than identifying two propositions merely because each is true. *)
Theorem leb_constructor_correspondence_certificate :
  forall aR aL bR bL,
    StBoolRel aR aL -> StBoolRel bR bL ->
    PropSPropRel (prosa.util.setoid.leb aR bR)
      (st_target_leb aL bL).
Proof. exact st_leb_correspondence. Qed.

Theorem leb_eq_statement_certificate :
  PropSPropRel st_source_leb_eq_statement
    st_target_leb_eq_statement.
Proof.
  unfold st_source_leb_eq_statement, st_target_leb_eq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource aL bL.
    pose aR := st_bool_to_rocq aL.
    pose bR := st_bool_to_rocq bL.
    exact (prop_to_sprop _ _
      (st_leb_eq_instance_correspondence aR aL bR bL
        (st_bool_target_roundtrip aL)
        (st_bool_target_roundtrip bL))
      (Hsource aR bR)).
  - intro Htarget. apply strictly_inhabits. intros aR bR.
    pose aL := st_bool_to_imported aR.
    pose bL := st_bool_to_imported bR.
    exact (sprop_to_prop _ _
      (st_leb_eq_instance_correspondence aR aL bR bL
        (@Lean.eq_refl ImportedSetoid.Bool aL)
        (@Lean.eq_refl ImportedSetoid.Bool bL))
      (Htarget aL bL)).
Qed.

(** [leqRW] is proof-valued.  Its observable public boundary is its full
    function type; the actual target body is independently guarded by Lean
    definitional equality in [SetoidComputationInterface]. *)
Definition st_source_leqRW_statement : Prop :=
  forall m n : nat, is_true (leq m n) -> (m <= n)%coq_nat.

Definition st_target_leqRW_statement : SProp :=
  forall m n : Lean.Nat, st_target_le m n -> st_target_le m n.

Lemma st_leqRW_instance_correspondence mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  PropSPropRel
    (is_true (leq mR nR) -> (mR <= nR)%coq_nat)
    (st_target_le mL nL -> st_target_le mL nL).
Proof.
  intros Hm Hn. apply st_imp_correspondence.
  - exact (st_nat_bool_le_correspondence mR mL nR nL Hm Hn).
  - exact (st_nat_coq_le_correspondence mR mL nR nL Hm Hn).
Qed.

Theorem leqRW_definition_type_certificate :
  PropSPropRel st_source_leqRW_statement
    st_target_leqRW_statement.
Proof.
  unfold st_source_leqRW_statement, st_target_leqRW_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource mL nL.
    pose mR := sub_nat_to_rocq mL.
    pose nR := sub_nat_to_rocq nL.
    exact (prop_to_sprop _ _
      (st_leqRW_instance_correspondence mR mL nR nL
        (sub_nat_rel_surjective mL) (sub_nat_rel_surjective nL))
      (Hsource mR nR)).
  - intro Htarget. apply strictly_inhabits. intros mR nR.
    pose mL := sub_nat_to_imported mR.
    pose nL := sub_nat_to_imported nR.
    exact (sprop_to_prop _ _
      (st_leqRW_instance_correspondence mR mL nR nL
        (sub_nat_rel_canonical mR) (sub_nat_rel_canonical nR))
      (Htarget mL nL)).
Qed.

Print Assumptions leb_constructor_correspondence_certificate.
Print Assumptions leb_eq_statement_certificate.
Print Assumptions leqRW_definition_type_certificate.
