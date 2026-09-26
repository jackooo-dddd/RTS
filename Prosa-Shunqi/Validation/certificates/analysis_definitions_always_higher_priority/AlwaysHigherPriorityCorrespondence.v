From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From prosa Require Import analysis.definitions.always_higher_priority.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedAlwaysHigherPriority.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder
  PriorityCoercionCorrespondence.

Module I := ImportedAlwaysHigherPriority.

(** Certificates for [analysis/definitions/always_higher_priority.v].
    The definition: related JLDP policies give related propositions for every
    pair of jobs.  The fact: source side is the exact elaborated type of the
    pinned source declaration (via [type of], the source proof is not used);
    target side is the type of the imported Lean theorem; JLFP policies are
    covered in both directions. *)

Ltac type_of_term t := let T := type of t in exact T.

Lemma ahp_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [Hpq Hqp]. apply I.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ (Hpq (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP (Hqp (sprop_to_prop _ _ HQ q))).
  - intros [Hpq Hqp]. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ (Hpq (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP (Hqp (prop_to_sprop _ _ HQ q))).
Qed.

Section AlwaysHigherPriority.
  Context (Job : eqType).
  Let dJ := pd_decidable_eq Job.

  Theorem always_higher_priority_correspondence pR pL :
    PdJLDPRel Job pR pL ->
    forall j1 j2 : Job,
      PropSPropRel
        (@prosa.analysis.definitions.always_higher_priority.always_higher_priority Job pR j1 j2)
        (I.Prosa_Analysis_Definitions_AlwaysHigherPriority_always_higher_priority Job dJ pL j1 j2).
  Proof.
    intros Hp j1 j2.
    unfold prosa.analysis.definitions.always_higher_priority.always_higher_priority.
    cbn [I.Prosa_Analysis_Definitions_AlwaysHigherPriority_always_higher_priority].
    apply pco_forall_nat => tR tL Ht.
    apply pd_bool_truth_correspondence.
    apply pd_bool_and_related.
    - exact (pd_jldp_field_at Job _ _ tR tL j1 j2 Hp Ht).
    - exact (pd_bool_not_related _ _ (pd_jldp_field_at Job _ _ tR tL j2 j1 Hp Ht)).
  Qed.

  Definition src_always_higher_priority_jlfp : Prop :=
    ltac:(type_of_term (@prosa.analysis.definitions.always_higher_priority.always_higher_priority_jlfp Job)).
  Definition tgt_always_higher_priority_jlfp : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Definitions_AlwaysHigherPriority_always_higher_priority_jlfp Job dJ)).
  Theorem always_higher_priority_jlfp_correspondence :
    PropSPropRel src_always_higher_priority_jlfp tgt_always_higher_priority_jlfp.
  Proof.
    apply pco_forall_jlfp => pR pL Hp.
    apply pco_forall_id => j.
    apply pco_forall_id => j'.
    apply ahp_iff_correspondence.
    - exact (always_higher_priority_correspondence _ _ (JLFP_to_JLDP_correspondence Job pR pL Hp) j j').
    - apply pd_bool_truth_correspondence.
      exact (pd_bool_and_related _ _ _ _ (Hp j j') (pd_bool_not_related _ _ (Hp j' j))).
  Qed.
End AlwaysHigherPriority.
