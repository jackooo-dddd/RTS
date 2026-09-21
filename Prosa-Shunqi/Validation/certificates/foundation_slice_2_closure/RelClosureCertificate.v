From mathcomp Require Import ssreflect ssrbool eqtype seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRel.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation RelListCorrespondence.
From prosa Require Import util.rel.

Definition RelPointwise (T : Type) (RR : T -> T -> bool)
    (RL : T -> T -> ImportedRel.Bool) : SProp :=
  forall x y, RelBoolRel (RR x y) (RL x y).

Definition rel_or_forward (P Q : Prop) (PL QL : SProp) :
    PropSPropRel P PL -> PropSPropRel Q QL -> P \/ Q -> Lean.Or PL QL.
Proof.
  intros HP HQ H. destruct H as [p | q].
  - exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
  - exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
Defined.

Definition rel_or_backward_strict (P Q : Prop) (PL QL : SProp) :
    PropSPropRel P PL -> PropSPropRel Q QL ->
    Lean.Or PL QL -> StrictlyInhabited (P \/ Q).
Proof.
  intros HP HQ H. destruct H as [p | q].
  - exact (strictly_inhabits (or_introl (sprop_to_prop _ _ HP p))).
  - exact (strictly_inhabits (or_intror (sprop_to_prop _ _ HQ q))).
Defined.

Lemma total_over_list_correspondence_certificate :
  forall (T : eqType) (deqL : ImportedRel.DecidableEq T)
         (RR : T -> T -> bool) (RL : T -> T -> ImportedRel.Bool)
         (xsR : seq T) (xsL : ImportedRel.List T),
    RelPointwise T RR RL -> RelListRel xsR xsL ->
    PropSPropRel
      (@prosa.util.rel.total_over_list T RR xsR)
      (Prosa_Util_Rel_total_over_list T deqL RL xsL).
Proof.
  intros T deqL RR RL xsR xsL HR Hxs.
  apply prop_sprop_rel_intro.
  - intros H x y HxL HyL.
    have HxR := sprop_to_prop _ _
      (rel_membership_correspondence T x xsR xsL Hxs) HxL.
    have HyR := sprop_to_prop _ _
      (rel_membership_correspondence T y xsR xsL Hxs) HyL.
    apply (rel_or_forward _ _ _ _
      (rel_bool_true_correspondence _ _ (HR x y))
      (rel_bool_true_correspondence _ _ (HR y x))).
    exact (H x y HxR HyR).
  - intro H. apply strictly_inhabits. intros x y HxR HyR.
    have HxL := prop_to_sprop _ _
      (rel_membership_correspondence T x xsR xsL Hxs) HxR.
    have HyL := prop_to_sprop _ _
      (rel_membership_correspondence T y xsR xsL Hxs) HyR.
    exact (interpret_strict _
      (rel_or_backward_strict _ _ _ _
        (rel_bool_true_correspondence _ _ (HR x y))
        (rel_bool_true_correspondence _ _ (HR y x))
        (H x y HxL HyL))).
Qed.

Lemma antisymmetric_over_list_correspondence_certificate :
  forall (T : eqType) (deqL : ImportedRel.DecidableEq T)
         (RR : T -> T -> bool) (RL : T -> T -> ImportedRel.Bool)
         (xsR : seq T) (xsL : ImportedRel.List T),
    RelPointwise T RR RL -> RelListRel xsR xsL ->
    PropSPropRel
      (@prosa.util.rel.antisymmetric_over_list T RR xsR)
      (Prosa_Util_Rel_antisymmetric_over_list T deqL RL xsL).
Proof.
  intros T deqL RR RL xsR xsL HR Hxs.
  apply prop_sprop_rel_intro.
  - intros H x y HxL HyL HxyL HyxL.
    apply coq_eq_to_imported_eq. apply H.
    + exact (sprop_to_prop _ _
        (rel_membership_correspondence T x xsR xsL Hxs) HxL).
    + exact (sprop_to_prop _ _
        (rel_membership_correspondence T y xsR xsL Hxs) HyL).
    + exact (sprop_to_prop _ _
        (rel_bool_true_correspondence _ _ (HR x y)) HxyL).
    + exact (sprop_to_prop _ _
        (rel_bool_true_correspondence _ _ (HR y x)) HyxL).
  - intro H. apply strictly_inhabits.
    intros x y HxR HyR HxyR HyxR.
    have Heq := H x y
      (prop_to_sprop _ _ (rel_membership_correspondence T x xsR xsL Hxs) HxR)
      (prop_to_sprop _ _ (rel_membership_correspondence T y xsR xsL Hxs) HyR)
      (prop_to_sprop _ _ (rel_bool_true_correspondence _ _ (HR x y)) HxyR)
      (prop_to_sprop _ _ (rel_bool_true_correspondence _ _ (HR y x)) HyxR).
    exact (imported_eq_to_coq_eq x y Heq).
Qed.

Print Assumptions total_over_list_correspondence_certificate.
Print Assumptions antisymmetric_over_list_correspondence_certificate.
