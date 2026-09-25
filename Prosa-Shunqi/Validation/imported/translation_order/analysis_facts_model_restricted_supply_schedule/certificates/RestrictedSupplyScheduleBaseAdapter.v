From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRestrictedSupplySchedule.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Artifact-local Boolean and decidable-equality adapters, checked against the
    exact imported production module. No parameterized semantic relation is
    introduced. *)

Inductive RssFalse : SProp := .
Inductive RssTrue : SProp := rss_true_intro.

Definition rss_false_elim (Q : SProp) (H : RssFalse) : Q :=
  match H return Q with end.

Definition rss_false_to_strict (H : RssFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition rss_coq_false_to_target (H : Logic.False) :
    ImportedRestrictedSupplySchedule.False :=
  match H return ImportedRestrictedSupplySchedule.False with end.

Definition rss_bool_to_imported (b : bool) :
    ImportedRestrictedSupplySchedule.Bool :=
  match b with
  | true => ImportedRestrictedSupplySchedule.Bool_true
  | false => ImportedRestrictedSupplySchedule.Bool_false
  end.

Definition rss_bool_to_rocq
    (b : ImportedRestrictedSupplySchedule.Bool) : bool :=
  match b with
  | ImportedRestrictedSupplySchedule.Bool_true => true
  | ImportedRestrictedSupplySchedule.Bool_false => false
  end.

Definition RssBoolRel (bR : bool)
    (bL : ImportedRestrictedSupplySchedule.Bool) : SProp :=
  Lean.eq (rss_bool_to_imported bR) bL.

Lemma rss_bool_source_roundtrip (b : bool) :
  Logic.eq (rss_bool_to_rocq (rss_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma rss_bool_target_roundtrip (b : ImportedRestrictedSupplySchedule.Bool) :
  Lean.eq (rss_bool_to_imported (rss_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition rss_false_ne_true
    (H : Lean.eq ImportedRestrictedSupplySchedule.Bool_false
      ImportedRestrictedSupplySchedule.Bool_true) : RssFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedRestrictedSupplySchedule.Bool_false => RssTrue
    | ImportedRestrictedSupplySchedule.Bool_true => RssFalse
    end
  with
  | Lean.eq_refl => rss_true_intro
  end.

Lemma rss_bool_truth_correspondence bR bL :
  RssBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedRestrictedSupplySchedule.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (rss_false_to_strict (rss_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition rss_decidable_eq (T : eqType) :
    ImportedRestrictedSupplySchedule.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H =>
        ImportedRestrictedSupplySchedule.Decidable_isTrue (Lean.eq x y)
          (coq_eq_to_imported_eq x y H)
    | ReflectF H =>
        ImportedRestrictedSupplySchedule.Decidable_isFalse (Lean.eq x y)
          (fun HL => rss_coq_false_to_target
            (H (imported_eq_to_coq_eq x y HL)))
    end.

(** Stable names used by the already audited restricted-supply proof pattern;
    each abbreviation still targets this file's own imported module. *)
Definition rs_false_elim := rss_false_elim.
Definition rs_false_to_strict := rss_false_to_strict.
Definition rs_coq_false_to_target := rss_coq_false_to_target.
Definition rs_bool_to_imported := rss_bool_to_imported.
Definition rs_bool_to_rocq := rss_bool_to_rocq.
Definition RsBoolRel := RssBoolRel.
Definition rs_false_ne_true := rss_false_ne_true.
Definition rs_bool_truth_correspondence := rss_bool_truth_correspondence.
Definition rs_decidable_eq := rss_decidable_eq.

Print Assumptions rss_bool_truth_correspondence.
Print Assumptions rss_decidable_eq.
