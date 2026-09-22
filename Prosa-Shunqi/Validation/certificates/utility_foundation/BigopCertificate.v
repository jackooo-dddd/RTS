From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop ssrfun.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBigop.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  BigopCorrespondence.
From prosa Require Import GeneratedBigopSource.

(** Structural target proposition at the approved representation boundary.
    [Monoid.law] remains the source-side package; its operation and three laws
    are passed to the actual imported Lean theorem through the audited
    unbundling functions in [BigopCorrespondence]. *)
Definition bo_target_big_pred1_seq_statement : SProp :=
  forall (R : Type) (idx : R) (op : Monoid.law idx) (X : eqType)
    (P : X -> ImportedBigop.Bool) (F : X -> R)
    (xs : ImportedBigop.List X) (i : X),
  bo_target_mem i xs ->
  ImportedBigop.List_Nodup X xs ->
  (forall x : X, Lean.eq (P x) (bo_target_decide_eq X x i)) ->
  Lean.eq (bo_target_bigSeq R X idx op P F xs) (F i).

Lemma bo_pred1_condition_correspondence (T : eqType)
    (PR : T -> bool) (PL : T -> ImportedBigop.Bool) (i : T) :
  BoPredRel PR PL ->
  PropSPropRel (PR =1 pred1 i)
    (forall x, Lean.eq (PL x) (bo_target_decide_eq T x i)).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. apply (prop_to_sprop _ _
      (bo_bool_eq_correspondence (PR x) (PL x)
        (x == i) (bo_target_decide_eq T x i)
        (HP x) (bo_decide_eq_related T x i))).
    move: (HR x). by rewrite pred1E.
  - intro HL. apply strictly_inhabits. intro x.
    have Hsource := sprop_to_prop _ _
      (bo_bool_eq_correspondence (PR x) (PL x)
        (x == i) (bo_target_decide_eq T x i)
        (HP x) (bo_decide_eq_related T x i)) (HL x).
    exact Hsource.
Qed.

Lemma bo_result_correspondence (R : Type)
    (source target expected : R) :
  Lean.eq source target ->
  PropSPropRel (Logic.eq source expected) (Lean.eq target expected).
Proof.
  intro Hst. apply prop_sprop_rel_intro.
  - intro Hsource.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Hst)
      (coq_eq_to_imported_eq _ _ Hsource)).
  - intro Htarget. apply strictly_inhabits.
    exact (imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hst Htarget)).
Qed.

Lemma bo_big_pred1_instance_correspondence
    (R : Type) (idx : R) (op : Monoid.law idx) (T : eqType)
    (PR : T -> bool) (PL : T -> ImportedBigop.Bool)
    (F : T -> R) (xsR : seq T) (xsL : ImportedBigop.List T)
    (i : T) :
  BoPredRel PR PL -> BoListRel xsR xsL ->
  PropSPropRel
    (i \in xsR -> uniq xsR -> PR =1 pred1 i ->
      \big[op/idx]_(j <- xsR | PR j) F j = F i)
    (bo_target_mem i xsL -> ImportedBigop.List_Nodup T xsL ->
      (forall x, Lean.eq (PL x) (bo_target_decide_eq T x i)) ->
      Lean.eq (bo_target_bigSeq R T idx op PL F xsL) (F i)).
Proof.
  intros HP Hxs. apply prop_sprop_rel_intro.
  - intros HR HmemL HuniqL HpredL.
    have HmemR := sprop_to_prop _ _
      (bo_membership_correspondence T i xsR xsL Hxs) HmemL.
    have HuniqR := sprop_to_prop _ _
      (bo_uniq_correspondence T xsR xsL Hxs) HuniqL.
    have HpredR := sprop_to_prop _ _
      (bo_pred1_condition_correspondence T PR PL i HP) HpredL.
    have Hresult := HR HmemR HuniqR HpredR.
    exact (prop_to_sprop _ _
      (bo_result_correspondence R _ _ (F i)
        (bo_bigop_related R idx op T PR PL F xsR xsL HP Hxs)) Hresult).
  - intro HL. apply strictly_inhabits.
    intros HmemR HuniqR HpredR.
    have HmemL := prop_to_sprop _ _
      (bo_membership_correspondence T i xsR xsL Hxs) HmemR.
    have HuniqL := prop_to_sprop _ _
      (bo_uniq_correspondence T xsR xsL Hxs) HuniqR.
    have HpredL := prop_to_sprop _ _
      (bo_pred1_condition_correspondence T PR PL i HP) HpredR.
    exact (sprop_to_prop _ _
      (bo_result_correspondence R _ _ (F i)
        (bo_bigop_related R idx op T PR PL F xsR xsL HP Hxs))
      (HL HmemL HuniqL HpredL)).
Qed.

Theorem big_pred1_seq_statement_certificate :
  PropSPropRel GeneratedBigopSource.statement_big_pred1_seq
    bo_target_big_pred1_seq_statement.
Proof.
  unfold GeneratedBigopSource.statement_big_pred1_seq,
    bo_target_big_pred1_seq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource R idx op T PL F xsL i.
    pose PR := bo_pred_to_rocq PL.
    pose xsR := bo_to_rocq xsL.
    have HP := bo_pred_surjective PL.
    have Hxs := bo_list_target_roundtrip xsL.
    exact (prop_to_sprop _ _
      (bo_big_pred1_instance_correspondence
        R idx op T PR PL F xsR xsL i HP Hxs)
      (Hsource R idx op T PR F xsR i)).
  - intro Htarget. apply strictly_inhabits.
    intros R idx op T PR F xsR i.
    pose PL := bo_pred_to_imported PR.
    pose xsL := bo_to_imported xsR.
    have HP := bo_pred_canonical PR.
    have Hxs : BoListRel xsR xsL := @Lean.eq_refl _ _.
    exact (sprop_to_prop _ _
      (bo_big_pred1_instance_correspondence
        R idx op T PR PL F xsR xsL i HP Hxs)
      (Htarget R idx op T PL F xsL i)).
Qed.

Print Assumptions big_pred1_seq_statement_certificate.
