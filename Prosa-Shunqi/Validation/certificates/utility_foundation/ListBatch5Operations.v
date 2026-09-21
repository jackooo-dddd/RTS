From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedListLast.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ListLastCertificate ListRemCertificate
  ListBatch2Certificate ListBatch3Operations ListBatch4Operations.
From prosa Require Import GeneratedListLastSource.

(** Operation-level correspondences introduced by the final [util/list.v]
    cluster.  These lemmas expose only computation from the current imported
    artifact; none of the nine target theorem constants is used here. *)

Definition l5_target_nat_map (f : Lean.Nat -> Lean.Nat)
    (xs : ImportedListLast.List_inst1 Lean.Nat) :
    ImportedListLast.List_inst1 Lean.Nat :=
  ImportedListLast.List_map_inst3 Lean.Nat Lean.Nat f xs.

Definition L5NatFunRel (fR : nat -> nat)
    (fL : Lean.Nat -> Lean.Nat) : SProp :=
  forall xR xL, SubNatRel xR xL -> SubNatRel (fR xR) (fL xL).

Lemma l5_nat_map_canonical (fR : nat -> nat)
    (fL : Lean.Nat -> Lean.Nat) : L5NatFunRel fR fL ->
  forall xs : seq nat,
    LlListRel (map fR xs) (l5_target_nat_map fL (ll_to_imported xs)).
Proof.
  intro Hf. induction xs as [|x xs IH].
  - unfold LlListRel, l5_target_nat_map.
    exact (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_nat_map_nil fL)).
  - unfold LlListRel in IH |- *.
    refine (sub_imported_eq_trans _ _ _
      (ll_list_cons_congr _ _ _ _
        (Hf x (sub_nat_to_imported x) (sub_nat_rel_canonical x)) IH) _).
    exact (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_nat_map_cons
        fL (sub_nat_to_imported x)
        (ll_to_imported xs))).
Qed.

Lemma l5_nat_map_related fR fL xsR xsL :
  L5NatFunRel fR fL -> LlListRel xsR xsL ->
  LlListRel (map fR xsR) (l5_target_nat_map fL xsL).
Proof.
  intros Hf Hxs. unfold LlListRel.
  have Hcanon := l5_nat_map_canonical fR fL Hf xsR.
  unfold LlListRel in Hcanon.
  exact (sub_imported_eq_trans _ _ _ Hcanon
    (sub_imported_eq_congr (l5_target_nat_map fL) _ _ Hxs)).
Qed.

Definition l5_target_countP {T : Type}
    (P : T -> ImportedListLast.Bool) (xs : ImportedListLast.List T) :
    Lean.Nat := ImportedListLast.List_countP T P xs.

Definition l5_target_bool_true_ne_false :
    ImportedListLast.Not
      (Lean.eq ImportedListLast.Bool_false ImportedListLast.Bool_true) :=
  fun H => ImportedListLast.Bool_noConfusion_inst1 ImportedListLast.False
    ImportedListLast.Bool_false ImportedListLast.Bool_true H.

Definition l5_target_bool_ne_true_of_eq_false
    (b : ImportedListLast.Bool) :
    Lean.eq ImportedListLast.Bool_false b ->
    ImportedListLast.Not (Lean.eq b ImportedListLast.Bool_true) :=
  fun Hb Htrue => l5_target_bool_true_ne_false
    (sub_imported_eq_trans _ _ _ Hb Htrue).

Lemma l5_countP_canonical (T : Type) (PR : T -> bool)
    (PL : T -> ImportedListLast.Bool) : LrPredRel PR PL ->
  forall xs : seq T,
    SubNatRel (count PR xs) (l5_target_countP PL (lr_to_imported xs)).
Proof.
  intro HP. induction xs as [|a xs IH].
  - unfold SubNatRel, l5_target_countP.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _
        ImportedListLast.Prosa_Validation_ListLastInterface_nat_zero)
      (sub_imported_eq_sym _ _
        (ImportedListLast.Prosa_Validation_ListLastInterface_generic_countP_nil
          T PL))).
  - have Hstep :=
      ImportedListLast.Prosa_Validation_ListLastInterface_generic_countP_cons
        T PL a (lr_to_imported xs).
    have Hb := HP a.
    destruct (PR a) eqn:Hpa.
    + cbn [ll_bool_to_imported] in Hb.
      have Hite := lb_imported_ite_true
        (Lean.eq (PL a) ImportedListLast.Bool_true)
        (ImportedListLast.instDecidableEqBool (PL a)
          ImportedListLast.Bool_true)
        (sub_imported_eq_sym _ _ Hb) ll_target_one ll_target_zero.
      have Hadd := lr_add_related (count PR xs)
        (l5_target_countP PL (lr_to_imported xs)) 1 ll_target_one
        IH lr_one_related.
      rewrite /= Hpa.
      unfold SubNatRel in Hadd |- *.
      have Hsource : Lean.eq
          (sub_nat_to_imported (S (count PR xs)))
          (sub_nat_to_imported (count PR xs + 1)) :=
        coq_eq_to_imported_eq _ _
          (f_equal sub_nat_to_imported
            (Logic.eq_sym (addn1 (count PR xs)))).
      exact (sub_imported_eq_trans _ _ _ Hsource
        (sub_imported_eq_trans _ _ _ Hadd
        (sub_imported_eq_sym _ _
          (sub_imported_eq_trans _ _ _ Hstep
            (sub_imported_eq_congr
              (lr_target_add (l5_target_countP PL (lr_to_imported xs)))
              _ _ Hite))))).
    + cbn [ll_bool_to_imported] in Hb.
      have Hite := lb_imported_ite_false
        (Lean.eq (PL a) ImportedListLast.Bool_true)
        (ImportedListLast.instDecidableEqBool (PL a)
          ImportedListLast.Bool_true)
        (l5_target_bool_ne_true_of_eq_false (PL a) Hb)
        ll_target_one ll_target_zero.
      rewrite /= Hpa.
      unfold SubNatRel in IH |- *.
      exact (sub_imported_eq_trans _ _ _ IH
        (sub_imported_eq_sym _ _
          (sub_imported_eq_trans _ _ _ Hstep
            (sub_imported_eq_congr
              (lr_target_add (l5_target_countP PL (lr_to_imported xs)))
              _ _ Hite)))).
Qed.

Lemma l5_countP_related (T : Type) (PR : T -> bool)
    (PL : T -> ImportedListLast.Bool) (xsR : seq T)
    (xsL : ImportedListLast.List T) :
  LrPredRel PR PL -> LrListRel xsR xsL ->
  SubNatRel (count PR xsR) (l5_target_countP PL xsL).
Proof.
  intros HP Hxs. unfold SubNatRel.
  have Hcanon := l5_countP_canonical T PR PL HP xsR.
  unfold SubNatRel in Hcanon.
  exact (sub_imported_eq_trans _ _ _ Hcanon
    (sub_imported_eq_congr (l5_target_countP PL) _ _ Hxs)).
Qed.

Definition l5_target_nat_countP
    (P : Lean.Nat -> ImportedListLast.Bool)
    (xs : ImportedListLast.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedListLast.List_countP_inst1 Lean.Nat P xs.

Lemma l5_nat_countP_canonical (PR : nat -> bool)
    (PL : Lean.Nat -> ImportedListLast.Bool) : LlPredRel PR PL ->
  forall xs : seq nat,
    SubNatRel (count PR xs)
      (l5_target_nat_countP PL (ll_to_imported xs)).
Proof.
  intro HP. induction xs as [|a xs IH].
  - unfold SubNatRel, l5_target_nat_countP.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _
        ImportedListLast.Prosa_Validation_ListLastInterface_nat_zero)
      (sub_imported_eq_sym _ _
        (ImportedListLast.Prosa_Validation_ListLastInterface_nat_countP_nil
          PL))).
  - have Hstep :=
      ImportedListLast.Prosa_Validation_ListLastInterface_nat_countP_cons
        PL (sub_nat_to_imported a) (ll_to_imported xs).
    have Hb := HP a (sub_nat_to_imported a) (sub_nat_rel_canonical a).
    destruct (PR a) eqn:Hpa.
    + cbn [ll_bool_to_imported] in Hb.
      have Hite := lb_imported_ite_true
        (Lean.eq (PL (sub_nat_to_imported a)) ImportedListLast.Bool_true)
        (ImportedListLast.instDecidableEqBool
          (PL (sub_nat_to_imported a)) ImportedListLast.Bool_true)
        (sub_imported_eq_sym _ _ Hb) ll_target_one ll_target_zero.
      have Hadd := lr_add_related (count PR xs)
        (l5_target_nat_countP PL (ll_to_imported xs)) 1 ll_target_one
        IH lr_one_related.
      rewrite /= Hpa.
      unfold SubNatRel in Hadd |- *.
      have Hsource : Lean.eq
          (sub_nat_to_imported (S (count PR xs)))
          (sub_nat_to_imported (count PR xs + 1)) :=
        coq_eq_to_imported_eq _ _
          (f_equal sub_nat_to_imported
            (Logic.eq_sym (addn1 (count PR xs)))).
      exact (sub_imported_eq_trans _ _ _ Hsource
        (sub_imported_eq_trans _ _ _ Hadd
          (sub_imported_eq_sym _ _
            (sub_imported_eq_trans _ _ _ Hstep
              (sub_imported_eq_congr
                (lr_target_add
                  (l5_target_nat_countP PL (ll_to_imported xs)))
                _ _ Hite))))).
    + cbn [ll_bool_to_imported] in Hb.
      have Hite := lb_imported_ite_false
        (Lean.eq (PL (sub_nat_to_imported a)) ImportedListLast.Bool_true)
        (ImportedListLast.instDecidableEqBool
          (PL (sub_nat_to_imported a)) ImportedListLast.Bool_true)
        (l5_target_bool_ne_true_of_eq_false
          (PL (sub_nat_to_imported a)) Hb)
        ll_target_one ll_target_zero.
      rewrite /= Hpa.
      unfold SubNatRel in IH |- *.
      exact (sub_imported_eq_trans _ _ _ IH
        (sub_imported_eq_sym _ _
          (sub_imported_eq_trans _ _ _ Hstep
            (sub_imported_eq_congr
              (lr_target_add
                (l5_target_nat_countP PL (ll_to_imported xs)))
              _ _ Hite)))).
Qed.

Lemma l5_nat_countP_related PR PL xsR xsL :
  LlPredRel PR PL -> LlListRel xsR xsL ->
  SubNatRel (count PR xsR) (l5_target_nat_countP PL xsL).
Proof.
  intros HP Hxs. unfold SubNatRel.
  have Hcanon := l5_nat_countP_canonical PR PL HP xsR.
  unfold SubNatRel in Hcanon.
  exact (sub_imported_eq_trans _ _ _ Hcanon
    (sub_imported_eq_congr (l5_target_nat_countP PL) _ _ Hxs)).
Qed.

Definition l5_target_prefix_of (T : eqType)
    (xs ys : ImportedListLast.List T) : SProp :=
  ImportedListLast.Prosa_Util_List_prefix_of
    (T : Type) (lr_decidable_eq T) xs ys.

Definition l5_target_strict_prefix_of (T : eqType)
    (xs ys : ImportedListLast.List T) : SProp :=
  ImportedListLast.Prosa_Util_List_strict_prefix_of
    (T : Type) (lr_decidable_eq T) xs ys.

Definition l5_target_shift_points_pos
    (xs : ImportedListLast.List_inst1 Lean.Nat) (s : Lean.Nat) :=
  ImportedListLast.Prosa_Util_List_shift_points_pos xs s.

Definition l5_target_shift_points_neg
    (xs : ImportedListLast.List_inst1 Lean.Nat) (s : Lean.Nat) :=
  ImportedListLast.Prosa_Util_List_shift_points_neg xs s.

Print Assumptions l5_nat_map_related.
Print Assumptions l5_countP_related.
Print Assumptions l5_nat_countP_related.
