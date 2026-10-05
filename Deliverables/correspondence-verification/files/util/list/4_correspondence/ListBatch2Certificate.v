From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedListLast.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ListLastCertificate ListRemCertificate.
From prosa Require Import GeneratedListLastSource.

(** This batch deliberately composes the established generic List, Boolean,
    membership, predicate, filter, Nat, and logical bridges. *)

Lemma lb_bool_false_correspondence (bR : bool)
    (bL : ImportedListLast.Bool) : LlBoolRel bR bL ->
  PropSPropRel (~~ bR) (Lean.eq bL ImportedListLast.Bool_false).
Proof.
  intro Hb.
  have Hfalse : LlBoolRel false ImportedListLast.Bool_false :=
    @Lean.eq_refl _ _.
  have Heq := lr_bool_eq_correspondence bR bL false
    ImportedListLast.Bool_false Hb Hfalse.
  apply prop_sprop_rel_intro.
  - intro Hneg. apply (prop_to_sprop _ _ Heq).
    destruct bR; cbn in Hneg; first discriminate Hneg.
    reflexivity.
  - intro HL. apply strictly_inhabits.
    have HR := sprop_to_prop _ _ Heq HL.
    destruct bR; cbn in HR |- *; first discriminate HR.
    reflexivity.
Qed.

Definition lb_target_filter_in_pred0_statement : SProp :=
  forall (T : eqType) (xs : ImportedListLast.List T)
    (P : T -> ImportedListLast.Bool),
    (forall x : T, lr_target_mem x xs ->
      Lean.eq (P x) ImportedListLast.Bool_false) ->
    Lean.eq (lr_target_filter P xs) (ImportedListLast.List_nil T).

Theorem filter_in_pred0_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_filter_in_pred0
    lb_target_filter_in_pred0_statement.
Proof.
  unfold GeneratedListLastSource.statement_filter_in_pred0,
    lb_target_filter_in_pred0_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T xsL PL HallL.
    pose xsR := lr_to_rocq xsL.
    pose PR := lr_pred_to_rocq PL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have HP : LrPredRel PR PL := lr_pred_surjective PL.
    have HallR : forall x : T, x \in xsR -> ~~ PR x.
    { intros x HmemR.
      have HmemL := prop_to_sprop _ _
        (lr_membership_correspondence T x xsR xsL Hxs) HmemR.
      exact (sprop_to_prop _ _
        (lb_bool_false_correspondence (PR x) (PL x) (HP x))
        (HallL x HmemL)). }
    have HfilterR := Hsource T xsR PR HallR.
    have Hfilter := lr_filter_related T PR PL xsR xsL HP Hxs.
    have Hnil : LrListRel [::] (ImportedListLast.List_nil T) :=
      @Lean.eq_refl _ _.
    exact (prop_to_sprop _ _
      (lr_list_eq_correspondence _ _ _ _ Hfilter Hnil)
      HfilterR).
  - intro Htarget. apply strictly_inhabits.
    intros T xsR PR HallR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have HP : LrPredRel PR (lr_pred_to_imported PR) := lr_pred_canonical PR.
    have HfilterL := Htarget T (lr_to_imported xsR)
      (lr_pred_to_imported PR) (fun x HmemL =>
        prop_to_sprop _ _
          (lb_bool_false_correspondence (PR x)
            (lr_pred_to_imported PR x) (HP x))
          (HallR x (sprop_to_prop _ _
            (lr_membership_correspondence T x xsR
              (lr_to_imported xsR) Hxs) HmemL))).
    have Hfilter := lr_filter_related T PR (lr_pred_to_imported PR)
      xsR (lr_to_imported xsR) HP Hxs.
    have Hnil : LrListRel [::] (ImportedListLast.List_nil T) :=
      @Lean.eq_refl _ _.
    exact (sprop_to_prop _ _
      (lr_list_eq_correspondence _ _ _ _ Hfilter Hnil)
      HfilterL).
Qed.

(** Actual imported computation for the new recursive definition. *)
Definition lb_target_rem_all (T : eqType) (x : T)
    (xs : ImportedListLast.List T) : ImportedListLast.List T :=
  ImportedListLast.Prosa_Util_List_rem_all T (lr_decidable_eq T) x xs.

Definition lb_imported_ite_true {A : Type} (p : SProp)
    (d : ImportedListLast.Decidable p) (hp : p) (x y : A) :
    Lean.eq (ImportedListLast.ite A p d x y) x :=
  match d as d0 return Lean.eq (ImportedListLast.ite A p d0 x y) x with
  | ImportedListLast.Decidable_isFalse hn => ll_false_elim _ (hn hp)
  | ImportedListLast.Decidable_isTrue _ => @Lean.eq_refl A x
  end.

Definition lb_imported_ite_false {A : Type} (p : SProp)
    (d : ImportedListLast.Decidable p) (hn : ImportedListLast.Not p)
    (x y : A) : Lean.eq (ImportedListLast.ite A p d x y) y :=
  match d as d0 return Lean.eq (ImportedListLast.ite A p d0 x y) y with
  | ImportedListLast.Decidable_isFalse _ => @Lean.eq_refl A y
  | ImportedListLast.Decidable_isTrue hp => ll_false_elim _ (hn hp)
  end.

Lemma lb_rem_all_canonical (T : eqType) (x : T) (xs : seq T) :
  LrListRel (GeneratedListLastSource.rem_all x xs)
    (lb_target_rem_all T x (lr_to_imported xs)).
Proof.
  unfold LrListRel.
  induction xs as [|a xs IH].
  - exact (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_generic_rem_all_nil
        T (lr_decidable_eq T) x)).
  - cbn [GeneratedListLastSource.rem_all lr_to_imported].
    have Hstep :=
      ImportedListLast.Prosa_Validation_ListLastInterface_generic_rem_all_cons
        T (lr_decidable_eq T) x a (lr_to_imported xs).
    destruct (@eqP T a x) as [Heq | Hneq].
    + have Hite := lb_imported_ite_true (Lean.eq a x)
        (lr_decidable_eq T a x) (coq_eq_to_imported_eq a x Heq)
        (lb_target_rem_all T x (lr_to_imported xs))
        (ImportedListLast.List_cons T a
          (lb_target_rem_all T x (lr_to_imported xs))).
      exact (sub_imported_eq_trans _ _ _ IH
        (sub_imported_eq_sym _ _
          (sub_imported_eq_trans _ _ _ Hstep Hite))).
    + have Hnot : ImportedListLast.Not (Lean.eq a x) :=
        fun HeqL => ll_coq_false_to_target
          (Hneq (imported_eq_to_coq_eq a x HeqL)).
      have Hite := lb_imported_ite_false (Lean.eq a x)
        (lr_decidable_eq T a x) Hnot
        (lb_target_rem_all T x (lr_to_imported xs))
        (ImportedListLast.List_cons T a
          (lb_target_rem_all T x (lr_to_imported xs))).
      have Hcons := sub_imported_eq_congr
        (ImportedListLast.List_cons T a) _ _ IH.
      exact (sub_imported_eq_trans _ _ _ Hcons
        (sub_imported_eq_sym _ _
          (sub_imported_eq_trans _ _ _ Hstep Hite))).
Qed.

Theorem rem_all_recursive_certificate (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  LrListRel xsR xsL ->
  LrListRel (GeneratedListLastSource.rem_all x xsR)
    (lb_target_rem_all T x xsL).
Proof.
  intro Hxs. unfold LrListRel.
  exact (sub_imported_eq_trans _ _ _ (lb_rem_all_canonical T x xsR)
    (sub_imported_eq_congr (lb_target_rem_all T x) _ _ Hxs)).
Qed.

Lemma lb_not_correspondence (P : Prop) (PL : SProp) :
  PropSPropRel P PL ->
  PropSPropRel (~ P) (ImportedListLast.Not PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros Hnot pL. apply ll_coq_false_to_target. apply Hnot.
    exact (sprop_to_prop _ _ HP pL).
  - intro Hnot. apply strictly_inhabits. intro pR.
    exact (interpret_strict Logic.False
      (ll_false_to_strict (Hnot (prop_to_sprop _ _ HP pR)))).
Qed.

Definition lb_target_nin_rem_all_statement : SProp :=
  forall (T : eqType) (x : T) (xs : ImportedListLast.List T),
    ImportedListLast.Not (lr_target_mem x (lb_target_rem_all T x xs)).

Definition lb_target_in_rem_all_statement : SProp :=
  forall (T : eqType) (a x : T) (xs : ImportedListLast.List T),
    lr_target_mem a (lb_target_rem_all T x xs) -> lr_target_mem a xs.

Theorem nin_rem_all_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_nin_rem_all
    lb_target_nin_rem_all_statement.
Proof.
  unfold GeneratedListLastSource.statement_nin_rem_all,
    lb_target_nin_rem_all_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T x xsL.
    pose xsR := lr_to_rocq xsL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have Hrem := rem_all_recursive_certificate T x xsR xsL Hxs.
    exact (prop_to_sprop _ _
      (lb_not_correspondence _ _
        (lr_membership_correspondence T x _ _ Hrem))
      (Hsource T x xsR)).
  - intro Htarget. apply strictly_inhabits.
    intros T x xsR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have Hrem := rem_all_recursive_certificate T x xsR
      (lr_to_imported xsR) Hxs.
    exact (sprop_to_prop _ _
      (lb_not_correspondence _ _
        (lr_membership_correspondence T x _ _ Hrem))
      (Htarget T x (lr_to_imported xsR))).
Qed.

Theorem in_rem_all_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_in_rem_all
    lb_target_in_rem_all_statement.
Proof.
  unfold GeneratedListLastSource.statement_in_rem_all,
    lb_target_in_rem_all_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T a x xsL HmemL.
    pose xsR := lr_to_rocq xsL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have Hrem := rem_all_recursive_certificate T x xsR xsL Hxs.
    have HmemR := sprop_to_prop _ _
      (lr_membership_correspondence T a _ _ Hrem) HmemL.
    exact (prop_to_sprop _ _
      (lr_membership_correspondence T a _ _ Hxs)
      (Hsource T a x xsR HmemR)).
  - intro Htarget. apply strictly_inhabits.
    intros T a x xsR HmemR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have Hrem := rem_all_recursive_certificate T x xsR
      (lr_to_imported xsR) Hxs.
    have HmemL := prop_to_sprop _ _
      (lr_membership_correspondence T a _ _ Hrem) HmemR.
    exact (sprop_to_prop _ _
      (lr_membership_correspondence T a _ _ Hxs)
      (Htarget T a x (lr_to_imported xsR) HmemL)).
Qed.

(** The monomorphic Nat export has its own imported List/Nat specialization.
    The following certificate connects it to the same source definition using
    the already certified Nat and monomorphic List relations. *)
Definition lb_target_nat_rem_all (x : Lean.Nat)
    (xs : ImportedListLast.List_inst1 Lean.Nat) :=
  ImportedListLast.Prosa_Util_List_rem_all_inst1 Lean.Nat
    ImportedListLast.instDecidableEqNat x xs.

Lemma lb_target_nat_rem_all_nil (x : Lean.Nat) :
  Lean.eq
    (lb_target_nat_rem_all x
      (ImportedListLast.List_nil_inst1 Lean.Nat))
    (ImportedListLast.List_nil_inst1 Lean.Nat).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma lb_target_nat_rem_all_cons (x a : Lean.Nat)
    (xs : ImportedListLast.List_inst1 Lean.Nat) :
  Lean.eq
    (lb_target_nat_rem_all x
      (ImportedListLast.List_cons_inst1 Lean.Nat a xs))
    (ImportedListLast.ite (ImportedListLast.List_inst1 Lean.Nat)
      (Lean.eq a x) (ImportedListLast.instDecidableEqNat a x)
      (lb_target_nat_rem_all x xs)
      (ImportedListLast.List_cons_inst1 Lean.Nat a
        (lb_target_nat_rem_all x xs))).
Proof. exact (@Lean.eq_refl _ _). Qed.

Definition lb_nat_mapped_neq (a x : nat) (Hneq : a <> x) :
    ImportedListLast.Not
      (Lean.eq (sub_nat_to_imported a) (sub_nat_to_imported x)) :=
  fun Heq =>
    let Hdecoded := f_equal sub_nat_to_rocq
      (imported_eq_to_coq_eq _ _ Heq) in
    ll_coq_false_to_target
      (Hneq
        (Logic.eq_trans (Logic.eq_sym (sub_nat_rocq_roundtrip a))
          (Logic.eq_trans Hdecoded (sub_nat_rocq_roundtrip x)))).

Lemma lb_nat_rem_all_canonical (x : nat) (xs : seq nat) :
  LlListRel (GeneratedListLastSource.rem_all x xs)
    (lb_target_nat_rem_all (sub_nat_to_imported x) (ll_to_imported xs)).
Proof.
  unfold LlListRel.
  induction xs as [|a xs IH].
  - exact (sub_imported_eq_sym _ _
      (lb_target_nat_rem_all_nil (sub_nat_to_imported x))).
  - cbn [GeneratedListLastSource.rem_all ll_to_imported].
    have Hstep := lb_target_nat_rem_all_cons
      (sub_nat_to_imported x) (sub_nat_to_imported a) (ll_to_imported xs).
    destruct (@eqP _ a x) as [Heq | Hneq].
    + subst a.
      have Hite := lb_imported_ite_true
        (Lean.eq (sub_nat_to_imported x) (sub_nat_to_imported x))
        (ImportedListLast.instDecidableEqNat
          (sub_nat_to_imported x) (sub_nat_to_imported x))
        (@Lean.eq_refl _ _) (lb_target_nat_rem_all (sub_nat_to_imported x)
          (ll_to_imported xs))
        (ImportedListLast.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported x)
          (lb_target_nat_rem_all (sub_nat_to_imported x)
            (ll_to_imported xs))).
      exact (sub_imported_eq_trans _ _ _ IH
        (sub_imported_eq_sym _ _
          (sub_imported_eq_trans _ _ _ Hstep Hite))).
    + have Hite := lb_imported_ite_false
        (Lean.eq (sub_nat_to_imported a) (sub_nat_to_imported x))
        (ImportedListLast.instDecidableEqNat
          (sub_nat_to_imported a) (sub_nat_to_imported x))
        (lb_nat_mapped_neq a x Hneq)
        (lb_target_nat_rem_all (sub_nat_to_imported x) (ll_to_imported xs))
        (ImportedListLast.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported a)
          (lb_target_nat_rem_all (sub_nat_to_imported x)
            (ll_to_imported xs))).
      have Hcons := sub_imported_eq_congr
        (ImportedListLast.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported a)) _ _ IH.
      exact (sub_imported_eq_trans _ _ _ Hcons
        (sub_imported_eq_sym _ _
          (sub_imported_eq_trans _ _ _ Hstep Hite))).
Qed.

Lemma lb_nat_rem_all_related xR xL xsR xsL :
  SubNatRel xR xL -> LlListRel xsR xsL ->
  LlListRel (GeneratedListLastSource.rem_all xR xsR)
    (lb_target_nat_rem_all xL xsL).
Proof.
  intros Hx Hxs. unfold LlListRel.
  exact (sub_imported_eq_trans _ _ _ (lb_nat_rem_all_canonical xR xsR)
    (sub_imported_eq_congr2 lb_target_nat_rem_all _ _ _ _ Hx Hxs)).
Qed.

Definition lb_target_rem_lt_id_statement : SProp :=
  forall (x : Lean.Nat) (xs : ImportedListLast.List_inst1 Lean.Nat),
    (forall y : Lean.Nat, ll_target_mem y xs -> ll_target_lt x y) ->
    Lean.eq (lb_target_nat_rem_all x xs) xs.

Theorem rem_lt_id_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_rem_lt_id
    lb_target_rem_lt_id_statement.
Proof.
  unfold GeneratedListLastSource.statement_rem_lt_id,
    lb_target_rem_lt_id_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource xL xsL HminL.
    pose xR := sub_nat_to_rocq xL.
    pose xsR := ll_to_rocq xsL.
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hxs : LlListRel xsR xsL := ll_target_roundtrip xsL.
    have HminR : forall y : nat, y \in xsR -> (xR < y)%N.
    { intros y HmemR.
      have Hy : SubNatRel y (sub_nat_to_imported y) := sub_nat_rel_canonical y.
      have HmemL := prop_to_sprop _ _
        (ll_membership_correspondence y (sub_nat_to_imported y)
          xsR xsL Hy Hxs) HmemR.
      exact (sprop_to_prop _ _
        (ll_nat_lt_correspondence xR xL y (sub_nat_to_imported y) Hx Hy)
        (HminL (sub_nat_to_imported y) HmemL)). }
    have HeqR := Hsource xR xsR HminR.
    have Hrem := lb_nat_rem_all_related xR xL xsR xsL Hx Hxs.
    exact (prop_to_sprop _ _
      (ll_list_eq_correspondence _ _ _ _ Hrem Hxs) HeqR).
  - intro Htarget. apply strictly_inhabits.
    intros xR xsR HminR.
    have Hx : SubNatRel xR (sub_nat_to_imported xR) :=
      sub_nat_rel_canonical xR.
    have Hxs : LlListRel xsR (ll_to_imported xsR) := @Lean.eq_refl _ _.
    have HeqL := Htarget (sub_nat_to_imported xR)
      (ll_to_imported xsR) (fun yL HmemL =>
        prop_to_sprop _ _
          (ll_nat_lt_correspondence xR (sub_nat_to_imported xR)
            (sub_nat_to_rocq yL) yL Hx (sub_nat_rel_surjective yL))
          (HminR (sub_nat_to_rocq yL)
            (sprop_to_prop _ _
              (ll_membership_correspondence (sub_nat_to_rocq yL) yL xsR
                (ll_to_imported xsR) (sub_nat_rel_surjective yL) Hxs)
              HmemL))).
    have Hrem := lb_nat_rem_all_related xR (sub_nat_to_imported xR)
      xsR (ll_to_imported xsR) Hx Hxs.
    exact (sprop_to_prop _ _
      (ll_list_eq_correspondence _ _ _ _ Hrem Hxs) HeqL).
Qed.

Print Assumptions filter_in_pred0_statement_certificate.
Print Assumptions rem_all_recursive_certificate.
Print Assumptions nin_rem_all_statement_certificate.
Print Assumptions in_rem_all_statement_certificate.
Print Assumptions rem_lt_id_statement_certificate.
