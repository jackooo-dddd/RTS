From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedListLast ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.
From prosa Require Import GeneratedListLastSource.

(** Order- and multiplicity-preserving representation of the exact monomorphic
    imported [List Nat] carrier used by this freshly exported artifact. *)
Fixpoint ll_to_imported (xs : seq nat) :
    ImportedListLast.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedListLast.List_nil_inst1 Lean.Nat
  | x :: xs' => ImportedListLast.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported x) (ll_to_imported xs')
  end.

Fixpoint ll_to_rocq (xs : ImportedListLast.List_inst1 Lean.Nat) : seq nat :=
  match xs with
  | ImportedListLast.List_nil_inst1 => [::]
  | ImportedListLast.List_cons_inst1 x xs' =>
      sub_nat_to_rocq x :: ll_to_rocq xs'
  end.

Definition LlListRel (xsR : seq nat)
    (xsL : ImportedListLast.List_inst1 Lean.Nat) : SProp :=
  Lean.eq (ll_to_imported xsR) xsL.

Definition ll_list_cons_congr (x y : Lean.Nat)
    (xs ys : ImportedListLast.List_inst1 Lean.Nat) :
  Lean.eq x y -> Lean.eq xs ys ->
  Lean.eq (ImportedListLast.List_cons_inst1 Lean.Nat x xs)
    (ImportedListLast.List_cons_inst1 Lean.Nat y ys) :=
  fun Hx Hxs => sub_imported_eq_congr2
    (ImportedListLast.List_cons_inst1 Lean.Nat) x y xs ys Hx Hxs.

Lemma ll_source_roundtrip (xs : seq nat) :
  Logic.eq (ll_to_rocq (ll_to_imported xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn; first reflexivity.
  f_equal.
  - exact (sub_nat_rocq_roundtrip x).
  - exact IH.
Qed.

Lemma ll_target_roundtrip (xs : ImportedListLast.List_inst1 Lean.Nat) :
  Lean.eq (ll_to_imported (ll_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ (ImportedListLast.List_nil_inst1 Lean.Nat)).
  - exact (ll_list_cons_congr _ _ _ _
      (sub_nat_imported_roundtrip x) IH).
Qed.

Definition ll_false_elim (Q : SProp) (H : ImportedListLast.False) : Q :=
  match H return Q with end.

Definition ll_false_to_strict (H : ImportedListLast.False) :
    StrictlyInhabited Logic.False := match H with end.

Definition ll_coq_false_to_target (H : Logic.False) :
    ImportedListLast.False := match H return ImportedListLast.False with end.

Definition ll_list_eq_correspondence xsR xsL ysR ysL :
  LlListRel xsR xsL -> LlListRel ysR ysL ->
  PropSPropRel (Logic.eq xsR ysR) (Lean.eq xsL ysL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Hx) Hy).
  - intro Hxy. apply strictly_inhabits.
    have Hmaps : Lean.eq (ll_to_imported xsR) (ll_to_imported ysR) :=
      sub_imported_eq_trans _ _ _ Hx
        (sub_imported_eq_trans _ _ _ Hxy (sub_imported_eq_sym _ _ Hy)).
    have Hback := f_equal ll_to_rocq (imported_eq_to_coq_eq _ _ Hmaps).
    exact (Logic.eq_trans (Logic.eq_sym (ll_source_roundtrip xsR))
      (Logic.eq_trans Hback (ll_source_roundtrip ysR))).
Defined.

Definition ll_target_nonempty
    (xs : ImportedListLast.List_inst1 Lean.Nat) : SProp :=
  ImportedListLast.Ne (ImportedListLast.List_inst1 Lean.Nat) xs
    (ImportedListLast.List_nil_inst1 Lean.Nat).

Lemma ll_nonempty_correspondence (xs : seq nat) :
  PropSPropRel (xs <> [::]) (ll_target_nonempty (ll_to_imported xs)).
Proof.
  apply prop_sprop_rel_intro.
  - intros Hne Heq.
    have Hmaps := f_equal ll_to_rocq (imported_eq_to_coq_eq _ _ Heq).
    apply ll_coq_false_to_target. apply Hne.
    exact (Logic.eq_trans (Logic.eq_sym (ll_source_roundtrip xs)) Hmaps).
  - intro Hne. apply strictly_inhabits. intro Heq.
    have Htarget : Lean.eq (ll_to_imported xs)
        (ImportedListLast.List_nil_inst1 Lean.Nat) :=
      coq_eq_to_imported_eq _ _ (f_equal ll_to_imported Heq).
    exact (interpret_strict Logic.False (ll_false_to_strict (Hne Htarget))).
Qed.

Definition ll_target_last
    (xs : ImportedListLast.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedListLast.Prosa_Util_List_last0 xs.

Lemma ll_last_canonical (xs : seq nat) :
  SubNatRel (GeneratedListLastSource.last0 xs)
    (ll_target_last (ll_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero).
  - destruct xs as [|y ys].
    + exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported x)).
    + exact IH.
Qed.

Definition ll_target_append
    (xs ys : ImportedListLast.List_inst1 Lean.Nat) :
    ImportedListLast.List_inst1 Lean.Nat :=
  ImportedListLast.HAppend_hAppend_inst7
    (ImportedListLast.List_inst1 Lean.Nat)
    (ImportedListLast.List_inst1 Lean.Nat)
    (ImportedListLast.List_inst1 Lean.Nat)
    (ImportedListLast.instHAppendOfAppend_inst1
      (ImportedListLast.List_inst1 Lean.Nat)
      (ImportedListLast.List_instAppend_inst1 Lean.Nat)) xs ys.

Lemma ll_append_canonical (xs ys : seq nat) :
  Lean.eq (ll_target_append (ll_to_imported xs) (ll_to_imported ys))
    (ll_to_imported (xs ++ ys)).
Proof.
  induction xs as [|x xs IH].
  - exact (ImportedListLast.Prosa_Validation_ListLastInterface_append_nil
      (ll_to_imported ys)).
  - exact (sub_imported_eq_trans _ _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_append_cons
        (sub_nat_to_imported x) (ll_to_imported xs) (ll_to_imported ys))
      (sub_imported_eq_congr
        (ImportedListLast.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported x)) _ _ IH)).
Qed.

Definition ll_bool_to_imported (b : bool) : ImportedListLast.Bool :=
  match b with
  | true => ImportedListLast.Bool_true
  | false => ImportedListLast.Bool_false
  end.

Definition ll_target_pred (P : nat -> bool) :
    Lean.Nat -> ImportedListLast.Bool :=
  fun n => ll_bool_to_imported (P (sub_nat_to_rocq n)).

Definition ll_target_filter (P : Lean.Nat -> ImportedListLast.Bool)
    (xs : ImportedListLast.List_inst1 Lean.Nat) :=
  ImportedListLast.List_filter_inst1 Lean.Nat P xs.

Lemma ll_target_filter_match (b : bool) (x : Lean.Nat)
    (tail : ImportedListLast.List_inst1 Lean.Nat) :
  Lean.eq
    (ImportedListLast.Prosa_Validation_ListLastInterface_filter_cons_match_1
      (fun _ : ImportedListLast.Bool =>
        ImportedListLast.List_inst1 Lean.Nat)
      (ll_bool_to_imported b)
      (fun _ : ImportedListLast.Unit =>
        ImportedListLast.List_cons_inst1 Lean.Nat x tail)
      (fun _ : ImportedListLast.Unit => tail))
    (match b with
     | true => ImportedListLast.List_cons_inst1 Lean.Nat x tail
     | false => tail
     end).
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma ll_filter_branch_canonical (b : bool) (x : nat) (filtered : seq nat)
    (tail : ImportedListLast.List_inst1 Lean.Nat)
    (IH : Lean.eq tail (ll_to_imported filtered)) :
  Lean.eq
    (match b with
     | true => ImportedListLast.List_cons_inst1 Lean.Nat
         (sub_nat_to_imported x) tail
     | false => tail
     end)
    (ll_to_imported
      (match b with
       | true => x :: filtered
       | false => filtered
       end)).
Proof.
  destruct b; cbn; first exact (sub_imported_eq_congr
    (ImportedListLast.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported x)) _ _ IH).
  exact IH.
Qed.

Lemma ll_source_filter_cons (P : nat -> bool) (x : nat) (xs : seq nat) :
  Logic.eq
    (match P x with
     | true => x :: [seq y <- xs | P y]
     | false => [seq y <- xs | P y]
     end)
    [seq y <- x :: xs | P y].
Proof. cbn. destruct (P x); reflexivity. Qed.

Lemma ll_filter_canonical (P : nat -> bool) (xs : seq nat) :
  Lean.eq (ll_target_filter (ll_target_pred P) (ll_to_imported xs))
    (ll_to_imported [seq x <- xs | P x]).
Proof.
  induction xs as [|x xs IH].
  - exact (ImportedListLast.Prosa_Validation_ListLastInterface_filter_nil
      (ll_target_pred P)).
  - refine (sub_imported_eq_trans _ _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_filter_cons
        (ll_target_pred P) (sub_nat_to_imported x) (ll_to_imported xs)) _).
    unfold ll_target_pred. rw (sub_nat_rocq_roundtrip x).
    unfold ll_target_filter, ll_target_pred in IH.
    refine (sub_imported_eq_trans _ _ _
      (ll_target_filter_match (P x) (sub_nat_to_imported x)
        (ImportedListLast.List_filter_inst1 Lean.Nat
          (fun n => ll_bool_to_imported (P (sub_nat_to_rocq n)))
          (ll_to_imported xs))) _).
    refine (sub_imported_eq_trans _ _ _
      (ll_filter_branch_canonical (P x) x
        [seq y <- xs | P y]
        (ImportedListLast.List_filter_inst1 Lean.Nat
          (fun n => ll_bool_to_imported (P (sub_nat_to_rocq n)))
          (ll_to_imported xs)) IH) _).
    exact (coq_eq_to_imported_eq _ _
      (f_equal ll_to_imported (ll_source_filter_cons P x xs))).
Qed.

(** Reusable logical lifting for the closed theorem statements.  These
    combinators quantify over both representations; they do not assume the
    source or target theorem being validated. *)
Lemma ll_nat_related_back nR nL :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. unfold SubNatRel in H.
  have Hback := f_equal sub_nat_to_rocq
    (imported_eq_to_coq_eq _ _ H).
  exact (Logic.eq_trans (Logic.eq_sym Hback) (sub_nat_rocq_roundtrip nR)).
Qed.

Lemma ll_nonempty_related xsR xsL : LlListRel xsR xsL ->
  PropSPropRel (xsR <> [::]) (ll_target_nonempty xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intros Hne Heq. apply ll_coq_false_to_target. apply Hne.
    have Hmap : Lean.eq (ll_to_imported xsR)
        (ImportedListLast.List_nil_inst1 Lean.Nat) :=
      sub_imported_eq_trans _ _ _ Hxs Heq.
    have Hback := f_equal ll_to_rocq (imported_eq_to_coq_eq _ _ Hmap).
    exact (Logic.eq_trans (Logic.eq_sym (ll_source_roundtrip xsR)) Hback).
  - intro Hne. apply strictly_inhabits. intro Heq.
    have Hmapped : Lean.eq (ll_to_imported xsR)
        (ImportedListLast.List_nil_inst1 Lean.Nat) :=
      coq_eq_to_imported_eq _ _ (f_equal ll_to_imported Heq).
    exact (interpret_strict Logic.False
      (ll_false_to_strict
        (Hne (sub_imported_eq_trans _ _ _
          (sub_imported_eq_sym _ _ Hxs) Hmapped)))).
Qed.

Lemma ll_last_related xsR xsL : LlListRel xsR xsL ->
  SubNatRel (GeneratedListLastSource.last0 xsR) (ll_target_last xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _
    (ll_last_canonical xsR)
    (sub_imported_eq_congr ll_target_last _ _ Hxs)).
Qed.

Lemma ll_cons_related xR xL xsR xsL :
  SubNatRel xR xL -> LlListRel xsR xsL ->
  LlListRel (xR :: xsR)
    (ImportedListLast.List_cons_inst1 Lean.Nat xL xsL).
Proof.
  intros Hx Hxs. exact (ll_list_cons_congr _ _ _ _ Hx Hxs).
Qed.

Lemma ll_nil_related : LlListRel [::]
    (ImportedListLast.List_nil_inst1 Lean.Nat).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma ll_append_related xsR xsL ysR ysL :
  LlListRel xsR xsL -> LlListRel ysR ysL ->
  LlListRel (xsR ++ ysR) (ll_target_append xsL ysL).
Proof.
  intros Hxs Hys. unfold LlListRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (ll_append_canonical xsR ysR))
    (sub_imported_eq_congr2 ll_target_append _ _ _ _ Hxs Hys)).
Qed.

Lemma ll_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros HPQ pL. apply (prop_to_sprop _ _ HQ).
    apply HPQ. exact (sprop_to_prop _ _ HP pL).
  - intro HL. apply strictly_inhabits. intro pR.
    apply (sprop_to_prop _ _ HQ).
    apply HL. exact (prop_to_sprop _ _ HP pR).
Qed.

Lemma ll_forall_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall nR, PR nR) (forall nL, PL nL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR nL. exact (prop_to_sprop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL))
      (HR (sub_nat_to_rocq nL))).
  - intro HL. apply strictly_inhabits. intro nR.
    exact (sprop_to_prop _ _
      (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR))
      (HL (sub_nat_to_imported nR))).
Qed.

Lemma ll_forall_list_correspondence
    (PR : seq nat -> Prop)
    (PL : ImportedListLast.List_inst1 Lean.Nat -> SProp) :
  (forall xsR xsL, LlListRel xsR xsL ->
    PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (forall xsR, PR xsR) (forall xsL, PL xsL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR xsL. exact (prop_to_sprop _ _
      (HP (ll_to_rocq xsL) xsL (ll_target_roundtrip xsL))
      (HR (ll_to_rocq xsL))).
  - intro HL. apply strictly_inhabits. intro xsR.
    exact (sprop_to_prop _ _
      (HP xsR (ll_to_imported xsR)
        (@Lean.eq_refl _ (ll_to_imported xsR)))
      (HL (ll_to_imported xsR))).
Qed.

Lemma ll_exists_list_correspondence
    (PR : seq nat -> Prop)
    (PL : ImportedListLast.List_inst1 Lean.Nat -> SProp) :
  (forall xsR xsL, LlListRel xsR xsL ->
    PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (exists xsR, PR xsR)
    (ImportedListLast.Exists (ImportedListLast.List_inst1 Lean.Nat) PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [xsR HR]. exact (ImportedListLast.Exists_intro
      (ImportedListLast.List_inst1 Lean.Nat) PL (ll_to_imported xsR)
      (prop_to_sprop _ _
        (HP xsR (ll_to_imported xsR)
          (@Lean.eq_refl _ (ll_to_imported xsR))) HR)).
  - intro HL. destruct HL as [xsL HL]. apply strictly_inhabits.
    exists (ll_to_rocq xsL). exact (sprop_to_prop _ _
      (HP (ll_to_rocq xsL) xsL (ll_target_roundtrip xsL)) HL).
Qed.

Definition ll_bool_to_rocq (b : ImportedListLast.Bool) : bool :=
  match b with
  | ImportedListLast.Bool_true => true
  | ImportedListLast.Bool_false => false
  end.

Lemma ll_bool_rocq_roundtrip (b : bool) :
  Logic.eq (ll_bool_to_rocq (ll_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma ll_bool_imported_roundtrip (b : ImportedListLast.Bool) :
  Lean.eq (ll_bool_to_imported (ll_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition LlBoolRel (bR : bool) (bL : ImportedListLast.Bool) : SProp :=
  Lean.eq (ll_bool_to_imported bR) bL.

Lemma ll_bool_true_correspondence bR bL : LlBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedListLast.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (ll_false_to_strict
          (ImportedListLast.Bool_noConfusion_inst1 ImportedListLast.False
            ImportedListLast.Bool_false ImportedListLast.Bool_true
            (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Definition LlPredRel (PR : nat -> bool)
    (PL : Lean.Nat -> ImportedListLast.Bool) : SProp :=
  forall nR nL, SubNatRel nR nL -> LlBoolRel (PR nR) (PL nL).

Definition ll_pred_from_imported
    (PL : Lean.Nat -> ImportedListLast.Bool) : nat -> bool :=
  fun n => ll_bool_to_rocq (PL (sub_nat_to_imported n)).

Lemma ll_pred_rel_surjective (PL : Lean.Nat -> ImportedListLast.Bool) :
  LlPredRel (ll_pred_from_imported PL) PL.
Proof.
  intros nR nL Hn. unfold LlBoolRel, ll_pred_from_imported.
  exact (sub_imported_eq_trans _ _ _
    (ll_bool_imported_roundtrip (PL (sub_nat_to_imported nR)))
    (sub_imported_eq_congr PL _ _ Hn)).
Qed.

Lemma ll_pred_rel_canonical (PR : nat -> bool) :
  LlPredRel PR (ll_target_pred PR).
Proof.
  intros nR nL Hn. unfold LlBoolRel, ll_target_pred.
  have Hback : Logic.eq (sub_nat_to_rocq nL) nR :=
    ll_nat_related_back nR nL Hn.
  rewrite Hback. exact (@Lean.eq_refl _ _).
Qed.

Lemma ll_forall_pred_correspondence
    (PRop : (nat -> bool) -> Prop)
    (PLop : (Lean.Nat -> ImportedListLast.Bool) -> SProp) :
  (forall PR PL, LlPredRel PR PL ->
    PropSPropRel (PRop PR) (PLop PL)) ->
  PropSPropRel (forall PR, PRop PR) (forall PL, PLop PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR PL. exact (prop_to_sprop _ _
      (HP (ll_pred_from_imported PL) PL (ll_pred_rel_surjective PL))
      (HR (ll_pred_from_imported PL))).
  - intro HL. apply strictly_inhabits. intro PR.
    exact (sprop_to_prop _ _
      (HP PR (ll_target_pred PR) (ll_pred_rel_canonical PR))
      (HL (ll_target_pred PR))).
Qed.

Definition ll_target_filter_match_value (b : ImportedListLast.Bool)
    (x : Lean.Nat) (tail : ImportedListLast.List_inst1 Lean.Nat) :=
  ImportedListLast.Prosa_Validation_ListLastInterface_filter_cons_match_1
    (fun _ : ImportedListLast.Bool =>
      ImportedListLast.List_inst1 Lean.Nat) b
    (fun _ : ImportedListLast.Unit =>
      ImportedListLast.List_cons_inst1 Lean.Nat x tail)
    (fun _ : ImportedListLast.Unit => tail).

Lemma ll_filter_with_pred_canonical PR PL : LlPredRel PR PL ->
  forall xs : seq nat,
  Lean.eq (ll_target_filter PL (ll_to_imported xs))
    (ll_to_imported [seq x <- xs | PR x]).
Proof.
  intro HP. induction xs as [|x xs IH].
  - exact (ImportedListLast.Prosa_Validation_ListLastInterface_filter_nil PL).
  - refine (sub_imported_eq_trans _ _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_filter_cons
        PL (sub_nat_to_imported x) (ll_to_imported xs)) _).
    have Hb := HP x (sub_nat_to_imported x) (sub_nat_rel_canonical x).
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (fun b => ll_target_filter_match_value b
          (sub_nat_to_imported x) (ll_target_filter PL (ll_to_imported xs)))
        _ _ (sub_imported_eq_sym _ _ Hb)) _).
    refine (sub_imported_eq_trans _ _ _
      (ll_target_filter_match (PR x) (sub_nat_to_imported x)
        (ll_target_filter PL (ll_to_imported xs))) _).
    refine (sub_imported_eq_trans _ _ _
      (ll_filter_branch_canonical (PR x) x
        [seq y <- xs | PR y] (ll_target_filter PL (ll_to_imported xs)) IH) _).
    exact (coq_eq_to_imported_eq _ _
      (f_equal ll_to_imported (ll_source_filter_cons PR x xs))).
Qed.

Lemma ll_filter_related PR PL xsR xsL :
  LlPredRel PR PL -> LlListRel xsR xsL ->
  LlListRel [seq x <- xsR | PR x] (ll_target_filter PL xsL).
Proof.
  intros HP Hxs. unfold LlListRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (ll_filter_with_pred_canonical PR PL HP xsR))
    (sub_imported_eq_congr (ll_target_filter PL) _ _ Hxs)).
Qed.

Definition ll_target_length
    (xs : ImportedListLast.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedListLast.List_length_inst1 Lean.Nat xs.

Definition ll_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedListLast.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedListLast.instHSub_inst1 Lean.Nat
      ImportedListLast.instSubNat) a b.

Definition ll_target_zero : Lean.Nat :=
  ImportedListLast.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedListLast.instOfNatNat Lean.Nat_zero).

Definition ll_target_one : Lean.Nat :=
  ImportedListLast.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ Lean.Nat_zero)
    (ImportedListLast.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition ll_target_getD
    (xs : ImportedListLast.List_inst1 Lean.Nat) (n : Lean.Nat) : Lean.Nat :=
  ImportedListLast.List_getD_inst1 Lean.Nat xs n ll_target_zero.

Lemma ll_length_canonical (xs : seq nat) :
  SubNatRel (size xs) (ll_target_length (ll_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _
        ImportedListLast.Prosa_Validation_ListLastInterface_nat_zero)
      (sub_imported_eq_sym _ _
        ImportedListLast.Prosa_Validation_ListLastInterface_length_nil)).
  - unfold SubNatRel in IH |- *.
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr Lean.Nat_succ _ _ IH) _).
    exact (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_length_cons_succ
        (sub_nat_to_imported x) (ll_to_imported xs))).
Qed.

Lemma ll_length_related xsR xsL : LlListRel xsR xsL ->
  SubNatRel (size xsR) (ll_target_length xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _
    (ll_length_canonical xsR)
    (sub_imported_eq_congr ll_target_length _ _ Hxs)).
Qed.

Lemma ll_target_pred_canonical (n : nat) :
  Lean.eq (ImportedListLast.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported n.-1).
Proof. destruct n; exact (@Lean.eq_refl _ _). Qed.

Lemma ll_sub_one_related nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ll_target_sub nL ll_target_one).
Proof.
  intro Hn. unfold SubNatRel, ll_target_sub.
  refine (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (ll_target_pred_canonical nR)) _).
  refine (sub_imported_eq_trans _ _ _
    (sub_imported_eq_congr ImportedListLast.Nat_pred _ _ Hn) _).
  exact (sub_imported_eq_sym _ _
    (ImportedListLast.Prosa_Validation_ListLastInterface_sub_one nL)).
Qed.

Lemma ll_getD_canonical (xs : seq nat) (n : nat) :
  Lean.eq (ll_target_getD (ll_to_imported xs) (sub_nat_to_imported n))
    (sub_nat_to_imported (nth O xs n)).
Proof.
  unfold ll_target_getD, ll_target_zero.
  revert n. induction xs as [|x xs IH]; intro n.
  - rewrite nth_nil. cbn [sub_nat_to_imported ll_to_imported].
    exact (sub_imported_eq_trans _ _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_getD_nil
        (sub_nat_to_imported n))
      ImportedListLast.Prosa_Validation_ListLastInterface_nat_zero).
  - destruct n as [|n].
    + refine (sub_imported_eq_trans _ _ _
        (sub_imported_eq_sym _ _
          (sub_imported_eq_congr
            (fun k => ll_target_getD
              (ImportedListLast.List_cons_inst1 Lean.Nat
                (sub_nat_to_imported x) (ll_to_imported xs)) k)
            _ _
            ImportedListLast.Prosa_Validation_ListLastInterface_nat_zero)) _).
      exact (ImportedListLast.Prosa_Validation_ListLastInterface_getD_zero
        (sub_nat_to_imported x) (ll_to_imported xs)).
    + refine (sub_imported_eq_trans _ _ _
        (ImportedListLast.Prosa_Validation_ListLastInterface_getD_succ_direct
          (sub_nat_to_imported x) (ll_to_imported xs)
          (sub_nat_to_imported n)) _).
      exact (IH n).
Qed.

Lemma ll_getD_related xsR xsL nR nL :
  LlListRel xsR xsL -> SubNatRel nR nL ->
  SubNatRel (nth O xsR nR) (ll_target_getD xsL nL).
Proof.
  intros Hxs Hn. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (ll_getD_canonical xsR nR))
    (sub_imported_eq_congr2 ll_target_getD _ _ _ _ Hxs Hn)).
Qed.

(** The actual imported [max0] is a left fold of the actual imported
    [Nat.max].  The following lemmas relate that computation to MathComp's
    [foldl maxn 0]; no theorem about either [max0] is assumed. *)
Definition ll_target_max (a b : Lean.Nat) : Lean.Nat :=
  ImportedListLast.Nat_max a b.

Definition ll_target_max0
    (xs : ImportedListLast.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedListLast.Prosa_Util_List_max0 xs.

Lemma ll_target_max_canonical (a b : nat) :
  Lean.eq
    (ll_target_max (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (maxn a b)).
Proof.
  unfold ll_target_max, ImportedListLast.Nat_max,
    ImportedListLast.Max_max_inst1, ImportedListLast.Nat_instMax,
    ImportedListLast.maxOfLe_inst1.
  cbn.
  destruct (ImportedListLast.Nat_decLe
    (sub_nat_to_imported a) (sub_nat_to_imported b)) as [Hnle|Hle].
  - have Hrel := sub_nat_le_correspondence a (sub_nat_to_imported a)
      b (sub_nat_to_imported b) (sub_nat_rel_canonical a)
      (sub_nat_rel_canonical b).
    have Hnot : ~ is_true (leq a b).
    { intro Hab.
      exact (interpret_strict Logic.False
        (ll_false_to_strict
          (Hnle (prop_to_sprop _ _ Hrel Hab)))). }
    have Hba : is_true (leq b a).
    { move: (leq_total a b) => /orP [Hab|Hba]; last exact Hba.
      exfalso. exact (Hnot Hab). }
    have Hmax : maxn a b = a := (elimT maxn_idPl Hba).
    rewrite Hmax. exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported a)).
  - have Hab : is_true (leq a b).
    { have Hrel := sub_nat_le_correspondence a (sub_nat_to_imported a)
        b (sub_nat_to_imported b) (sub_nat_rel_canonical a)
        (sub_nat_rel_canonical b).
      exact (sprop_to_prop _ _ Hrel Hle). }
    have Hmax : maxn a b = b := (elimT maxn_idPr Hab).
    rewrite Hmax. exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported b)).
Qed.

Lemma ll_foldl_max_canonical (z : nat) (xs : seq nat) :
  Lean.eq
    (ImportedListLast.List_foldl_inst3 Lean.Nat Lean.Nat
      ImportedListLast.Nat_max (sub_nat_to_imported z)
      (ll_to_imported xs))
    (sub_nat_to_imported (foldl maxn z xs)).
Proof.
  revert z. induction xs as [|x xs IH]; intro z.
  - exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported z)).
  - cbn [ll_to_imported ImportedListLast.List_foldl_inst3 foldl].
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (fun init => ImportedListLast.List_foldl_inst3
          Lean.Nat Lean.Nat ImportedListLast.Nat_max init
          (ll_to_imported xs)) _ _
        (ll_target_max_canonical z x)) _).
    exact (IH (maxn z x)).
Qed.

Lemma ll_max0_canonical (xs : seq nat) :
  SubNatRel (GeneratedListLastSource.max0 xs)
    (ll_target_max0 (ll_to_imported xs)).
Proof.
  unfold GeneratedListLastSource.max0, ll_target_max0,
    ImportedListLast.Prosa_Util_List_max0, SubNatRel.
  exact (sub_imported_eq_sym _ _ (ll_foldl_max_canonical 0 xs)).
Qed.

Lemma ll_max0_related xsR xsL : LlListRel xsR xsL ->
  SubNatRel (GeneratedListLastSource.max0 xsR) (ll_target_max0 xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _
    (ll_max0_canonical xsR)
    (sub_imported_eq_congr ll_target_max0 _ _ Hxs)).
Qed.

Lemma ll_max_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (maxn aR bR) (ll_target_max aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (ll_target_max_canonical aR bR))
    (sub_imported_eq_congr2 ll_target_max _ _ _ _ Ha Hb)).
Qed.

Definition ll_target_le (a b : Lean.Nat) : SProp :=
  ImportedListLast.LE_le_inst1 Lean.Nat ImportedListLast.instLENat a b.

Lemma ll_nat_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (ll_target_le aL bL).
Proof.
  intros Ha Hb. exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

Definition ll_target_lt (a b : Lean.Nat) : SProp :=
  ImportedListLast.LT_lt_inst1 Lean.Nat ImportedListLast.instLTNat a b.

Lemma ll_nat_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (ll_target_lt aL bL).
Proof.
  intros Ha Hb. exact (sub_nat_lt_correspondence aR aL bR bL Ha Hb).
Qed.

(** MathComp exposes membership as a reflected Boolean, whereas the imported
    Lean list exposes the inductive [List.Mem] proposition.  This adapter is
    bidirectional and preserves the element and list representation maps. *)
Definition ll_target_mem (x : Lean.Nat)
    (xs : ImportedListLast.List_inst1 Lean.Nat) : SProp :=
  ImportedListLast.Membership_mem_inst3 Lean.Nat
    (ImportedListLast.List_inst1 Lean.Nat)
    (ImportedListLast.List_instMembership_inst1 Lean.Nat) xs x.

Definition ll_target_mem_transport (x x' : Lean.Nat)
    (xs xs' : ImportedListLast.List_inst1 Lean.Nat) :
  Lean.eq x x' -> Lean.eq xs xs' ->
  ImportedListLast.List_Mem_inst1 Lean.Nat x xs ->
  ImportedListLast.List_Mem_inst1 Lean.Nat x' xs' :=
  fun Hx Hxs Hmem =>
    match Hx in Lean.eq _ y return
      Lean.eq xs xs' -> ImportedListLast.List_Mem_inst1 Lean.Nat x xs ->
      ImportedListLast.List_Mem_inst1 Lean.Nat y xs'
    with
    | Lean.eq_refl => fun Hlists Hm =>
        match Hlists in Lean.eq _ ys return
          ImportedListLast.List_Mem_inst1 Lean.Nat x xs ->
          ImportedListLast.List_Mem_inst1 Lean.Nat x ys
        with
        | Lean.eq_refl => fun Hm' => Hm'
        end Hm
    end Hxs Hmem.

Definition ll_mem_head_of_rocq_eq (x y : nat)
    (xs : ImportedListLast.List_inst1 Lean.Nat) :
  Logic.eq x y ->
  ImportedListLast.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
    (ImportedListLast.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported y) xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedListLast.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
        (ImportedListLast.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported z) xs)
    with
    | Logic.eq_refl => ImportedListLast.List_Mem_head_inst1 Lean.Nat
        (sub_nat_to_imported x) xs
    end.

Fixpoint ll_seq_mem_forward (x : nat) (xs : seq nat) :
  SubNatTruth (x \in xs) ->
  ImportedListLast.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
    (ll_to_imported xs) :=
  match xs as xs0 return SubNatTruth (x \in xs0) ->
      ImportedListLast.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
        (ll_to_imported xs0)
  with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqnP x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedListLast.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
          (ImportedListLast.List_cons_inst1 Lean.Nat
            (sub_nat_to_imported y) (ll_to_imported ys))
      with
      | ReflectT Hxy => fun _ => ll_mem_head_of_rocq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedListLast.List_Mem_tail_inst1 Lean.Nat
          (sub_nat_to_imported x) (sub_nat_to_imported y) _
          (ll_seq_mem_forward x ys H)
      end
  end.

Definition ll_mem_tail_truth (a b : bool) :
  SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, true => fun _ => sub_nat_truth_intro
  | true, false => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Definition ll_mem_head_truth (a b : bool) :
  SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, true => fun _ => sub_nat_truth_intro
  | true, false => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Definition ll_eq_refl_truth (x : nat) : SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Fixpoint ll_imported_mem_decoded (x : Lean.Nat)
    (xs : ImportedListLast.List_inst1 Lean.Nat)
    (H : ImportedListLast.List_Mem_inst1 Lean.Nat x xs) :
    SubNatTruth (sub_nat_to_rocq x \in ll_to_rocq xs) :=
  match H with
  | ImportedListLast.List_Mem_head_inst1 ys =>
      ll_mem_head_truth _ _ (ll_eq_refl_truth (sub_nat_to_rocq x))
  | ImportedListLast.List_Mem_tail_inst1 y ys Htail =>
      ll_mem_tail_truth _ _ (ll_imported_mem_decoded x ys Htail)
  end.

Definition ll_mem_truth_transport (x x' : nat) (xs xs' : seq nat) :
  Logic.eq x x' -> Logic.eq xs xs' ->
  SubNatTruth (x \in xs) -> SubNatTruth (x' \in xs') :=
  fun Hx Hxs Htruth =>
    match Hx in Logic.eq _ y return Logic.eq xs xs' ->
      SubNatTruth (x \in xs) -> SubNatTruth (y \in xs')
    with
    | Logic.eq_refl => fun Hlists Ht =>
        match Hlists in Logic.eq _ ys return
          SubNatTruth (x \in xs) -> SubNatTruth (x \in ys)
        with
        | Logic.eq_refl => fun Ht' => Ht'
        end Ht
    end Hxs Htruth.

Definition ll_imported_mem_backward (x : nat) (xs : seq nat)
    (H : ImportedListLast.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
      (ll_to_imported xs)) : SubNatTruth (x \in xs) :=
  ll_mem_truth_transport _ _ _ _ (sub_nat_rocq_roundtrip x)
    (ll_source_roundtrip xs)
    (ll_imported_mem_decoded (sub_nat_to_imported x)
      (ll_to_imported xs) H).

Lemma ll_membership_correspondence xR xL xsR xsL :
  SubNatRel xR xL -> LlListRel xsR xsL ->
  PropSPropRel (xR \in xsR) (ll_target_mem xL xsL).
Proof.
  intros Hx Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold ll_target_mem.
    apply (ll_target_mem_transport _ _ _ _ Hx Hxs).
    apply ll_seq_mem_forward. exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply ll_imported_mem_backward.
    unfold ll_target_mem in Hmem.
    exact (ll_target_mem_transport _ _ _ _
      (sub_imported_eq_sym _ _ Hx) (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Definition ll_target_positive (n : Lean.Nat) : ImportedListLast.Bool :=
  ImportedListLast.Decidable_decide
    (ll_target_lt ll_target_zero n)
    (ImportedListLast.Nat_decLt ll_target_zero n).

Lemma ll_positive_canonical (n : nat) :
  LlBoolRel (ltn O n) (ll_target_positive (sub_nat_to_imported n)).
Proof. destruct n; exact (@Lean.eq_refl _ _). Qed.

Lemma ll_positive_pred_rel :
  LlPredRel (fun n => ltn O n) ll_target_positive.
Proof.
  intros nR nL Hn. unfold LlBoolRel.
  exact (sub_imported_eq_trans _ _ _ (ll_positive_canonical nR)
    (sub_imported_eq_congr ll_target_positive _ _ Hn)).
Qed.

Definition ll_target_last0_cons_statement : SProp :=
  forall (x : Lean.Nat) (xs : ImportedListLast.List_inst1 Lean.Nat),
    ll_target_nonempty xs ->
    Lean.eq
      (ll_target_last
        (ImportedListLast.List_cons_inst1 Lean.Nat x xs))
      (ll_target_last xs).

Theorem last0_cons_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_last0_cons
    ll_target_last0_cons_statement.
Proof.
  unfold GeneratedListLastSource.statement_last0_cons,
    ll_target_last0_cons_statement.
  apply ll_forall_nat_correspondence. intros xR xL Hx.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply ll_imp_correspondence.
  - exact (ll_nonempty_related xsR xsL Hxs).
  - apply sub_nat_eq_correspondence.
    + exact (ll_last_related _ _ (ll_cons_related _ _ _ _ Hx Hxs)).
    + exact (ll_last_related _ _ Hxs).
Qed.

Definition ll_target_last0_cat_statement : SProp :=
  forall (xs_l xs_r : ImportedListLast.List_inst1 Lean.Nat),
    ll_target_nonempty xs_r ->
    Lean.eq (ll_target_last (ll_target_append xs_l xs_r))
      (ll_target_last xs_r).

Theorem last0_cat_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_last0_cat
    ll_target_last0_cat_statement.
Proof.
  unfold GeneratedListLastSource.statement_last0_cat,
    ll_target_last0_cat_statement.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply ll_forall_list_correspondence. intros ysR ysL Hys.
  apply ll_imp_correspondence.
  - exact (ll_nonempty_related ysR ysL Hys).
  - apply sub_nat_eq_correspondence.
    + exact (ll_last_related _ _
        (ll_append_related _ _ _ _ Hxs Hys)).
    + exact (ll_last_related _ _ Hys).
Qed.

Definition ll_target_last0_nth_statement : SProp :=
  forall xs : ImportedListLast.List_inst1 Lean.Nat,
    Lean.eq (ll_target_last xs)
      (ll_target_getD xs
        (ll_target_sub (ll_target_length xs) ll_target_one)).

Theorem last0_nth_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_last0_nth
    ll_target_last0_nth_statement.
Proof.
  unfold GeneratedListLastSource.statement_last0_nth,
    ll_target_last0_nth_statement.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply sub_nat_eq_correspondence.
  - exact (ll_last_related _ _ Hxs).
  - apply ll_getD_related.
    + exact Hxs.
    + exact (ll_sub_one_related _ _ (ll_length_related _ _ Hxs)).
Qed.

Definition ll_target_last0_ex_cat_statement : SProp :=
  forall (x : Lean.Nat) (xs : ImportedListLast.List_inst1 Lean.Nat),
    ll_target_nonempty xs -> Lean.eq (ll_target_last xs) x ->
    ImportedListLast.Exists (ImportedListLast.List_inst1 Lean.Nat)
      (fun xsh => Lean.eq
        (ll_target_append xsh
          (ImportedListLast.List_cons_inst1 Lean.Nat x
            (ImportedListLast.List_nil_inst1 Lean.Nat))) xs).

Theorem last0_ex_cat_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_last0_ex_cat
    ll_target_last0_ex_cat_statement.
Proof.
  unfold GeneratedListLastSource.statement_last0_ex_cat,
    ll_target_last0_ex_cat_statement.
  apply ll_forall_nat_correspondence. intros xR xL Hx.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply ll_imp_correspondence.
  - exact (ll_nonempty_related xsR xsL Hxs).
  - apply ll_imp_correspondence.
    + apply sub_nat_eq_correspondence.
      * exact (ll_last_related _ _ Hxs).
      * exact Hx.
    + apply ll_exists_list_correspondence. intros xshR xshL Hxsh.
      apply ll_list_eq_correspondence.
      * apply ll_append_related.
        -- exact Hxsh.
        -- exact (ll_cons_related _ _ _ _ Hx ll_nil_related).
      * exact Hxs.
Qed.

Definition ll_target_last0_filter_statement : SProp :=
  forall (x : Lean.Nat) (xs : ImportedListLast.List_inst1 Lean.Nat)
    (P : Lean.Nat -> ImportedListLast.Bool),
    ll_target_nonempty xs -> Lean.eq (ll_target_last xs) x ->
    Lean.eq (P x) ImportedListLast.Bool_true ->
    Lean.eq (ll_target_last (ll_target_filter P xs)) x.

Theorem last0_filter_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_last0_filter
    ll_target_last0_filter_statement.
Proof.
  unfold GeneratedListLastSource.statement_last0_filter,
    ll_target_last0_filter_statement.
  apply ll_forall_nat_correspondence. intros xR xL Hx.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply ll_forall_pred_correspondence. intros PR PL HP.
  apply ll_imp_correspondence.
  - exact (ll_nonempty_related xsR xsL Hxs).
  - apply ll_imp_correspondence.
    + apply sub_nat_eq_correspondence.
      * exact (ll_last_related _ _ Hxs).
      * exact Hx.
    + apply ll_imp_correspondence.
      * exact (ll_bool_true_correspondence (PR xR) (PL xL)
          (HP xR xL Hx)).
      * apply sub_nat_eq_correspondence.
        -- exact (ll_last_related _ _
             (ll_filter_related PR PL xsR xsL HP Hxs)).
        -- exact Hx.
Qed.

Definition ll_target_max0_cons_statement : SProp :=
  forall (x : Lean.Nat) (xs : ImportedListLast.List_inst1 Lean.Nat),
    Lean.eq
      (ll_target_max0
        (ImportedListLast.List_cons_inst1 Lean.Nat x xs))
      (ll_target_max x (ll_target_max0 xs)).

Theorem max0_cons_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_max0_cons
    ll_target_max0_cons_statement.
Proof.
  unfold GeneratedListLastSource.statement_max0_cons,
    ll_target_max0_cons_statement.
  apply ll_forall_nat_correspondence. intros xR xL Hx.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply sub_nat_eq_correspondence.
  - exact (ll_max0_related _ _ (ll_cons_related _ _ _ _ Hx Hxs)).
  - apply ll_max_related.
    + exact Hx.
    + exact (ll_max0_related _ _ Hxs).
Qed.

Definition ll_target_max0_2cons_eq_statement : SProp :=
  forall (x : Lean.Nat) (xs : ImportedListLast.List_inst1 Lean.Nat),
    Lean.eq
      (ll_target_max0
        (ImportedListLast.List_cons_inst1 Lean.Nat x
          (ImportedListLast.List_cons_inst1 Lean.Nat x xs)))
      (ll_target_max0
        (ImportedListLast.List_cons_inst1 Lean.Nat x xs)).

Theorem max0_2cons_eq_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_max0_2cons_eq
    ll_target_max0_2cons_eq_statement.
Proof.
  unfold GeneratedListLastSource.statement_max0_2cons_eq,
    ll_target_max0_2cons_eq_statement.
  apply ll_forall_nat_correspondence. intros xR xL Hx.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply sub_nat_eq_correspondence.
  - exact (ll_max0_related _ _
      (ll_cons_related _ _ _ _ Hx
        (ll_cons_related _ _ _ _ Hx Hxs))).
  - exact (ll_max0_related _ _ (ll_cons_related _ _ _ _ Hx Hxs)).
Qed.

Definition ll_target_max0_2cons_le_statement : SProp :=
  forall (x1 x2 : Lean.Nat)
    (xs : ImportedListLast.List_inst1 Lean.Nat),
    ll_target_le x1 x2 ->
    Lean.eq
      (ll_target_max0
        (ImportedListLast.List_cons_inst1 Lean.Nat x1
          (ImportedListLast.List_cons_inst1 Lean.Nat x2 xs)))
      (ll_target_max0
        (ImportedListLast.List_cons_inst1 Lean.Nat x2 xs)).

Theorem max0_2cons_le_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_max0_2cons_le
    ll_target_max0_2cons_le_statement.
Proof.
  unfold GeneratedListLastSource.statement_max0_2cons_le,
    ll_target_max0_2cons_le_statement.
  apply ll_forall_nat_correspondence. intros x1R x1L Hx1.
  apply ll_forall_nat_correspondence. intros x2R x2L Hx2.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply ll_imp_correspondence.
  - exact (ll_nat_le_correspondence _ _ _ _ Hx1 Hx2).
  - apply sub_nat_eq_correspondence.
    + exact (ll_max0_related _ _
        (ll_cons_related _ _ _ _ Hx1
          (ll_cons_related _ _ _ _ Hx2 Hxs))).
    + exact (ll_max0_related _ _ (ll_cons_related _ _ _ _ Hx2 Hxs)).
Qed.

Definition ll_target_last_le_max_statement : SProp :=
  forall xs : ImportedListLast.List_inst1 Lean.Nat,
    ll_target_le (ll_target_last xs) (ll_target_max0 xs).

Theorem last_of_seq_le_max_of_seq_statement_certificate :
  PropSPropRel
    GeneratedListLastSource.statement_last_of_seq_le_max_of_seq
    ll_target_last_le_max_statement.
Proof.
  unfold GeneratedListLastSource.statement_last_of_seq_le_max_of_seq,
    ll_target_last_le_max_statement.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply ll_nat_le_correspondence.
  - exact (ll_last_related _ _ Hxs).
  - exact (ll_max0_related _ _ Hxs).
Qed.

Definition ll_target_max0_of_uniform_set_statement : SProp :=
  forall (k : Lean.Nat) (xs : ImportedListLast.List_inst1 Lean.Nat),
    ll_target_lt ll_target_zero (ll_target_length xs) ->
    (forall x : Lean.Nat, ll_target_mem x xs -> Lean.eq x k) ->
    Lean.eq (ll_target_max0 xs) k.

Theorem max0_of_uniform_set_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_max0_of_uniform_set
    ll_target_max0_of_uniform_set_statement.
Proof.
  unfold GeneratedListLastSource.statement_max0_of_uniform_set,
    ll_target_max0_of_uniform_set_statement.
  apply ll_forall_nat_correspondence. intros kR kL Hk.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply ll_imp_correspondence.
  - apply ll_nat_lt_correspondence.
    + exact (sub_nat_rel_canonical O).
    + exact (ll_length_related _ _ Hxs).
  - apply ll_imp_correspondence.
    + apply ll_forall_nat_correspondence. intros xR xL Hx.
      apply ll_imp_correspondence.
      * exact (ll_membership_correspondence _ _ _ _ Hx Hxs).
      * exact (sub_nat_eq_correspondence _ _ _ _ Hx Hk).
    + apply sub_nat_eq_correspondence.
      * exact (ll_max0_related _ _ Hxs).
      * exact Hk.
Qed.

Definition ll_target_in_max0_le_statement : SProp :=
  forall (xs : ImportedListLast.List_inst1 Lean.Nat) (x : Lean.Nat),
    ll_target_mem x xs -> ll_target_le x (ll_target_max0 xs).

Theorem in_max0_le_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_in_max0_le
    ll_target_in_max0_le_statement.
Proof.
  unfold GeneratedListLastSource.statement_in_max0_le,
    ll_target_in_max0_le_statement.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply ll_forall_nat_correspondence. intros xR xL Hx.
  apply ll_imp_correspondence.
  - exact (ll_membership_correspondence _ _ _ _ Hx Hxs).
  - apply ll_nat_le_correspondence.
    + exact Hx.
    + exact (ll_max0_related _ _ Hxs).
Qed.

Definition ll_target_max0_in_seq_statement : SProp :=
  forall xs : ImportedListLast.List_inst1 Lean.Nat,
    ll_target_nonempty xs -> ll_target_mem (ll_target_max0 xs) xs.

Theorem max0_in_seq_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_max0_in_seq
    ll_target_max0_in_seq_statement.
Proof.
  unfold GeneratedListLastSource.statement_max0_in_seq,
    ll_target_max0_in_seq_statement.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply ll_imp_correspondence.
  - exact (ll_nonempty_related _ _ Hxs).
  - apply ll_membership_correspondence.
    + exact (ll_max0_related _ _ Hxs).
    + exact Hxs.
Qed.

Definition ll_target_max0_rem0_statement : SProp :=
  forall xs : ImportedListLast.List_inst1 Lean.Nat,
    Lean.eq (ll_target_max0 (ll_target_filter ll_target_positive xs))
      (ll_target_max0 xs).

Theorem max0_rem0_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_max0_rem0
    ll_target_max0_rem0_statement.
Proof.
  unfold GeneratedListLastSource.statement_max0_rem0,
    ll_target_max0_rem0_statement.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply sub_nat_eq_correspondence.
  - apply ll_max0_related.
    exact (ll_filter_related _ _ _ _ ll_positive_pred_rel Hxs).
  - exact (ll_max0_related _ _ Hxs).
Qed.

Definition ll_target_max_of_dominating_seq_statement : SProp :=
  forall (xs ys : ImportedListLast.List_inst1 Lean.Nat),
    (forall n : Lean.Nat,
      ll_target_le (ll_target_getD xs n) (ll_target_getD ys n)) ->
    ll_target_le (ll_target_max0 xs) (ll_target_max0 ys).

Theorem max_of_dominating_seq_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_max_of_dominating_seq
    ll_target_max_of_dominating_seq_statement.
Proof.
  unfold GeneratedListLastSource.statement_max_of_dominating_seq,
    ll_target_max_of_dominating_seq_statement.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply ll_forall_list_correspondence. intros ysR ysL Hys.
  apply ll_imp_correspondence.
  - apply ll_forall_nat_correspondence. intros nR nL Hn.
    apply ll_nat_le_correspondence.
    + exact (ll_getD_related _ _ _ _ Hxs Hn).
    + exact (ll_getD_related _ _ _ _ Hys Hn).
  - apply ll_nat_le_correspondence.
    + exact (ll_max0_related _ _ Hxs).
    + exact (ll_max0_related _ _ Hys).
Qed.

Definition ll_target_nth0_cons_statement : SProp :=
  forall (x : Lean.Nat) (xs : ImportedListLast.List_inst1 Lean.Nat)
    (n : Lean.Nat),
    ll_target_lt ll_target_zero n ->
    Lean.eq
      (ll_target_getD
        (ImportedListLast.List_cons_inst1 Lean.Nat x xs) n)
      (ll_target_getD xs (ll_target_sub n ll_target_one)).

Theorem nth0_cons_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_nth0_cons
    ll_target_nth0_cons_statement.
Proof.
  unfold GeneratedListLastSource.statement_nth0_cons,
    ll_target_nth0_cons_statement.
  apply ll_forall_nat_correspondence. intros xR xL Hx.
  apply ll_forall_list_correspondence. intros xsR xsL Hxs.
  apply ll_forall_nat_correspondence. intros nR nL Hn.
  apply ll_imp_correspondence.
  - apply ll_nat_lt_correspondence.
    + exact (sub_nat_rel_canonical O).
    + exact Hn.
  - apply sub_nat_eq_correspondence.
    + apply ll_getD_related.
      * exact (ll_cons_related _ _ _ _ Hx Hxs).
      * exact Hn.
    + apply ll_getD_related.
      * exact Hxs.
      * exact (ll_sub_one_related _ _ Hn).
Qed.

Print Assumptions ll_source_roundtrip.
Print Assumptions ll_target_roundtrip.
Print Assumptions ll_nonempty_correspondence.
Print Assumptions ll_last_canonical.
Print Assumptions ll_append_canonical.
Print Assumptions ll_filter_canonical.
Print Assumptions last0_cons_statement_certificate.
Print Assumptions last0_cat_statement_certificate.
Print Assumptions last0_nth_statement_certificate.
Print Assumptions last0_ex_cat_statement_certificate.
Print Assumptions last0_filter_statement_certificate.
Print Assumptions ll_target_max_canonical.
Print Assumptions ll_max0_canonical.
Print Assumptions max0_cons_statement_certificate.
Print Assumptions max0_2cons_eq_statement_certificate.
Print Assumptions max0_2cons_le_statement_certificate.
Print Assumptions last_of_seq_le_max_of_seq_statement_certificate.
Print Assumptions ll_membership_correspondence.
Print Assumptions ll_positive_pred_rel.
Print Assumptions max0_of_uniform_set_statement_certificate.
Print Assumptions in_max0_le_statement_certificate.
Print Assumptions max0_in_seq_statement_certificate.
Print Assumptions max0_rem0_statement_certificate.
Print Assumptions max_of_dominating_seq_statement_certificate.
Print Assumptions nth0_cons_statement_certificate.
