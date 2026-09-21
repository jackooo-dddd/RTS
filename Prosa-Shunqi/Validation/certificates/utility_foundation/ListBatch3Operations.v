From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedListLast.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ListLastCertificate ListRemCertificate ListBatch2Certificate.
From prosa Require Import GeneratedListLastSource.

(** Small logical combinators used to compose already-certified operation
    correspondences. *)
Lemma l3_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p | q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intros [p | q]; apply strictly_inhabits.
    + left. exact (sprop_to_prop _ _ HP p).
    + right. exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma l3_identity_eq_correspondence {T : Type} (x y : T) :
  PropSPropRel (Logic.eq x y) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - exact (coq_eq_to_imported_eq x y).
  - intro H. apply strictly_inhabits. exact (imported_eq_to_coq_eq x y H).
Qed.

Lemma l3_forall_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (HP x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _ (HP x) (HL x)).
Qed.

Lemma l3_forall_generic_list_correspondence (T : Type)
    (PR : seq T -> Prop) (PL : ImportedListLast.List T -> SProp) :
  (forall xsR xsL, LrListRel xsR xsL ->
    PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (forall xsR, PR xsR) (forall xsL, PL xsL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR xsL. exact (prop_to_sprop _ _
      (HP (lr_to_rocq xsL) xsL (lr_target_roundtrip xsL))
      (HR (lr_to_rocq xsL))).
  - intro HL. apply strictly_inhabits. intro xsR.
    exact (sprop_to_prop _ _
      (HP xsR (lr_to_imported xsR) (@Lean.eq_refl _ _))
      (HL (lr_to_imported xsR))).
Qed.

Lemma l3_exists_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (exists nR, PR nR) (ImportedListLast.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [nR Hn]. exact (ImportedListLast.Exists_intro Lean.Nat PL
      (sub_nat_to_imported nR)
      (prop_to_sprop _ _
        (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) Hn)).
  - intros [nL Hn]. apply strictly_inhabits.
    exists (sub_nat_to_rocq nL).
    exact (sprop_to_prop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL)) Hn).
Qed.

(** The imported [Nodup] representation is [Pairwise Ne].  These proofs are
    the namespace-local instantiation of the already established
    [uniq]/[Nodup] proof pattern; it cannot reuse [ImportedSeqset.List]
    directly because each lean4export artifact has a distinct imported List
    inductive. *)
Definition l3_nodup_transport {T : Type}
    (xs ys : ImportedListLast.List T) :
    Lean.eq xs ys -> ImportedListLast.List_Nodup T xs ->
    ImportedListLast.List_Nodup T ys :=
  fun Hxy H =>
    match Hxy in Lean.eq _ zs return ImportedListLast.List_Nodup T zs with
    | Lean.eq_refl => H
    end.

Inductive L3True : SProp := l3_I.
Inductive L3False : SProp := .

Definition L3BoolTruth (b : bool) : SProp :=
  match b with true => L3True | false => L3False end.

Definition l3_bool_prop_to_truth (b : bool) : is_true b -> L3BoolTruth b :=
  match b return is_true b -> L3BoolTruth b with
  | true => fun _ => l3_I
  | false => fun H =>
      match H in Logic.eq _ z return
        match z with true => L3False | false => L3True end
      with Logic.eq_refl => l3_I end
  end.

Definition l3_and_left (a b : bool) :
    L3BoolTruth (a && b) -> L3BoolTruth a :=
  match a, b return L3BoolTruth (a && b) -> L3BoolTruth a with
  | true, _ => fun _ => l3_I
  | false, _ => fun H => H
  end.

Definition l3_and_right (a b : bool) :
    L3BoolTruth (a && b) -> L3BoolTruth b :=
  match a, b return L3BoolTruth (a && b) -> L3BoolTruth b with
  | true, true => fun _ => l3_I
  | true, false => fun H => H
  | false, true => fun _ => l3_I
  | false, false => fun H => H
  end.

Definition l3_neg_mem_contra (b : bool) :
    L3BoolTruth (~~ b) -> L3BoolTruth b -> ImportedListLast.False :=
  match b return
      L3BoolTruth (~~ b) -> L3BoolTruth b -> ImportedListLast.False with
  | true => fun H _ => match H with end
  | false => fun _ H => match H with end
  end.

Fixpoint l3_uniq_truth_forward (T : eqType) (xs : seq T) :
    L3BoolTruth (uniq xs) ->
    ImportedListLast.List_Nodup T (lr_to_imported xs).
Proof.
  destruct xs as [|x xs].
  - intro Hnil. exact (ImportedListLast.List_Pairwise_nil T
      (ImportedListLast.Ne T)).
  - intro Huniq.
    apply ImportedListLast.List_Pairwise_cons.
    + intros y Hy Hxy.
      have HyR := sprop_to_prop _ _
        (lr_membership_correspondence T y xs (lr_to_imported xs)
          (@Lean.eq_refl _ _)) Hy.
      have Hcoq : Logic.eq x y := imported_eq_to_coq_eq x y Hxy.
      subst y.
      exact (l3_neg_mem_contra (x \in xs)
        (l3_and_left _ _ Huniq)
        (l3_bool_prop_to_truth _ HyR)).
    + exact (l3_uniq_truth_forward T xs (l3_and_right _ _ Huniq)).
Defined.

Definition l3_uniq_forward (T : eqType) (xs : seq T) :
    uniq xs -> ImportedListLast.List_Nodup T (lr_to_imported xs) :=
  fun H => l3_uniq_truth_forward T xs (l3_bool_prop_to_truth _ H).

Definition l3_strict_uniq_transport (T : eqType) (xs ys : seq T) :
    Logic.eq xs ys -> StrictlyInhabited (uniq xs) ->
    StrictlyInhabited (uniq ys) :=
  fun H Huniq =>
    match H in Logic.eq _ zs return StrictlyInhabited (uniq zs) with
    | Logic.eq_refl => Huniq
    end.

Lemma l3_imported_nodup_backward (T : eqType)
    (xs : ImportedListLast.List T) :
  ImportedListLast.List_Nodup T xs ->
  StrictlyInhabited (uniq (lr_to_rocq xs)).
Proof.
  intro Hnodup. induction Hnodup as [|y ys Hhead Htail IH].
  - exact (strictly_inhabits (Logic.eq_refl true)).
  - destruct IH as [IHuniq].
    apply strictly_inhabits. apply/andP. split; last exact IHuniq.
    apply/negP. intro Hmem.
    have HmemL := prop_to_sprop _ _
      (lr_membership_correspondence T y (lr_to_rocq ys) ys
        (lr_target_roundtrip ys)) Hmem.
    have Hneq := Hhead y HmemL.
    exact (interpret_strict Logic.False
      (ll_false_to_strict (Hneq (@Lean.eq_refl T y)))).
Qed.

Lemma l3_uniq_backward (T : eqType) (xs : seq T) :
  ImportedListLast.List_Nodup T (lr_to_imported xs) ->
  StrictlyInhabited (uniq xs).
Proof.
  intro Hnodup.
  exact (l3_strict_uniq_transport T _ _ (lr_source_roundtrip xs)
    (l3_imported_nodup_backward T (lr_to_imported xs) Hnodup)).
Qed.

Lemma l3_uniq_correspondence (T : eqType)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  LrListRel xsR xsL ->
  PropSPropRel (uniq xsR) (ImportedListLast.List_Nodup T xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Huniq. exact (l3_nodup_transport _ _ Hxs
      (l3_uniq_forward T xsR Huniq)).
  - intro Hnodup.
    have Hcanonical := l3_nodup_transport _ _
      (sub_imported_eq_sym _ _ Hxs) Hnodup.
    exact (l3_uniq_backward T xsR Hcanonical).
Qed.

(** Generic defaulted lookup. *)
Definition l3_target_getD {T : Type}
    (xs : ImportedListLast.List T) (n : Lean.Nat) (d : T) : T :=
  ImportedListLast.List_getD T xs n d.

Lemma l3_getD_canonical {T : Type} (d : T) (xs : seq T) (n : nat) :
  Lean.eq (nth d xs n)
    (l3_target_getD (lr_to_imported xs) (sub_nat_to_imported n) d).
Proof.
  revert n. induction xs as [|a xs IH]; intro n.
  - destruct n; exact (@Lean.eq_refl T d).
  - destruct n as [|n].
    + cbn. exact (sub_imported_eq_sym _ _
        (ImportedListLast.Prosa_Validation_ListLastInterface_generic_getD_zero
          T a d (lr_to_imported xs))).
    + cbn. exact (sub_imported_eq_trans _ _ _ (IH n)
        (sub_imported_eq_sym _ _
          (ImportedListLast.Prosa_Validation_ListLastInterface_generic_getD_succ
            T a d (lr_to_imported xs) (sub_nat_to_imported n)))).
Qed.

Lemma l3_getD_related {T : Type} (d : T)
    (xsR : seq T) (xsL : ImportedListLast.List T)
    (nR : nat) (nL : Lean.Nat) :
  LrListRel xsR xsL -> SubNatRel nR nL ->
  Lean.eq (nth d xsR nR) (l3_target_getD xsL nL d).
Proof.
  intros Hxs Hn.
  exact (sub_imported_eq_trans _ _ _ (l3_getD_canonical d xsR nR)
    (sub_imported_eq_congr2 (fun xs n => l3_target_getD xs n d)
      _ _ _ _ Hxs Hn)).
Qed.

(** Boolean folds [all]/[has] and emptiness. *)
Definition l3_target_all {T : Type} (xs : ImportedListLast.List T)
    (P : T -> ImportedListLast.Bool) : ImportedListLast.Bool :=
  ImportedListLast.List_all T xs P.

Definition l3_target_any {T : Type} (xs : ImportedListLast.List T)
    (P : T -> ImportedListLast.Bool) : ImportedListLast.Bool :=
  ImportedListLast.List_any T xs P.

Definition l3_target_isEmpty {T : Type}
    (xs : ImportedListLast.List T) : ImportedListLast.Bool :=
  ImportedListLast.List_isEmpty T xs.

Lemma l3_bool_and_related aR aL bR bL :
  LlBoolRel aR aL -> LlBoolRel bR bL ->
  LlBoolRel (aR && bR) (ImportedListLast.Bool_and aL bL).
Proof.
  intros Ha Hb. unfold LlBoolRel in *.
  destruct aR, bR; cbn in *;
    exact (sub_imported_eq_congr2 ImportedListLast.Bool_and _ _ _ _ Ha Hb).
Qed.

Lemma l3_bool_or_related aR aL bR bL :
  LlBoolRel aR aL -> LlBoolRel bR bL ->
  LlBoolRel (aR || bR) (ImportedListLast.Bool_or aL bL).
Proof.
  intros Ha Hb. unfold LlBoolRel in *.
  destruct aR, bR; cbn in *;
    exact (sub_imported_eq_congr2 ImportedListLast.Bool_or _ _ _ _ Ha Hb).
Qed.

Fixpoint l3_all_canonical (T : Type) (PR : T -> bool)
    (PL : T -> ImportedListLast.Bool) (xs : seq T) :
  LrPredRel PR PL ->
  LlBoolRel (all PR xs) (l3_target_all (lr_to_imported xs) PL).
Proof.
  intro HP. destruct xs as [|a xs].
  - exact (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_generic_all_nil
        T PL)).
  - exact (sub_imported_eq_trans _ _ _
      (l3_bool_and_related _ _ _ _ (HP a)
        (l3_all_canonical T PR PL xs HP))
      (sub_imported_eq_sym _ _
        (ImportedListLast.Prosa_Validation_ListLastInterface_generic_all_cons
          T PL a (lr_to_imported xs)))).
Defined.

Lemma l3_all_related (T : Type) (PR : T -> bool)
    (PL : T -> ImportedListLast.Bool) (xsR : seq T)
    (xsL : ImportedListLast.List T) :
  LrPredRel PR PL -> LrListRel xsR xsL ->
  LlBoolRel (all PR xsR) (l3_target_all xsL PL).
Proof.
  intros HP Hxs. unfold LrListRel in Hxs. unfold LlBoolRel.
  exact (sub_imported_eq_trans _ _ _ (l3_all_canonical T PR PL xsR HP)
    (sub_imported_eq_congr (fun zs => l3_target_all zs PL) _ _ Hxs)).
Qed.

Fixpoint l3_any_canonical (T : Type) (PR : T -> bool)
    (PL : T -> ImportedListLast.Bool) (xs : seq T) :
  LrPredRel PR PL ->
  LlBoolRel (has PR xs) (l3_target_any (lr_to_imported xs) PL).
Proof.
  intro HP. destruct xs as [|a xs].
  - exact (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_generic_any_nil
        T PL)).
  - exact (sub_imported_eq_trans _ _ _
      (l3_bool_or_related _ _ _ _ (HP a)
        (l3_any_canonical T PR PL xs HP))
      (sub_imported_eq_sym _ _
        (ImportedListLast.Prosa_Validation_ListLastInterface_generic_any_cons
          T PL a (lr_to_imported xs)))).
Defined.

Lemma l3_any_related (T : Type) (PR : T -> bool)
    (PL : T -> ImportedListLast.Bool) (xsR : seq T)
    (xsL : ImportedListLast.List T) :
  LrPredRel PR PL -> LrListRel xsR xsL ->
  LlBoolRel (has PR xsR) (l3_target_any xsL PL).
Proof.
  intros HP Hxs. unfold LrListRel in Hxs. unfold LlBoolRel.
  exact (sub_imported_eq_trans _ _ _ (l3_any_canonical T PR PL xsR HP)
    (sub_imported_eq_congr (fun zs => l3_target_any zs PL) _ _ Hxs)).
Qed.

Definition l3_isEmpty_canonical (T : Type) (xs : seq T) :
    LlBoolRel (nilp xs) (l3_target_isEmpty (lr_to_imported xs)) :=
  match xs with
  | [::] => sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_generic_isEmpty_nil T)
  | a :: tail => sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_generic_isEmpty_cons
        T a (lr_to_imported tail))
  end.

Lemma l3_isEmpty_related (T : Type) (xsR : seq T)
    (xsL : ImportedListLast.List T) : LrListRel xsR xsL ->
  LlBoolRel (nilp xsR) (l3_target_isEmpty xsL).
Proof.
  intro Hxs. unfold LrListRel in Hxs. unfold LlBoolRel.
  exact (sub_imported_eq_trans _ _ _ (l3_isEmpty_canonical T xsR)
    (sub_imported_eq_congr l3_target_isEmpty _ _ Hxs)).
Qed.

(** Generic last-with-default computation. *)
Definition l3_target_last {T : Type}
    (xs : ImportedListLast.List T) (d : T) : T :=
  ImportedListLast.List_getLastD T xs d.

Lemma l3_last_canonical {T : Type} (d : T) (xs : seq T) :
  Lean.eq (last d xs) (l3_target_last (lr_to_imported xs) d).
Proof.
  induction xs as [|a xs IH].
  - cbn. exact (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_generic_getLastD_nil
        T d)).
  - destruct xs as [|b xs].
    + cbn. exact (sub_imported_eq_sym _ _
        (ImportedListLast.Prosa_Validation_ListLastInterface_generic_getLastD_singleton
          T a d)).
    + cbn in IH |- *.
      exact (sub_imported_eq_trans _ _ _ IH
        (sub_imported_eq_sym _ _
          (ImportedListLast.Prosa_Validation_ListLastInterface_generic_getLastD_cons_cons
            T a b d (lr_to_imported xs)))).
Qed.

Lemma l3_last_related {T : Type} (d : T)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  LrListRel xsR xsL ->
  Lean.eq (last d xsR) (l3_target_last xsL d).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _
    (l3_last_canonical d xsR)
    (sub_imported_eq_congr (fun zs => l3_target_last zs d) _ _ Hxs)).
Qed.

(** Equality and membership when the element itself is related by imported
    equality.  This is used for defaulted lookup results. *)
Lemma l3_element_eq_correspondence {T : Type}
    (xR xL yR yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL ->
  PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Hx) Hy).
  - intro Hxy. apply strictly_inhabits.
    have Hcanonical : Lean.eq xR yR :=
      sub_imported_eq_trans _ _ _ Hx
        (sub_imported_eq_trans _ _ _ Hxy (sub_imported_eq_sym _ _ Hy)).
    exact (imported_eq_to_coq_eq _ _ Hcanonical).
Qed.

Definition l3_mem_element_transport {T : Type} (x y : T)
    (xs : ImportedListLast.List T) :
  Lean.eq x y -> ImportedListLast.List_Mem T x xs ->
  ImportedListLast.List_Mem T y xs :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ z return ImportedListLast.List_Mem T z xs with
    | Lean.eq_refl => Hmem
    end.

Lemma l3_membership_related (T : eqType) (xR xL : T)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  Lean.eq xR xL -> LrListRel xsR xsL ->
  PropSPropRel (xR \in xsR) (lr_target_mem xL xsL).
Proof.
  intros Hx Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold lr_target_mem.
    exact (l3_mem_element_transport xR xL xsL Hx
      (prop_to_sprop _ _
        (lr_membership_correspondence T xR xsR xsL Hxs) Hmem)).
  - intro Hmem. apply strictly_inhabits.
    exact (sprop_to_prop _ _
      (lr_membership_correspondence T xR xsR xsL Hxs)
      (l3_mem_element_transport xL xR xsL
        (sub_imported_eq_sym _ _ Hx) Hmem)).
Qed.

(** Generic non-emptiness, preserving the source Boolean disequality and the
    imported Lean propositional disequality. *)
Definition l3_target_nonempty {T : Type}
    (xs : ImportedListLast.List T) : SProp :=
  ImportedListLast.Ne (ImportedListLast.List T) xs
    (ImportedListLast.List_nil T).

Lemma l3_nonempty_correspondence (T : eqType)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  LrListRel xsR xsL ->
  PropSPropRel (xsR != [::]) (l3_target_nonempty xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intros Hne HeqL. apply ll_coq_false_to_target.
    move: Hne => /negP Hne. apply Hne. apply/eqP.
    have Hmaps : Lean.eq (lr_to_imported xsR)
        (ImportedListLast.List_nil T) :=
      sub_imported_eq_trans _ _ _ Hxs HeqL.
    have Hback := f_equal lr_to_rocq
      (imported_eq_to_coq_eq _ _ Hmaps).
    exact (Logic.eq_trans (Logic.eq_sym (lr_source_roundtrip xsR)) Hback).
  - intro Hne. apply strictly_inhabits. apply/negP => /eqP Hnil.
    have Htarget : Lean.eq xsL (ImportedListLast.List_nil T) :=
      sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hxs)
        (coq_eq_to_imported_eq _ _ (f_equal lr_to_imported Hnil)).
    exact (interpret_strict Logic.False
      (ll_false_to_strict (Hne Htarget))).
Qed.

(** Pointwise Nat-valued functions and imported Boolean order decisions. *)
Definition L3NatFunRel {T : Type} (fR : T -> nat)
    (fL : T -> Lean.Nat) : SProp :=
  forall x, SubNatRel (fR x) (fL x).

Definition l3_nat_fun_to_imported {T : Type} (fR : T -> nat) :
    T -> Lean.Nat := fun x => sub_nat_to_imported (fR x).

Definition l3_nat_fun_to_rocq {T : Type} (fL : T -> Lean.Nat) :
    T -> nat := fun x => sub_nat_to_rocq (fL x).

Lemma l3_nat_fun_canonical {T : Type} (fR : T -> nat) :
  L3NatFunRel fR (l3_nat_fun_to_imported fR).
Proof. intro x. exact (sub_nat_rel_canonical (fR x)). Qed.

Lemma l3_nat_fun_surjective {T : Type} (fL : T -> Lean.Nat) :
  L3NatFunRel (l3_nat_fun_to_rocq fL) fL.
Proof. intro x. exact (sub_nat_rel_surjective (fL x)). Qed.

Definition l3_target_decide_le (a b : Lean.Nat) : ImportedListLast.Bool :=
  ImportedListLast.Decidable_decide (ll_target_le a b)
    (ImportedListLast.Nat_decLe a b).

Definition l3_target_decide_lt (a b : Lean.Nat) : ImportedListLast.Bool :=
  ImportedListLast.Decidable_decide (ll_target_lt a b)
    (ImportedListLast.Nat_decLt a b).

Lemma l3_decide_le_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  LlBoolRel (leq aR bR) (l3_target_decide_le aL bL).
Proof.
  intros Ha Hb. apply lr_decide_bool_correspondence.
  exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma l3_decide_lt_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  LlBoolRel (ltn aR bR) (l3_target_decide_lt aL bL).
Proof.
  intros Ha Hb. apply lr_decide_bool_correspondence.
  exact (sub_nat_lt_correspondence aR aL bR bL Ha Hb).
Qed.

(** Adjacent-pair sortedness.  The relation is Boolean on both sides; only
    its truth observation enters the target [IsChain] proposition. *)
Definition L3BinaryPredRel {T : Type} (RR : T -> T -> bool)
    (RL : T -> T -> ImportedListLast.Bool) : SProp :=
  forall x y, LlBoolRel (RR x y) (RL x y).

Definition l3_binary_pred_to_imported {T : Type}
    (RR : T -> T -> bool) : T -> T -> ImportedListLast.Bool :=
  fun x y => ll_bool_to_imported (RR x y).

Definition l3_binary_pred_to_rocq {T : Type}
    (RL : T -> T -> ImportedListLast.Bool) : T -> T -> bool :=
  fun x y => ll_bool_to_rocq (RL x y).

Lemma l3_binary_pred_canonical {T : Type} (RR : T -> T -> bool) :
  L3BinaryPredRel RR (l3_binary_pred_to_imported RR).
Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

Lemma l3_binary_pred_surjective {T : Type}
    (RL : T -> T -> ImportedListLast.Bool) :
  L3BinaryPredRel (l3_binary_pred_to_rocq RL) RL.
Proof. intros x y. exact (ll_bool_imported_roundtrip (RL x y)). Qed.

Definition l3_target_sorted {T : Type}
    (RL : T -> T -> ImportedListLast.Bool)
    (xs : ImportedListLast.List T) : SProp :=
  ImportedListLast.Prosa_Util_List_boolSorted T RL xs.

Definition l3_sorted_transport {T : Type}
    (RL : T -> T -> ImportedListLast.Bool)
    (xs ys : ImportedListLast.List T) :
  Lean.eq xs ys -> l3_target_sorted RL xs -> l3_target_sorted RL ys :=
  fun Hxy H =>
    match Hxy in Lean.eq _ zs return l3_target_sorted RL zs with
    | Lean.eq_refl => H
    end.

Definition l3_bool_truth_to_target_true (b : bool)
    (bL : ImportedListLast.Bool) :
  LlBoolRel b bL -> L3BoolTruth b ->
  Lean.eq bL ImportedListLast.Bool_true :=
  match b return LlBoolRel b bL -> L3BoolTruth b ->
      Lean.eq bL ImportedListLast.Bool_true with
  | true => fun Hb _ => sub_imported_eq_sym _ _ Hb
  | false => fun _ H => match H with end
  end.

Fixpoint l3_path_truth_forward (T : Type) (RR : T -> T -> bool)
    (RL : T -> T -> ImportedListLast.Bool) (a : T)
    (xs : seq T) {struct xs} :
  L3BinaryPredRel RR RL -> L3BoolTruth (path RR a xs) ->
  l3_target_sorted RL
    (ImportedListLast.List_cons T a (lr_to_imported xs)).
Proof.
  intros HR Hsorted. destruct xs as [|b tail].
  - exact (ImportedListLast.Prosa_Validation_ListLastInterface_generic_boolSorted_singleton
      T RL a).
  - apply (ImportedListLast.Iff_mpr _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_generic_boolSorted_cons_cons
        T RL a b (lr_to_imported tail))).
    exact (Lean.And_intro _ _
      (l3_bool_truth_to_target_true (RR a b) (RL a b) (HR a b)
        (l3_and_left _ _ Hsorted))
      (l3_path_truth_forward T RR RL b tail HR
        (l3_and_right _ _ Hsorted))).
Defined.

Definition l3_sorted_truth_forward (T : Type) (RR : T -> T -> bool)
    (RL : T -> T -> ImportedListLast.Bool) (xs : seq T) :
  L3BinaryPredRel RR RL -> L3BoolTruth (sorted RR xs) ->
  l3_target_sorted RL (lr_to_imported xs) :=
  match xs as zs return L3BinaryPredRel RR RL ->
      L3BoolTruth (sorted RR zs) ->
      l3_target_sorted RL (lr_to_imported zs) with
  | [::] => fun _ _ =>
      ImportedListLast.Prosa_Validation_ListLastInterface_generic_boolSorted_nil
        T RL
  | a :: tail => l3_path_truth_forward T RR RL a tail
  end.

Fixpoint l3_path_backward_canonical (T : Type)
    (RR : T -> T -> bool) (RL : T -> T -> ImportedListLast.Bool)
    (a : T) (xs : seq T) {struct xs} :
  L3BinaryPredRel RR RL ->
  l3_target_sorted RL
    (ImportedListLast.List_cons T a (lr_to_imported xs)) ->
  StrictlyInhabited (path RR a xs).
Proof.
  intros HR Hsorted. destruct xs as [|b tail].
  - exact (strictly_inhabits (Logic.eq_refl true)).
  - destruct (ImportedListLast.Iff_mp _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_generic_boolSorted_cons_cons
        T RL a b (lr_to_imported tail)) Hsorted) as [Hab Htail].
    destruct (l3_path_backward_canonical T RR RL b tail HR Htail)
      as [HsortedR].
    apply strictly_inhabits. apply/andP. split.
    + exact (sprop_to_prop _ _
        (ll_bool_true_correspondence (RR a b) (RL a b) (HR a b)) Hab).
    + exact HsortedR.
Defined.

Definition l3_sorted_backward_canonical (T : Type)
    (RR : T -> T -> bool) (RL : T -> T -> ImportedListLast.Bool)
    (xs : seq T) :
  L3BinaryPredRel RR RL -> l3_target_sorted RL (lr_to_imported xs) ->
  StrictlyInhabited (sorted RR xs) :=
  match xs as zs return L3BinaryPredRel RR RL ->
      l3_target_sorted RL (lr_to_imported zs) ->
      StrictlyInhabited (sorted RR zs) with
  | [::] => fun _ _ => strictly_inhabits (Logic.eq_refl true)
  | a :: tail => l3_path_backward_canonical T RR RL a tail
  end.

Lemma l3_sorted_correspondence (T : Type)
    (RR : T -> T -> bool) (RL : T -> T -> ImportedListLast.Bool)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  L3BinaryPredRel RR RL -> LrListRel xsR xsL ->
  PropSPropRel (sorted RR xsR) (l3_target_sorted RL xsL).
Proof.
  intros HR Hxs. apply prop_sprop_rel_intro.
  - intro Hsorted. apply (l3_sorted_transport RL _ _ Hxs).
    exact (l3_sorted_truth_forward T RR RL xsR HR
      (l3_bool_prop_to_truth _ Hsorted)).
  - intro Hsorted.
    exact (l3_sorted_backward_canonical T RR RL xsR HR
      (l3_sorted_transport RL _ _ (sub_imported_eq_sym _ _ Hxs) Hsorted)).
Qed.

(** Product/list/zip correspondence.  Source pairs are mapped constructor by
    constructor to the actual imported Lean [Prod]. *)
Definition l3_pair_to_imported {T U : Type} (p : T * U) :
    ImportedListLast.Prod T U :=
  match p with (x, y) => ImportedListLast.Prod_mk T U x y end.

Definition l3_pair_to_rocq {T U : Type}
    (p : ImportedListLast.Prod T U) : T * U :=
  match p with ImportedListLast.Prod_mk x y => (x, y) end.

Lemma l3_pair_source_roundtrip {T U : Type} (p : T * U) :
  Logic.eq (l3_pair_to_rocq (l3_pair_to_imported p)) p.
Proof. destruct p. reflexivity. Qed.

Lemma l3_pair_target_roundtrip {T U : Type}
    (p : ImportedListLast.Prod T U) :
  Lean.eq (l3_pair_to_imported (l3_pair_to_rocq p)) p.
Proof. destruct p. exact (@Lean.eq_refl _ _). Qed.

Fixpoint l3_pair_list_to_imported {T U : Type} (xs : seq (T * U)) :
    ImportedListLast.List (ImportedListLast.Prod T U) :=
  match xs with
  | [::] => ImportedListLast.List_nil (ImportedListLast.Prod T U)
  | p :: tail => ImportedListLast.List_cons (ImportedListLast.Prod T U)
      (l3_pair_to_imported p) (l3_pair_list_to_imported tail)
  end.

Fixpoint l3_pair_list_to_rocq {T U : Type}
    (xs : ImportedListLast.List (ImportedListLast.Prod T U)) : seq (T * U) :=
  match xs with
  | ImportedListLast.List_nil => [::]
  | ImportedListLast.List_cons p tail =>
      l3_pair_to_rocq p :: l3_pair_list_to_rocq tail
  end.

Definition L3PairListRel {T U : Type} (xsR : seq (T * U))
    (xsL : ImportedListLast.List (ImportedListLast.Prod T U)) : SProp :=
  Lean.eq (l3_pair_list_to_imported xsR) xsL.

Lemma l3_pair_list_source_roundtrip {T U : Type} (xs : seq (T * U)) :
  Logic.eq (l3_pair_list_to_rocq (l3_pair_list_to_imported xs)) xs.
Proof.
  induction xs as [|p xs IH]; cbn; first reflexivity.
  f_equal.
  - exact (l3_pair_source_roundtrip p).
  - exact IH.
Qed.

Lemma l3_pair_list_target_roundtrip {T U : Type}
    (xs : ImportedListLast.List (ImportedListLast.Prod T U)) :
  Lean.eq (l3_pair_list_to_imported (l3_pair_list_to_rocq xs)) xs.
Proof.
  induction xs as [|p xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr2
      (ImportedListLast.List_cons (ImportedListLast.Prod T U)) _ _ _ _
      (l3_pair_target_roundtrip p) IH).
Qed.

Definition l3_pair_target_mem {T U : Type}
    (p : ImportedListLast.Prod T U)
    (xs : ImportedListLast.List (ImportedListLast.Prod T U)) : SProp :=
  ImportedListLast.List_Mem (ImportedListLast.Prod T U) p xs.

Definition l3_pair_mem_head_of_coq_eq {T U : Type}
    (p q : T * U)
    (xs : ImportedListLast.List (ImportedListLast.Prod T U)) :
  Logic.eq p q ->
  l3_pair_target_mem (l3_pair_to_imported p)
    (ImportedListLast.List_cons (ImportedListLast.Prod T U)
      (l3_pair_to_imported q) xs) :=
  fun H => match H in Logic.eq _ z return
      l3_pair_target_mem (l3_pair_to_imported p)
        (ImportedListLast.List_cons (ImportedListLast.Prod T U)
          (l3_pair_to_imported z) xs) with
    | Logic.eq_refl => ImportedListLast.List_Mem_head
        (ImportedListLast.Prod T U) (l3_pair_to_imported p) xs
    end.

Fixpoint l3_pair_seq_mem_forward (T U : eqType) (p : T * U)
    (xs : seq (T * U)) :
  SubNatTruth (p \in xs) ->
  l3_pair_target_mem (l3_pair_to_imported p)
    (l3_pair_list_to_imported xs) :=
  match xs as zs return SubNatTruth (p \in zs) ->
      l3_pair_target_mem (l3_pair_to_imported p)
        (l3_pair_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | q :: tail =>
      match @eqP _ p q as r in reflect _ b return
        SubNatTruth (b || (p \in tail)) ->
        l3_pair_target_mem (l3_pair_to_imported p)
          (ImportedListLast.List_cons (ImportedListLast.Prod T U)
            (l3_pair_to_imported q) (l3_pair_list_to_imported tail)) with
      | ReflectT Hpq => fun _ => l3_pair_mem_head_of_coq_eq p q _ Hpq
      | ReflectF _ => fun H => ImportedListLast.List_Mem_tail
          (ImportedListLast.Prod T U) (l3_pair_to_imported p)
          (l3_pair_to_imported q) _
          (l3_pair_seq_mem_forward T U p tail H)
      end
  end.

Definition l3_pair_eq_refl_truth (T U : eqType) (p : T * U) :
    SubNatTruth (p == p).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Fixpoint l3_pair_imported_mem_decoded (T U : eqType)
    (p : ImportedListLast.Prod T U)
    (xs : ImportedListLast.List (ImportedListLast.Prod T U))
    (H : ImportedListLast.List_Mem (ImportedListLast.Prod T U) p xs) :
  SubNatTruth (l3_pair_to_rocq p \in l3_pair_list_to_rocq xs) :=
  match H with
  | ImportedListLast.List_Mem_head tail =>
      ll_mem_head_truth _ _
        (l3_pair_eq_refl_truth T U (l3_pair_to_rocq p))
  | ImportedListLast.List_Mem_tail q tail Htail =>
      ll_mem_tail_truth _ _
        (l3_pair_imported_mem_decoded T U p tail Htail)
  end.

Lemma l3_pair_imported_mem_backward (T U : eqType) (p : T * U)
    (xs : seq (T * U)) :
  l3_pair_target_mem (l3_pair_to_imported p)
      (l3_pair_list_to_imported xs) ->
  SubNatTruth (p \in xs).
Proof.
  intro H.
  have Hdecoded := l3_pair_imported_mem_decoded T U
    (l3_pair_to_imported p) (l3_pair_list_to_imported xs) H.
  cbn in Hdecoded.
  rewrite (l3_pair_source_roundtrip p) in Hdecoded.
  rewrite (l3_pair_list_source_roundtrip xs) in Hdecoded.
  exact Hdecoded.
Qed.

Definition l3_pair_list_mem_transport {T U : Type}
    (p : ImportedListLast.Prod T U)
    (xs ys : ImportedListLast.List (ImportedListLast.Prod T U)) :
  Lean.eq xs ys -> l3_pair_target_mem p xs -> l3_pair_target_mem p ys :=
  fun Hxy H =>
    match Hxy in Lean.eq _ zs return l3_pair_target_mem p zs with
    | Lean.eq_refl => H
    end.

Lemma l3_pair_membership_correspondence (T U : eqType)
    (p : T * U) (xsR : seq (T * U))
    (xsL : ImportedListLast.List (ImportedListLast.Prod T U)) :
  L3PairListRel xsR xsL ->
  PropSPropRel (p \in xsR)
    (l3_pair_target_mem (l3_pair_to_imported p) xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. apply (l3_pair_list_mem_transport _ _ _ Hxs).
    apply l3_pair_seq_mem_forward. exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply l3_pair_imported_mem_backward.
    exact (l3_pair_list_mem_transport _ _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Definition l3_target_zip {T U : Type}
    (xs : ImportedListLast.List T) (ys : ImportedListLast.List U) :
    ImportedListLast.List (ImportedListLast.Prod T U) :=
  ImportedListLast.List_zip T U xs ys.

Fixpoint l3_zip_canonical (T U : Type) (xs : seq T) :
  forall ys : seq U,
  Lean.eq (l3_pair_list_to_imported (zip xs ys))
    (l3_target_zip (lr_to_imported xs) (lr_to_imported ys)).
Proof.
  destruct xs as [|a xs]; intro ys.
  - destruct ys as [|b ys].
    + cbn [zip l3_pair_list_to_imported lr_to_imported l3_target_zip].
      exact (sub_imported_eq_sym _ _
        (ImportedListLast.Prosa_Validation_ListLastInterface_generic_zip_nil_left
          T U (ImportedListLast.List_nil U))).
    + cbn [zip l3_pair_list_to_imported lr_to_imported l3_target_zip].
      exact (sub_imported_eq_sym _ _
        (ImportedListLast.Prosa_Validation_ListLastInterface_generic_zip_nil_left
          T U (lr_to_imported (b :: ys)))).
  - destruct ys as [|b ys].
    + cbn [zip l3_pair_list_to_imported lr_to_imported l3_target_zip].
      exact (sub_imported_eq_sym _ _
        (ImportedListLast.Prosa_Validation_ListLastInterface_generic_zip_nil_right
          T U (lr_to_imported (a :: xs)))).
    + cbn [zip l3_pair_list_to_imported l3_pair_to_imported].
      exact (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr
          (ImportedListLast.List_cons (ImportedListLast.Prod T U)
            (ImportedListLast.Prod_mk T U a b)) _ _
          (l3_zip_canonical T U xs ys))
        (sub_imported_eq_sym _ _
          (ImportedListLast.Prosa_Validation_ListLastInterface_generic_zip_cons
            T U a (lr_to_imported xs) b (lr_to_imported ys)))).
Defined.

Lemma l3_zip_related (T U : Type) (xsR : seq T) (xsL : ImportedListLast.List T)
    (ysR : seq U) (ysL : ImportedListLast.List U) :
  LrListRel xsR xsL -> LrListRel ysR ysL ->
  L3PairListRel (zip xsR ysR) (l3_target_zip xsL ysL).
Proof.
  intros Hxs Hys. unfold L3PairListRel.
  exact (sub_imported_eq_trans _ _ _ (l3_zip_canonical T U xsR ysR)
    (sub_imported_eq_congr2 l3_target_zip _ _ _ _ Hxs Hys)).
Qed.

(** [index]/[idxOf] correspondence through the actual exported recursion
    equation and the approved MathComp equality decision. *)
Definition l3_target_idxOf (T : eqType) (x : T)
    (xs : ImportedListLast.List T) : Lean.Nat :=
  ImportedListLast.List_idxOf T
    (ImportedListLast.instBEqOfDecidableEq T (lr_decidable_eq T)) x xs.

Definition l3_target_eq_bool (T : eqType) (x y : T) :
    ImportedListLast.Bool :=
  ImportedListLast.Decidable_decide (Lean.eq x y) (lr_decidable_eq T x y).

Lemma l3_index_cons (T : eqType) (x a : T) (xs : seq T) :
  index x (a :: xs) = if a == x then O else S (index x xs).
Proof. by rewrite /= eq_sym. Qed.

Definition l3_target_cond_nat (b : ImportedListLast.Bool)
    (x y : Lean.Nat) : Lean.Nat := ImportedListLast.cond Lean.Nat b x y.

Lemma l3_cond_nat_related (bR : bool) (bL : ImportedListLast.Bool)
    (xR yR : nat) (xL yL : Lean.Nat) :
  LlBoolRel bR bL -> SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (if bR then xR else yR) (l3_target_cond_nat bL xL yL).
Proof.
  intros Hb Hx Hy. destruct bR; cbn in *.
  - exact (sub_imported_eq_trans _ _ _ Hx
      (sub_imported_eq_congr (fun b => l3_target_cond_nat b xL yL)
        _ _ Hb)).
  - exact (sub_imported_eq_trans _ _ _ Hy
      (sub_imported_eq_congr (fun b => l3_target_cond_nat b xL yL)
        _ _ Hb)).
Qed.

Lemma l3_zero_related : SubNatRel 0 ll_target_zero.
Proof.
  exact (sub_imported_eq_sym _ _
    ImportedListLast.Prosa_Validation_ListLastInterface_nat_zero).
Qed.

Definition l3_nat_source_transport (n m : nat) (nL : Lean.Nat) :
  Logic.eq n m -> SubNatRel n nL -> SubNatRel m nL :=
  fun H Hrel =>
    match H in Logic.eq _ k return SubNatRel k nL with
    | Logic.eq_refl => Hrel
    end.

Lemma l3_succ_related nR nL : SubNatRel nR nL ->
  SubNatRel (S nR) (lr_target_add nL ll_target_one).
Proof.
  intro Hn. apply (l3_nat_source_transport (nR + 1) (S nR) _ (addn1 nR)).
  exact (lr_add_related nR nL 1 ll_target_one Hn lr_one_related).
Qed.

Fixpoint l3_idxOf_canonical (T : eqType) (x : T) (xs : seq T) :
  SubNatRel (index x xs) (l3_target_idxOf T x (lr_to_imported xs)).
Proof.
  destruct xs as [|a xs].
  - exact (sub_imported_eq_trans _ _ _ l3_zero_related
      (sub_imported_eq_sym _ _
        (ImportedListLast.Prosa_Validation_ListLastInterface_generic_idxOf_nil
          T (lr_decidable_eq T) x))).
  - rewrite (l3_index_cons T x a xs).
    refine (sub_imported_eq_trans _ _ _
      (l3_cond_nat_related (a == x) (l3_target_eq_bool T a x)
        0 (index x xs).+1 ll_target_zero
        (lr_target_add (l3_target_idxOf T x (lr_to_imported xs)) ll_target_one)
        (sub_imported_eq_sym _ _ (lr_decide_eq_canonical T a x)) l3_zero_related
        (l3_succ_related _ _ (l3_idxOf_canonical T x xs))) _).
    exact (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_generic_idxOf_cons
        T (lr_decidable_eq T) x a (lr_to_imported xs))).
Defined.

Lemma l3_idxOf_related (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  LrListRel xsR xsL ->
  SubNatRel (index x xsR) (l3_target_idxOf T x xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _
    (l3_idxOf_canonical T x xsR)
    (sub_imported_eq_congr (l3_target_idxOf T x) _ _ Hxs)).
Qed.

Print Assumptions l3_uniq_correspondence.
Print Assumptions l3_getD_related.
Print Assumptions l3_all_related.
Print Assumptions l3_any_related.
Print Assumptions l3_isEmpty_related.
Print Assumptions l3_last_related.
Print Assumptions l3_membership_related.
Print Assumptions l3_nonempty_correspondence.
Print Assumptions l3_decide_le_related.
Print Assumptions l3_sorted_correspondence.
Print Assumptions l3_pair_membership_correspondence.
Print Assumptions l3_zip_related.
Print Assumptions l3_idxOf_related.
