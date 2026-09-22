From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPoet ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Artifact-local realization of the already approved
    [eqType -> Type + DecidableEq] and [seq -> List] boundaries. *)

Inductive PoFalse : SProp := .
Inductive PoTrue : SProp := po_true_intro.

Definition po_false_elim (Q : SProp) (H : PoFalse) : Q :=
  match H return Q with end.

Definition po_false_to_strict (H : PoFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition po_coq_false_to_target (H : Logic.False) :
    ImportedPoet.False := match H return ImportedPoet.False with end.

Definition po_bool_to_imported (b : bool) : ImportedPoet.Bool :=
  match b with
  | true => ImportedPoet.Bool_true
  | false => ImportedPoet.Bool_false
  end.

Definition po_bool_to_rocq (b : ImportedPoet.Bool) : bool :=
  match b with
  | ImportedPoet.Bool_true => true
  | ImportedPoet.Bool_false => false
  end.

Definition PoBoolRel (bR : bool) (bL : ImportedPoet.Bool) : SProp :=
  Lean.eq (po_bool_to_imported bR) bL.

Lemma po_bool_source_roundtrip (b : bool) :
  Logic.eq (po_bool_to_rocq (po_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma po_bool_target_roundtrip (b : ImportedPoet.Bool) :
  Lean.eq (po_bool_to_imported (po_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition po_false_ne_true
    (H : Lean.eq ImportedPoet.Bool_false ImportedPoet.Bool_true) :
    PoFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedPoet.Bool_false => PoTrue
    | ImportedPoet.Bool_true => PoFalse
    end
  with
  | Lean.eq_refl => po_true_intro
  end.

Lemma po_bool_truth_correspondence bR bL : PoBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedPoet.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (po_false_to_strict (po_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Lemma po_bool_eqb_correspondence aR aL bR bL :
  PoBoolRel aR aL -> PoBoolRel bR bL ->
  PropSPropRel (is_true (aR == bR)) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Heq. move/eqP: Heq => Heq. subst bR.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Ha) Hb).
  - intro Heq. apply strictly_inhabits. apply/eqP.
    have Hcanonical : Lean.eq (po_bool_to_imported aR)
        (po_bool_to_imported bR) :=
      sub_imported_eq_trans _ _ _ Ha
        (sub_imported_eq_trans _ _ _ Heq
          (sub_imported_eq_sym _ _ Hb)).
    have Hdecoded := f_equal po_bool_to_rocq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (po_bool_source_roundtrip aR) in Hdecoded.
    rewrite (po_bool_source_roundtrip bR) in Hdecoded.
    exact Hdecoded.
Qed.

Lemma po_bool_and_related aR aL bR bL :
  PoBoolRel aR aL -> PoBoolRel bR bL ->
  PoBoolRel (aR && bR) (ImportedPoet.Bool_and aL bL).
Proof.
  intros Ha Hb. destruct aR, bR; cbn in *;
    destruct aL, bL; try exact (@Lean.eq_refl _ _);
    try exact (po_false_elim _ (po_false_ne_true Ha));
    try exact (po_false_elim _ (po_false_ne_true Hb));
    try exact (po_false_elim _ (po_false_ne_true
      (sub_imported_eq_sym _ _ Ha)));
    try exact (po_false_elim _ (po_false_ne_true
      (sub_imported_eq_sym _ _ Hb))).
Qed.

Definition po_decidable_eq (T : eqType) : ImportedPoet.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedPoet.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedPoet.Decidable_isFalse (Lean.eq x y)
        (fun HL => po_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint po_list_to_imported {T : Type} (xs : seq T) :
    ImportedPoet.List T :=
  match xs with
  | [::] => ImportedPoet.List_nil T
  | x :: tail => ImportedPoet.List_cons T x (po_list_to_imported tail)
  end.

Fixpoint po_list_to_rocq {T : Type} (xs : ImportedPoet.List T) : seq T :=
  match xs with
  | ImportedPoet.List_nil => [::]
  | ImportedPoet.List_cons x tail => x :: po_list_to_rocq tail
  end.

Definition PoListRel {T : Type} (xsR : seq T)
    (xsL : ImportedPoet.List T) : SProp :=
  Lean.eq (po_list_to_imported xsR) xsL.

Lemma po_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (po_list_to_rocq (po_list_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma po_list_target_roundtrip {T : Type} (xs : ImportedPoet.List T) :
  Lean.eq (po_list_to_imported (po_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedPoet.List_cons T x) _ _ IH).
Qed.

Definition po_target_mem {T : Type} (x : T)
    (xs : ImportedPoet.List T) : SProp :=
  ImportedPoet.Membership_mem T (ImportedPoet.List T)
    (ImportedPoet.List_instMembership T) xs x.

Definition po_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedPoet.List T) :
  Lean.eq xs ys -> ImportedPoet.List_Mem T x xs ->
  ImportedPoet.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedPoet.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition po_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedPoet.List T) : Logic.eq x y ->
    ImportedPoet.List_Mem T x (ImportedPoet.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedPoet.List_Mem T x (ImportedPoet.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedPoet.List_Mem_head T x xs
    end.

Definition po_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition po_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition po_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint po_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedPoet.List_Mem T x (po_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedPoet.List_Mem T x (po_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedPoet.List_Mem T x
          (ImportedPoet.List_cons T y (po_list_to_imported ys)) with
      | ReflectT Hxy => fun _ => po_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedPoet.List_Mem_tail T x y _
          (po_seq_mem_forward x ys H)
      end
  end.

Fixpoint po_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedPoet.List T)
    (H : ImportedPoet.List_Mem T x xs) :
    SubNatTruth (x \in po_list_to_rocq xs) :=
  match H with
  | ImportedPoet.List_Mem_head ys =>
      po_mem_head_truth _ _ (po_eq_refl_truth T x)
  | ImportedPoet.List_Mem_tail y ys Htail =>
      po_mem_tail_truth _ _ (po_imported_mem_decoded x ys Htail)
  end.

Definition po_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma po_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedPoet.List T) :
  PoListRel xsR xsL ->
  PropSPropRel (x \in xsR) (po_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold po_target_mem.
    apply (po_list_mem_transport x _ _ Hxs).
    apply po_seq_mem_forward. exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (po_mem_truth_transport x _ _ (po_list_source_roundtrip xsR)).
    apply po_imported_mem_decoded.
    unfold po_target_mem in Hmem.
    exact (po_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Definition po_target_length {T : Type} (xs : ImportedPoet.List T) :
    Lean.Nat := ImportedPoet.List_length T xs.

Fixpoint po_length_canonical {T : Type} (xs : seq T) :
  SubNatRel (size xs) (po_target_length (po_list_to_imported xs)).
Proof.
  destruct xs as [|x xs].
  - unfold SubNatRel, po_target_length.
    exact (sub_imported_eq_sym _ _
      (ImportedPoet.Prosa_Validation_PoetInterface_production_length_nil T)).
  - cbn [size]. unfold SubNatRel in *.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr Lean.Nat_succ _ _
        (po_length_canonical T xs))
      (sub_imported_eq_sym _ _
        (ImportedPoet.Prosa_Validation_PoetInterface_production_length_cons
          T x (po_list_to_imported xs)))).
Defined.

Lemma po_length_related {T : Type} (xsR : seq T)
    (xsL : ImportedPoet.List T) : PoListRel xsR xsL ->
  SubNatRel (size xsR) (po_target_length xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _
    (po_length_canonical xsR)
    (sub_imported_eq_congr po_target_length _ _ Hxs)).
Qed.

(** Product and zip preserve source order and multiplicity. *)
Definition po_pair_to_imported {T U : Type} (p : T * U) :
    ImportedPoet.Prod T U :=
  match p with (x, y) => ImportedPoet.Prod_mk T U x y end.

Definition po_pair_to_rocq {T U : Type}
    (p : ImportedPoet.Prod T U) : T * U :=
  match p with ImportedPoet.Prod_mk x y => (x, y) end.

Lemma po_pair_source_roundtrip {T U : Type} (p : T * U) :
  Logic.eq (po_pair_to_rocq (po_pair_to_imported p)) p.
Proof. destruct p. reflexivity. Qed.

Lemma po_pair_target_roundtrip {T U : Type}
    (p : ImportedPoet.Prod T U) :
  Lean.eq (po_pair_to_imported (po_pair_to_rocq p)) p.
Proof. destruct p. exact (@Lean.eq_refl _ _). Qed.

Fixpoint po_pair_list_to_imported {T U : Type} (xs : seq (T * U)) :
    ImportedPoet.List (ImportedPoet.Prod T U) :=
  match xs with
  | [::] => ImportedPoet.List_nil (ImportedPoet.Prod T U)
  | p :: tail => ImportedPoet.List_cons (ImportedPoet.Prod T U)
      (po_pair_to_imported p) (po_pair_list_to_imported tail)
  end.

Definition PoPairListRel {T U : Type} (xsR : seq (T * U))
    (xsL : ImportedPoet.List (ImportedPoet.Prod T U)) : SProp :=
  Lean.eq (po_pair_list_to_imported xsR) xsL.

Definition po_target_zip {T U : Type}
    (xs : ImportedPoet.List T) (ys : ImportedPoet.List U) :
    ImportedPoet.List (ImportedPoet.Prod T U) :=
  ImportedPoet.List_zip T U xs ys.

Fixpoint po_zip_canonical (T U : Type) (xs : seq T) :
  forall ys : seq U,
  Lean.eq (po_pair_list_to_imported (zip xs ys))
    (po_target_zip (po_list_to_imported xs) (po_list_to_imported ys)).
Proof.
  destruct xs as [|x xs]; intro ys.
  - destruct ys as [|y ys];
      cbn [zip po_pair_list_to_imported po_list_to_imported po_target_zip].
    + exact (sub_imported_eq_sym _ _
        (ImportedPoet.Prosa_Validation_PoetInterface_production_zip_nil_left
          T U (ImportedPoet.List_nil U))).
    + exact (sub_imported_eq_sym _ _
        (ImportedPoet.Prosa_Validation_PoetInterface_production_zip_nil_left
          T U (po_list_to_imported (y :: ys)))).
  - destruct ys as [|y ys].
    + cbn [zip po_pair_list_to_imported po_list_to_imported po_target_zip].
      exact (sub_imported_eq_sym _ _
        (ImportedPoet.Prosa_Validation_PoetInterface_production_zip_nil_right
          T U (po_list_to_imported (x :: xs)))).
    + cbn [zip po_pair_list_to_imported po_list_to_imported
        po_pair_to_imported].
      exact (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr
          (ImportedPoet.List_cons (ImportedPoet.Prod T U)
            (ImportedPoet.Prod_mk T U x y)) _ _
          (po_zip_canonical T U xs ys))
        (sub_imported_eq_sym _ _
          (ImportedPoet.Prosa_Validation_PoetInterface_production_zip_cons
            T U x (po_list_to_imported xs) y (po_list_to_imported ys)))).
Defined.

Lemma po_zip_related (T U : Type)
    (xsR : seq T) (xsL : ImportedPoet.List T)
    (ysR : seq U) (ysL : ImportedPoet.List U) :
  PoListRel xsR xsL -> PoListRel ysR ysL ->
  PoPairListRel (zip xsR ysR) (po_target_zip xsL ysL).
Proof.
  intros Hxs Hys. unfold PoPairListRel.
  exact (sub_imported_eq_trans _ _ _ (po_zip_canonical T U xsR ysR)
    (sub_imported_eq_congr2 po_target_zip _ _ _ _ Hxs Hys)).
Qed.

Definition PoPairPredRel {T U : Type} (PR : T * U -> bool)
    (PL : ImportedPoet.Prod T U -> ImportedPoet.Bool) : SProp :=
  forall pR pL,
    Lean.eq (po_pair_to_imported pR) pL -> PoBoolRel (PR pR) (PL pL).

Definition po_pair_pred_to_imported {T U : Type} (PR : T * U -> bool)
    (p : ImportedPoet.Prod T U) : ImportedPoet.Bool :=
  po_bool_to_imported (PR (po_pair_to_rocq p)).

Lemma po_pair_pred_canonical {T U : Type} (PR : T * U -> bool) :
  PoPairPredRel PR (po_pair_pred_to_imported PR).
Proof.
  intros pR pL Hp. unfold PoBoolRel, po_pair_pred_to_imported.
  have Hback := f_equal po_pair_to_rocq
    (imported_eq_to_coq_eq _ _ Hp).
  rewrite (po_pair_source_roundtrip pR) in Hback.
  rewrite <- Hback. exact (@Lean.eq_refl _ _).
Qed.

Fixpoint po_all_canonical (T U : Type) (PR : T * U -> bool)
    (PL : ImportedPoet.Prod T U -> ImportedPoet.Bool)
    (HP : PoPairPredRel PR PL) (xs : seq (T * U)) :
  PoBoolRel (all PR xs)
    (ImportedPoet.List_all (ImportedPoet.Prod T U)
      (po_pair_list_to_imported xs) PL).
Proof.
  destruct xs as [|p xs].
  - unfold PoBoolRel.
    exact (sub_imported_eq_sym _ _
      (ImportedPoet.Prosa_Validation_PoetInterface_production_all_nil
        (ImportedPoet.Prod T U) PL)).
  - refine (sub_imported_eq_trans _ _ _
      (po_bool_and_related (PR p) (PL (po_pair_to_imported p))
        (all PR xs)
        (ImportedPoet.List_all (ImportedPoet.Prod T U)
          (po_pair_list_to_imported xs) PL)
        (HP p (po_pair_to_imported p) (@Lean.eq_refl _ _))
        (po_all_canonical T U PR PL HP xs)) _).
    exact (sub_imported_eq_sym _ _
      (ImportedPoet.Prosa_Validation_PoetInterface_production_all_cons
        (ImportedPoet.Prod T U) PL (po_pair_to_imported p)
        (po_pair_list_to_imported xs))).
Defined.

Lemma po_all_related (T U : Type) (PR : T * U -> bool)
    (PL : ImportedPoet.Prod T U -> ImportedPoet.Bool)
    (xsR : seq (T * U))
    (xsL : ImportedPoet.List (ImportedPoet.Prod T U)) :
  PoPairPredRel PR PL -> PoPairListRel xsR xsL ->
  PoBoolRel (all PR xsR)
    (ImportedPoet.List_all (ImportedPoet.Prod T U) xsL PL).
Proof.
  intros HP Hxs. exact (sub_imported_eq_trans _ _ _
    (po_all_canonical T U PR PL HP xsR)
    (sub_imported_eq_congr
      (fun zs => ImportedPoet.List_all (ImportedPoet.Prod T U) zs PL)
      _ _ Hxs)).
Qed.

(** Artifact-local logical constructors, composed only from lower-level
    operation correspondences. *)
Lemma po_and_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P /\ Q) (Lean.And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p q]. exact (Lean.And_intro PL QL
      (prop_to_sprop _ _ HP p) (prop_to_sprop _ _ HQ q)).
  - intros [p q]. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ HP p).
    + exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma po_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H pL. apply (prop_to_sprop _ _ HQ).
    apply H. exact (sprop_to_prop _ _ HP pL).
  - intro H. apply strictly_inhabits. intro p.
    apply (sprop_to_prop _ _ HQ).
    exact (H (prop_to_sprop _ _ HP p)).
Qed.

Lemma po_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P <-> Q) (ImportedPoet.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [HPQ HQP]. exact (ImportedPoet.Iff_intro PL QL
      (fun p => prop_to_sprop _ _ HQ (HPQ (sprop_to_prop _ _ HP p)))
      (fun q => prop_to_sprop _ _ HP (HQP (sprop_to_prop _ _ HQ q)))).
  - intro H. apply strictly_inhabits. split.
    + intro p. apply (sprop_to_prop _ _ HQ).
      exact (ImportedPoet.mp PL QL H (prop_to_sprop _ _ HP p)).
    + intro q. apply (sprop_to_prop _ _ HP).
      exact (ImportedPoet.mpr PL QL H (prop_to_sprop _ _ HQ q)).
Qed.

Lemma po_forall_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (HP x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _ (HP x) (HL x)).
Qed.

Lemma po_exists_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (ImportedPoet.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (ImportedPoet.Exists_intro T PL x
      (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x.
    exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma po_exists_list_correspondence (T : Type)
    (PR : seq T -> Prop) (PL : ImportedPoet.List T -> SProp) :
  (forall xsR xsL, PoListRel xsR xsL ->
    PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (exists xsR, PR xsR)
    (ImportedPoet.Exists (ImportedPoet.List T) PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [xsR Hxs]. exact (ImportedPoet.Exists_intro
      (ImportedPoet.List T) PL (po_list_to_imported xsR)
      (prop_to_sprop _ _
        (HP xsR (po_list_to_imported xsR) (@Lean.eq_refl _ _)) Hxs)).
  - intros [xsL Hxs]. apply strictly_inhabits.
    exists (po_list_to_rocq xsL).
    exact (sprop_to_prop _ _
      (HP (po_list_to_rocq xsL) xsL (po_list_target_roundtrip xsL)) Hxs).
Qed.

Definition PoProp2Rel {T U : Type} (PR : T -> U -> Prop)
    (PL : T -> U -> SProp) : Prop :=
  forall x y, PropSPropRel (PR x y) (PL x y).

Print Assumptions po_bool_truth_correspondence.
Print Assumptions po_membership_correspondence.
Print Assumptions po_length_related.
Print Assumptions po_zip_related.
Print Assumptions po_all_related.
