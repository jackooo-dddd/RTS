From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import util.notation.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBigcat ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Artifact-local adapter for the approved eqType/DecidableEq, Bool and
    ordered seq/List boundaries.  The imported datatypes are generated for
    this exact Bigcat export, so the adapter cannot be replaced by a
    same-named List bridge from another export artifact. *)

Inductive BcFalse : SProp := .
Inductive BcTrue : SProp := bc_true_intro.

Definition bc_false_elim (Q : SProp) (H : BcFalse) : Q :=
  match H return Q with end.

Definition bc_false_to_strict (H : BcFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition bc_coq_false_to_target (H : Logic.False) :
    ImportedBigcat.False := match H return ImportedBigcat.False with end.

Definition bc_target_false_elim (Q : SProp) (H : ImportedBigcat.False) : Q :=
  match H return Q with end.

Definition bc_target_false_to_strict (H : ImportedBigcat.False) :
    StrictlyInhabited Logic.False := match H with end.

Definition bc_bool_to_imported (b : bool) : ImportedBigcat.Bool :=
  match b with
  | true => ImportedBigcat.Bool_true
  | false => ImportedBigcat.Bool_false
  end.

Definition bc_bool_to_rocq (b : ImportedBigcat.Bool) : bool :=
  match b with
  | ImportedBigcat.Bool_true => true
  | ImportedBigcat.Bool_false => false
  end.

Definition BcBoolRel (bR : bool) (bL : ImportedBigcat.Bool) : SProp :=
  Lean.eq (bc_bool_to_imported bR) bL.

Lemma bc_bool_source_roundtrip b :
  Logic.eq (bc_bool_to_rocq (bc_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma bc_bool_target_roundtrip b :
  Lean.eq (bc_bool_to_imported (bc_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition bc_false_ne_true
    (H : Lean.eq ImportedBigcat.Bool_false ImportedBigcat.Bool_true) :
    BcFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedBigcat.Bool_false => BcTrue
    | ImportedBigcat.Bool_true => BcFalse
    end
  with
  | Lean.eq_refl => bc_true_intro
  end.

Lemma bc_bool_truth_correspondence bR bL : BcBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedBigcat.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (bc_false_to_strict (bc_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Lemma bc_bool_eq_correspondence aR aL bR bL :
  BcBoolRel aR aL -> BcBoolRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Ha) Hb).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (bc_bool_to_imported aR)
        (bc_bool_to_imported bR) :=
      sub_imported_eq_trans _ _ _ Ha
        (sub_imported_eq_trans _ _ _ Heq
          (sub_imported_eq_sym _ _ Hb)).
    have Hdecoded := f_equal bc_bool_to_rocq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (bc_bool_source_roundtrip aR) in Hdecoded.
    rewrite (bc_bool_source_roundtrip bR) in Hdecoded.
    exact Hdecoded.
Qed.

Lemma bc_bool_and_related aR aL bR bL :
  BcBoolRel aR aL -> BcBoolRel bR bL ->
  BcBoolRel (aR && bR) (ImportedBigcat.Bool_and aL bL).
Proof.
  intros Ha Hb. destruct aR, bR; cbn in *;
    destruct aL, bL; try exact (@Lean.eq_refl _ _);
    try exact (bc_false_elim _ (bc_false_ne_true Ha));
    try exact (bc_false_elim _ (bc_false_ne_true Hb));
    try exact (bc_false_elim _ (bc_false_ne_true
      (sub_imported_eq_sym _ _ Ha)));
    try exact (bc_false_elim _ (bc_false_ne_true
      (sub_imported_eq_sym _ _ Hb))).
Qed.

Definition bc_decidable_eq (T : eqType) : ImportedBigcat.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedBigcat.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedBigcat.Decidable_isFalse (Lean.eq x y)
        (fun HL => bc_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Definition bc_target_decide_eq (T : eqType) (x y : T) :
    ImportedBigcat.Bool :=
  ImportedBigcat.Decidable_decide (Lean.eq x y) (bc_decidable_eq T x y).

Lemma bc_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedBigcat.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  BcBoolRel b (ImportedBigcat.Decidable_decide Q d).
Proof.
  intro Hrel. unfold BcBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (bc_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (bc_target_false_elim _ (bc_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Lemma bc_decide_eq_related (T : eqType) (x y : T) :
  BcBoolRel (x == y) (bc_target_decide_eq T x y).
Proof.
  apply bc_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - intro Hxy. move/eqP: Hxy => Hxy.
    exact (coq_eq_to_imported_eq x y Hxy).
  - intro Hxy. apply strictly_inhabits. apply/eqP.
    exact (imported_eq_to_coq_eq x y Hxy).
Qed.

Definition bc_target_ne (T : Type) (x y : T) : SProp :=
  ImportedBigcat.Ne T x y.

Lemma bc_ne_correspondence (T : Type) (x y : T) :
  PropSPropRel (x <> y) (bc_target_ne T x y).
Proof.
  apply prop_sprop_rel_intro.
  - intros Hne Hxy. apply bc_coq_false_to_target. apply Hne.
    exact (imported_eq_to_coq_eq x y Hxy).
  - intro Hne. apply strictly_inhabits. intro Hxy.
    exact (interpret_strict Logic.False
      (bc_target_false_to_strict
        (Hne (coq_eq_to_imported_eq x y Hxy)))).
Qed.

Lemma bc_bool_ne_correspondence (T : eqType) (x y : T) :
  PropSPropRel (is_true (x != y)) (bc_target_ne T x y).
Proof.
  apply prop_sprop_rel_intro.
  - intros Hne Hxy. apply bc_coq_false_to_target.
    move/negP: Hne => Hne. apply Hne. apply/eqP.
    exact (imported_eq_to_coq_eq x y Hxy).
  - intro Hne. apply strictly_inhabits. apply/negP. intro Hxy.
    exact (interpret_strict Logic.False
      (bc_target_false_to_strict
        (Hne (coq_eq_to_imported_eq x y (elimT eqP Hxy))))).
Qed.

Fixpoint bc_to_imported {T : Type} (xs : seq T) :
    ImportedBigcat.List T :=
  match xs with
  | [::] => ImportedBigcat.List_nil T
  | x :: tail => ImportedBigcat.List_cons T x (bc_to_imported tail)
  end.

Fixpoint bc_to_rocq {T : Type} (xs : ImportedBigcat.List T) : seq T :=
  match xs with
  | ImportedBigcat.List_nil => [::]
  | ImportedBigcat.List_cons x tail => x :: bc_to_rocq tail
  end.

Definition BcListRel {T : Type} (xsR : seq T)
    (xsL : ImportedBigcat.List T) : SProp :=
  Lean.eq (bc_to_imported xsR) xsL.

Lemma bc_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (bc_to_rocq (bc_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma bc_list_target_roundtrip {T : Type} (xs : ImportedBigcat.List T) :
  Lean.eq (bc_to_imported (bc_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (ImportedBigcat.List_cons T x) _ _ IH).
Qed.

Definition bc_target_mem {T : Type} (x : T)
    (xs : ImportedBigcat.List T) : SProp :=
  ImportedBigcat.Membership_mem T (ImportedBigcat.List T)
    (ImportedBigcat.List_instMembership T) xs x.

Definition bc_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedBigcat.List T) :
  Lean.eq xs ys -> ImportedBigcat.List_Mem T x xs ->
  ImportedBigcat.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedBigcat.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition bc_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedBigcat.List T) : Logic.eq x y ->
    ImportedBigcat.List_Mem T x (ImportedBigcat.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedBigcat.List_Mem T x (ImportedBigcat.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedBigcat.List_Mem_head T x xs
    end.

Definition bc_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition bc_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition bc_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint bc_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedBigcat.List_Mem T x (bc_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedBigcat.List_Mem T x (bc_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedBigcat.List_Mem T x
          (ImportedBigcat.List_cons T y (bc_to_imported ys)) with
      | ReflectT Hxy => fun _ => bc_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedBigcat.List_Mem_tail T x y _
          (bc_seq_mem_forward x ys H)
      end
  end.

Fixpoint bc_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedBigcat.List T)
    (H : ImportedBigcat.List_Mem T x xs) :
    SubNatTruth (x \in bc_to_rocq xs) :=
  match H with
  | ImportedBigcat.List_Mem_head ys =>
      bc_mem_head_truth _ _ (bc_eq_refl_truth T x)
  | ImportedBigcat.List_Mem_tail y ys Htail =>
      bc_mem_tail_truth _ _ (bc_imported_mem_decoded x ys Htail)
  end.

Definition bc_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma bc_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedBigcat.List T) :
  BcListRel xsR xsL ->
  PropSPropRel (x \in xsR) (bc_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold bc_target_mem.
    apply (bc_list_mem_transport x _ _ Hxs).
    apply bc_seq_mem_forward. exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (bc_mem_truth_transport x _ _ (bc_list_source_roundtrip xsR)).
    apply bc_imported_mem_decoded. unfold bc_target_mem in Hmem.
    exact (bc_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Definition bc_target_decide_mem (T : eqType) (x : T)
    (xs : ImportedBigcat.List T) : ImportedBigcat.Bool :=
  ImportedBigcat.Decidable_decide (bc_target_mem x xs)
    (ImportedBigcat.List_instDecidableMemOfLawfulBEq T
      (ImportedBigcat.instBEqOfDecidableEq T (bc_decidable_eq T))
      (ImportedBigcat.instLawfulBEq T (bc_decidable_eq T)) x xs).

Lemma bc_decide_mem_related (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedBigcat.List T) :
  BcListRel xsR xsL ->
  BcBoolRel (x \in xsR) (bc_target_decide_mem T x xsL).
Proof.
  intro Hxs. apply bc_decide_bool_correspondence.
  exact (bc_membership_correspondence T x xsR xsL Hxs).
Qed.

Definition BcPredRel {T : Type} (PR : T -> bool)
    (PL : T -> ImportedBigcat.Bool) : SProp :=
  forall x, BcBoolRel (PR x) (PL x).

Definition bc_pred_to_imported {T : Type} (PR : T -> bool) :
    T -> ImportedBigcat.Bool := fun x => bc_bool_to_imported (PR x).

Definition bc_pred_to_rocq {T : Type}
    (PL : T -> ImportedBigcat.Bool) : T -> bool :=
  fun x => bc_bool_to_rocq (PL x).

Lemma bc_pred_canonical {T : Type} (PR : T -> bool) :
  BcPredRel PR (bc_pred_to_imported PR).
Proof. intro x. exact (@Lean.eq_refl _ _). Qed.

Lemma bc_pred_surjective {T : Type} (PL : T -> ImportedBigcat.Bool) :
  BcPredRel (bc_pred_to_rocq PL) PL.
Proof. intro x. exact (bc_bool_target_roundtrip (PL x)). Qed.

Definition bc_target_append {T : Type} (xs ys : ImportedBigcat.List T) :
    ImportedBigcat.List T :=
  ImportedBigcat.HAppend_hAppend (ImportedBigcat.List T)
    (ImportedBigcat.List T) (ImportedBigcat.List T)
    (ImportedBigcat.instHAppendOfAppend (ImportedBigcat.List T)
      (ImportedBigcat.List_instAppend T)) xs ys.

Lemma bc_append_canonical (T : Type) (xs ys : seq T) :
  Lean.eq (bc_target_append (bc_to_imported xs) (bc_to_imported ys))
    (bc_to_imported (xs ++ ys)).
Proof.
  induction xs as [|x xs IH].
  - exact (ImportedBigcat.Prosa_Validation_BigcatInterface_production_append_nil
      T (bc_to_imported ys)).
  - refine (sub_imported_eq_trans _ _ _
      (ImportedBigcat.Prosa_Validation_BigcatInterface_production_append_cons
        T x (bc_to_imported xs) (bc_to_imported ys)) _).
    exact (sub_imported_eq_congr (ImportedBigcat.List_cons T x) _ _ IH).
Qed.

Lemma bc_append_related (T : Type)
    (xsR ysR : seq T) (xsL ysL : ImportedBigcat.List T) :
  BcListRel xsR xsL -> BcListRel ysR ysL ->
  BcListRel (xsR ++ ysR) (bc_target_append xsL ysL).
Proof.
  intros Hxs Hys. unfold BcListRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (bc_append_canonical T xsR ysR))
    (sub_imported_eq_congr2 bc_target_append _ _ _ _ Hxs Hys)).
Qed.

Definition bc_target_filter {T : Type}
    (P : T -> ImportedBigcat.Bool) (xs : ImportedBigcat.List T) :
    ImportedBigcat.List T := ImportedBigcat.List_filter T P xs.

Definition bc_filter_match {T : Type} (b : ImportedBigcat.Bool)
    (x : T) (tail : ImportedBigcat.List T) : ImportedBigcat.List T :=
  ImportedBigcat.Prosa_Validation_BigcatInterface_production_filter_cons_match_1
    (fun _ : ImportedBigcat.Bool => ImportedBigcat.List T) b
    (fun _ : ImportedBigcat.Unit => ImportedBigcat.List_cons T x tail)
    (fun _ : ImportedBigcat.Unit => tail).

Lemma bc_filter_match_canonical {T : Type} (b : bool) (x : T)
    (tail : ImportedBigcat.List T) :
  Lean.eq (bc_filter_match (bc_bool_to_imported b) x tail)
    (match b with
     | true => ImportedBigcat.List_cons T x tail
     | false => tail
     end).
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma bc_filter_branch_canonical {T : Type} (b : bool) (x : T)
    (filtered : seq T) (tail : ImportedBigcat.List T) :
  Lean.eq tail (bc_to_imported filtered) ->
  Lean.eq
    (match b with
     | true => ImportedBigcat.List_cons T x tail
     | false => tail
     end)
    (bc_to_imported
      (match b with true => x :: filtered | false => filtered end)).
Proof.
  intro IH. destruct b; cbn.
  - exact (sub_imported_eq_congr (ImportedBigcat.List_cons T x) _ _ IH).
  - exact IH.
Qed.

Lemma bc_source_filter_cons {T : Type} (P : T -> bool)
    (x : T) (xs : seq T) :
  Logic.eq
    (match P x with
     | true => x :: [seq y <- xs | P y]
     | false => [seq y <- xs | P y]
     end)
    [seq y <- x :: xs | P y].
Proof. cbn. destruct (P x); reflexivity. Qed.

Lemma bc_filter_canonical (T : Type) (PR : T -> bool)
    (PL : T -> ImportedBigcat.Bool) : BcPredRel PR PL ->
  forall xs : seq T,
  Lean.eq (bc_target_filter PL (bc_to_imported xs))
    (bc_to_imported [seq x <- xs | PR x]).
Proof.
  intro HP. induction xs as [|x xs IH].
  - exact (ImportedBigcat.Prosa_Validation_BigcatInterface_production_filter_nil
      T PL).
  - refine (sub_imported_eq_trans _ _ _
      (ImportedBigcat.Prosa_Validation_BigcatInterface_production_filter_cons
        T PL x (bc_to_imported xs)) _).
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (fun b => bc_filter_match b x
          (bc_target_filter PL (bc_to_imported xs))) _ _
        (sub_imported_eq_sym _ _ (HP x))) _).
    refine (sub_imported_eq_trans _ _ _
      (bc_filter_match_canonical (PR x) x
        (bc_target_filter PL (bc_to_imported xs))) _).
    refine (sub_imported_eq_trans _ _ _
      (bc_filter_branch_canonical (PR x) x
        [seq y <- xs | PR y]
        (bc_target_filter PL (bc_to_imported xs)) IH) _).
    exact (coq_eq_to_imported_eq _ _
      (f_equal bc_to_imported (bc_source_filter_cons PR x xs))).
Qed.

Lemma bc_filter_related (T : Type) (PR : T -> bool)
    (PL : T -> ImportedBigcat.Bool) (xsR : seq T)
    (xsL : ImportedBigcat.List T) :
  BcPredRel PR PL -> BcListRel xsR xsL ->
  BcListRel [seq x <- xsR | PR x] (bc_target_filter PL xsL).
Proof.
  intros HP Hxs. unfold BcListRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (bc_filter_canonical T PR PL HP xsR))
    (sub_imported_eq_congr (bc_target_filter PL) _ _ Hxs)).
Qed.

Definition BcListFamilyRel {X Y : Type} (fR : X -> seq Y)
    (fL : X -> ImportedBigcat.List Y) : SProp :=
  forall x, BcListRel (fR x) (fL x).

Definition bc_family_to_imported {X Y : Type} (f : X -> seq Y) :
    X -> ImportedBigcat.List Y := fun x => bc_to_imported (f x).

Lemma bc_family_canonical {X Y : Type} (f : X -> seq Y) :
  BcListFamilyRel f (bc_family_to_imported f).
Proof. intro x. exact (@Lean.eq_refl _ _). Qed.

Lemma bc_decide_eq_filter_family_related (X Y : eqType)
    (f : X -> seq Y) (g : Y -> X) (y : X) :
  BcListFamilyRel
    (fun x => [seq z <- f x | g z == y])
    (fun x => bc_target_filter
      (fun z => bc_target_decide_eq X (g z) y)
      (bc_to_imported (f x))).
Proof.
  intro x. apply bc_filter_related.
  - intro z. exact (bc_decide_eq_related X (g z) y).
  - exact (@Lean.eq_refl _ _).
Qed.

Definition bc_target_flatMap {X Y : Type}
    (f : X -> ImportedBigcat.List Y) (xs : ImportedBigcat.List X) :
    ImportedBigcat.List Y := ImportedBigcat.List_flatMap X Y f xs.

Lemma bc_flatMap_canonical (X Y : Type)
    (fR : X -> seq Y) (fL : X -> ImportedBigcat.List Y) :
  BcListFamilyRel fR fL -> forall xs : seq X,
  Lean.eq (bc_target_flatMap fL (bc_to_imported xs))
    (bc_to_imported (flatten [seq fR x | x <- xs])).
Proof.
  intro Hf. induction xs as [|x xs IH].
  - exact (ImportedBigcat.Prosa_Validation_BigcatInterface_production_flatMap_nil
      X Y fL).
  - refine (sub_imported_eq_trans _ _ _
      (ImportedBigcat.Prosa_Validation_BigcatInterface_production_flatMap_cons
        X Y fL x (bc_to_imported xs)) _).
    cbn [flatten].
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr2 bc_target_append _ _ _ _
        (sub_imported_eq_sym _ _ (Hf x)) IH)
      (bc_append_canonical Y (fR x)
        (flatten [seq fR z | z <- xs]))).
Qed.

Lemma bc_flatMap_related (X Y : Type)
    (fR : X -> seq Y) (fL : X -> ImportedBigcat.List Y)
    (xsR : seq X) (xsL : ImportedBigcat.List X) :
  BcListFamilyRel fR fL -> BcListRel xsR xsL ->
  BcListRel (flatten [seq fR x | x <- xsR])
    (bc_target_flatMap fL xsL).
Proof.
  intros Hf Hxs. unfold BcListRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (bc_flatMap_canonical X Y fR fL Hf xsR))
    (sub_imported_eq_congr (bc_target_flatMap fL) _ _ Hxs)).
Qed.

Definition bc_target_bigCatSeqAll (X Y : Type)
    (xs : ImportedBigcat.List X) (f : X -> ImportedBigcat.List Y) :
    ImportedBigcat.List Y :=
  ImportedBigcat.Prosa_Util_Bigcat_bigCatSeqAll X Y xs f.

Lemma bc_source_bigcat_seq_as_flatten (X Y : Type)
    (f : X -> seq Y) (xs : seq X) :
  Logic.eq (\cat_(x <- xs) f x) (flatten [seq f x | x <- xs]).
Proof.
  induction xs as [|x xs IH].
  - by rewrite big_nil.
  - by rewrite big_cons /= IH.
Qed.

Lemma bc_source_bigcat_filter_as_flatten (X Y : Type)
    (f : X -> seq Y) (P : X -> bool) (xs : seq X) :
  Logic.eq (\cat_(x <- xs | P x) f x)
    (flatten [seq f x | x <- [seq x <- xs | P x]]).
Proof.
  induction xs as [|x xs IH].
  - by rewrite big_nil.
  - rewrite big_cons /=. case HP: (P x); cbn.
    + by rewrite IH.
    + exact IH.
Qed.

Lemma bc_bigCatSeqAll_related (X Y : Type)
    (fR : X -> seq Y) (fL : X -> ImportedBigcat.List Y)
    (xsR : seq X) (xsL : ImportedBigcat.List X) :
  BcListFamilyRel fR fL -> BcListRel xsR xsL ->
  BcListRel (\cat_(x <- xsR) fR x)
    (bc_target_bigCatSeqAll X Y xsL fL).
Proof.
  intros Hf Hxs. unfold BcListRel, bc_target_bigCatSeqAll.
  refine (sub_imported_eq_trans _ _ _ _
    (sub_imported_eq_sym _ _
      (ImportedBigcat.Prosa_Validation_BigcatInterface_production_bigCatSeqAll_eq
        X Y xsL fL))).
  have Hflat := bc_flatMap_related X Y fR fL xsR xsL Hf Hxs.
  unfold BcListRel, bc_target_flatMap in Hflat.
  exact (sub_imported_eq_trans _ _ _
    (coq_eq_to_imported_eq _ _
      (f_equal bc_to_imported
        (bc_source_bigcat_seq_as_flatten X Y fR xsR))) Hflat).
Qed.

Definition bc_target_bigCatSeq (X Y : Type)
    (xs : ImportedBigcat.List X) (P : X -> ImportedBigcat.Bool)
    (f : X -> ImportedBigcat.List Y) : ImportedBigcat.List Y :=
  ImportedBigcat.Prosa_Util_Bigcat_bigCatSeq X Y xs P f.

Lemma bc_bigCatSeq_related (X Y : Type)
    (fR : X -> seq Y) (fL : X -> ImportedBigcat.List Y)
    (PR : X -> bool) (PL : X -> ImportedBigcat.Bool)
    (xsR : seq X) (xsL : ImportedBigcat.List X) :
  BcListFamilyRel fR fL -> BcPredRel PR PL -> BcListRel xsR xsL ->
  BcListRel (\cat_(x <- xsR | PR x) fR x)
    (bc_target_bigCatSeq X Y xsL PL fL).
Proof.
  intros Hf HP Hxs. unfold BcListRel, bc_target_bigCatSeq.
  refine (sub_imported_eq_trans _ _ _ _
    (sub_imported_eq_sym _ _
      (ImportedBigcat.Prosa_Validation_BigcatInterface_production_bigCatSeq_eq
        X Y xsL PL fL))).
  have Hfilter := bc_filter_related X PR PL xsR xsL HP Hxs.
  have Hflat := bc_flatMap_related X Y fR fL
    [seq x <- xsR | PR x] (bc_target_filter PL xsL) Hf Hfilter.
  unfold BcListRel, bc_target_flatMap in Hflat.
  exact (sub_imported_eq_trans _ _ _
    (coq_eq_to_imported_eq _ _
      (f_equal bc_to_imported
        (bc_source_bigcat_filter_as_flatten X Y fR PR xsR))) Hflat).
Qed.

Lemma bc_list_eq_correspondence (T : Type)
    (xsR ysR : seq T) (xsL ysL : ImportedBigcat.List T) :
  BcListRel xsR xsL -> BcListRel ysR ysL ->
  PropSPropRel (Logic.eq xsR ysR) (Lean.eq xsL ysL).
Proof.
  intros Hxs Hys. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Hxs) Hys).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (bc_to_imported xsR) (bc_to_imported ysR) :=
      sub_imported_eq_trans _ _ _ Hxs
        (sub_imported_eq_trans _ _ _ Heq
          (sub_imported_eq_sym _ _ Hys)).
    have Hdecoded := f_equal bc_to_rocq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (bc_list_source_roundtrip xsR) in Hdecoded.
    rewrite (bc_list_source_roundtrip ysR) in Hdecoded.
    exact Hdecoded.
Qed.

Definition bc_nodup_transport {T : Type}
    (xs ys : ImportedBigcat.List T) :
  Lean.eq xs ys -> ImportedBigcat.List_Nodup T xs ->
  ImportedBigcat.List_Nodup T ys :=
  fun Hxy H =>
    match Hxy in Lean.eq _ zs return ImportedBigcat.List_Nodup T zs with
    | Lean.eq_refl => H
    end.

Definition bc_and_left_truth (a b : bool) :
    SubNatTruth (a && b) -> SubNatTruth a :=
  match a, b return SubNatTruth (a && b) -> SubNatTruth a with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => fun H => H
  end.

Definition bc_and_right_truth (a b : bool) :
    SubNatTruth (a && b) -> SubNatTruth b :=
  match a, b return SubNatTruth (a && b) -> SubNatTruth b with
  | true, true => fun _ => sub_nat_truth_intro
  | true, false => fun H => H
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Definition bc_neg_mem_contra (b : bool) :
    SubNatTruth (~~ b) -> SubNatTruth b -> ImportedBigcat.False :=
  match b return SubNatTruth (~~ b) -> SubNatTruth b -> ImportedBigcat.False with
  | true => fun H _ => match H with end
  | false => fun _ H => match H with end
  end.

Fixpoint bc_uniq_truth_forward (T : eqType) (xs : seq T) :
    SubNatTruth (uniq xs) -> ImportedBigcat.List_Nodup T (bc_to_imported xs).
Proof.
  destruct xs as [|x xs].
  - intro Hnil. exact (ImportedBigcat.List_Pairwise_nil T (ImportedBigcat.Ne T)).
  - intro Huniq. apply ImportedBigcat.List_Pairwise_cons.
    + intros y Hy Hxy.
      have HyR := sprop_to_prop _ _
        (bc_membership_correspondence T y xs (bc_to_imported xs)
          (@Lean.eq_refl _ _)) Hy.
      have Hcoq : Logic.eq x y := imported_eq_to_coq_eq x y Hxy.
      subst y.
      exact (bc_neg_mem_contra (x \in xs)
        (bc_and_left_truth _ _ Huniq) (sub_nat_prop_to_truth _ HyR)).
    + exact (bc_uniq_truth_forward T xs (bc_and_right_truth _ _ Huniq)).
Defined.

Definition bc_uniq_forward (T : eqType) (xs : seq T) :
    uniq xs -> ImportedBigcat.List_Nodup T (bc_to_imported xs) :=
  fun H => bc_uniq_truth_forward T xs (sub_nat_prop_to_truth _ H).

Lemma bc_imported_nodup_backward (T : eqType)
    (xs : ImportedBigcat.List T) :
  ImportedBigcat.List_Nodup T xs -> StrictlyInhabited (uniq (bc_to_rocq xs)).
Proof.
  intro Hnodup. induction Hnodup as [|y ys Hhead Htail IH].
  - exact (strictly_inhabits (Logic.eq_refl true)).
  - destruct IH as [IHuniq]. apply strictly_inhabits.
    apply/andP. split; last exact IHuniq.
    apply/negP. intro Hmem.
    have HmemL := prop_to_sprop _ _
      (bc_membership_correspondence T y (bc_to_rocq ys) ys
        (bc_list_target_roundtrip ys)) Hmem.
    have Hneq := Hhead y HmemL.
    exact (interpret_strict Logic.False
      (bc_target_false_to_strict (Hneq (@Lean.eq_refl T y)))).
Qed.

Lemma bc_uniq_correspondence (T : eqType)
    (xsR : seq T) (xsL : ImportedBigcat.List T) :
  BcListRel xsR xsL ->
  PropSPropRel (uniq xsR) (ImportedBigcat.List_Nodup T xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Huniq. exact (bc_nodup_transport _ _ Hxs
      (bc_uniq_forward T xsR Huniq)).
  - intro Hnodup.
    have Hcanonical := bc_nodup_transport _ _
      (sub_imported_eq_sym _ _ Hxs) Hnodup.
    have Hstrict := bc_imported_nodup_backward T
      (bc_to_imported xsR) Hcanonical.
    destruct Hstrict as [Huniq]. apply strictly_inhabits.
    rewrite (bc_list_source_roundtrip xsR) in Huniq.
    exact Huniq.
Qed.

Definition bc_target_length {T : Type} (xs : ImportedBigcat.List T) :
    Lean.Nat := ImportedBigcat.List_length T xs.

Lemma bc_length_canonical (T : Type) (xs : seq T) :
  SubNatRel (size xs) (bc_target_length (bc_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (sub_imported_eq_sym _ _
      (ImportedBigcat.Prosa_Validation_BigcatInterface_production_length_nil T)).
  - unfold SubNatRel in IH |- *.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr Lean.Nat_succ _ _ IH)
      (sub_imported_eq_sym _ _
        (ImportedBigcat.Prosa_Validation_BigcatInterface_production_length_cons
          T x (bc_to_imported xs)))).
Qed.

Lemma bc_length_related (T : Type) (xsR : seq T)
    (xsL : ImportedBigcat.List T) : BcListRel xsR xsL ->
  SubNatRel (size xsR) (bc_target_length xsL).
Proof.
  intro Hxs. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _ (bc_length_canonical T xsR)
    (sub_imported_eq_congr bc_target_length _ _ Hxs)).
Qed.

(** Half-open natural-interval concatenation. *)
Definition bc_nat_family_to_imported {T : Type} (f : nat -> seq T) :
    Lean.Nat -> ImportedBigcat.List T :=
  fun i => bc_to_imported (f (sub_nat_to_rocq i)).

Definition BcNatFamilyRel {T : Type} (fR : nat -> seq T)
    (fL : Lean.Nat -> ImportedBigcat.List T) : SProp :=
  forall iR iL, SubNatRel iR iL -> BcListRel (fR iR) (fL iL).

Lemma bc_nat_family_value_related (T : Type) (f : nat -> seq T) (i : nat) :
  BcListRel (f i)
    (bc_nat_family_to_imported f (sub_nat_to_imported i)).
Proof.
  unfold BcListRel, bc_nat_family_to_imported.
  exact (sub_imported_eq_sym _ _
    (coq_eq_to_imported_eq _ _
      (f_equal bc_to_imported
        (f_equal f (sub_nat_rocq_roundtrip i))))).
Qed.

Lemma bc_nat_family_canonical (T : Type) (f : nat -> seq T) :
  BcNatFamilyRel f (bc_nat_family_to_imported f).
Proof.
  intros iR iL Hi. unfold SubNatRel in Hi. destruct Hi.
  exact (bc_nat_family_value_related T f iR).
Qed.

Lemma bc_filtered_nat_family_related (T : Type)
    (f : nat -> seq T) (P : T -> bool) :
  BcNatFamilyRel (fun i => [seq x <- f i | P x])
    (fun i => bc_target_filter (bc_pred_to_imported P)
      (bc_nat_family_to_imported f i)).
Proof.
  intros iR iL Hi. exact (bc_filter_related T P
    (bc_pred_to_imported P) (f iR) (bc_nat_family_to_imported f iL)
    (bc_pred_canonical P) (bc_nat_family_canonical T f iR iL Hi)).
Qed.

Lemma bc_nat_family_add_value_related (T : Type)
    (f : nat -> seq T) (m d : nat) :
  BcListRel (f (m + d))
    (bc_nat_family_to_imported f
      (Lean.Nat_add (sub_nat_to_imported m) (sub_nat_to_imported d))).
Proof.
  unfold BcListRel.
  exact (sub_imported_eq_trans _ _ _
    (bc_nat_family_value_related T f (m + d))
    (sub_imported_eq_congr (bc_nat_family_to_imported f) _ _
      (sub_add_correspondence m (sub_nat_to_imported m)
        d (sub_nat_to_imported d)
        (sub_nat_rel_canonical m) (sub_nat_rel_canonical d)))).
Qed.

Definition bc_target_bigCat_nat {T : Type}
    (m n : Lean.Nat) (f : Lean.Nat -> ImportedBigcat.List T) :
    ImportedBigcat.List T :=
  ImportedBigcat.Prosa_Util_Notation_bigCat T m n f.

Definition bc_target_bigCat_nat_delta {T : Type}
    (m d : Lean.Nat) (f : Lean.Nat -> ImportedBigcat.List T) :
    ImportedBigcat.List T :=
  bc_target_bigCat_nat m (Lean.Nat_add m d) f.

Definition bc_target_le (a b : Lean.Nat) : SProp :=
  ImportedBigcat.LE_le_inst1 Lean.Nat ImportedBigcat.instLENat a b.

Definition bc_target_lt (a b : Lean.Nat) : SProp :=
  ImportedBigcat.LT_lt_inst1 Lean.Nat ImportedBigcat.instLTNat a b.

Lemma bc_nat_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (bc_target_le aL bL).
Proof.
  intros Ha Hb. unfold bc_target_le.
  exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma bc_nat_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (bc_target_lt aL bL).
Proof.
  intros Ha Hb. unfold bc_target_lt.
  exact (sub_nat_lt_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma bc_bigCatNat_delta_related_rel (T : Type)
    (fR : nat -> seq T) (fL : Lean.Nat -> ImportedBigcat.List T)
    (m d : nat) :
  BcNatFamilyRel fR fL ->
  BcListRel (\cat_(m <= i < m + d) fR i)
    (bc_target_bigCat_nat_delta
      (sub_nat_to_imported m) (sub_nat_to_imported d) fL).
Proof.
  intro Hf. induction d as [|d IH].
  - rewrite addn0 big_geq //.
    unfold BcListRel, bc_target_bigCat_nat_delta,
      bc_target_bigCat_nat. cbn.
    exact (sub_imported_eq_sym _ _
      (ImportedBigcat.Prosa_Validation_BigcatInterface_production_bigCat_same
        T (sub_nat_to_imported m) fL)).
  - rewrite addnS big_nat_recr.
    exact (leq_addr d m).
    have Happ := bc_append_related T
      (\cat_(m <= i < m + d) fR i) (fR (m + d))
      (bc_target_bigCat_nat_delta
        (sub_nat_to_imported m) (sub_nat_to_imported d) fL)
      (fL (Lean.Nat_add
        (sub_nat_to_imported m) (sub_nat_to_imported d)))
      IH (Hf (m + d)
        (Lean.Nat_add (sub_nat_to_imported m) (sub_nat_to_imported d))
        (sub_add_correspondence m (sub_nat_to_imported m)
          d (sub_nat_to_imported d)
          (sub_nat_rel_canonical m) (sub_nat_rel_canonical d))).
    unfold BcListRel, bc_target_bigCat_nat_delta,
      bc_target_bigCat_nat in Happ |- *.
    exact (sub_imported_eq_trans _ _ _ Happ
      (sub_imported_eq_sym _ _
        (ImportedBigcat.Prosa_Validation_BigcatInterface_production_bigCat_add_succ
          T (sub_nat_to_imported m) (sub_nat_to_imported d) fL))).
Qed.

Lemma bc_bigCatNat_delta_related (T : Type) (f : nat -> seq T)
    (m d : nat) :
  BcListRel (\cat_(m <= i < m + d) f i)
    (bc_target_bigCat_nat_delta
      (sub_nat_to_imported m) (sub_nat_to_imported d)
      (bc_nat_family_to_imported f)).
Proof.
  exact (bc_bigCatNat_delta_related_rel T f
    (bc_nat_family_to_imported f) m d (bc_nat_family_canonical T f)).
Qed.

Lemma bc_bigCatNat_related_rel (T : Type)
    (fR : nat -> seq T) (fL : Lean.Nat -> ImportedBigcat.List T)
    (m n : nat) :
  BcNatFamilyRel fR fL ->
  BcListRel (\cat_(m <= i < n) fR i)
    (bc_target_bigCat_nat (sub_nat_to_imported m)
      (sub_nat_to_imported n) fL).
Proof.
  intro Hf. unfold BcListRel.
  apply coq_eq_to_imported_eq.
  case Hmn: (m <= n)%N.
  - have HmnP : (m <= n)%N by exact Hmn.
    have Hn : m + (n - m) = n by rewrite addnC subnK.
    rewrite -Hn.
    have Hdelta := bc_bigCatNat_delta_related_rel T fR fL
      m (n - m) Hf.
    have HdeltaP := imported_eq_to_coq_eq _ _ Hdelta.
    unfold BcListRel, bc_target_bigCat_nat_delta,
      bc_target_bigCat_nat in HdeltaP |- *.
    etransitivity; first exact HdeltaP.
    apply imported_eq_to_coq_eq.
    exact (sub_imported_eq_congr
        (fun upper => ImportedBigcat.Prosa_Util_Notation_bigCat T
          (sub_nat_to_imported m) upper fL) _ _
        (sub_imported_eq_sym _ _
          (sub_add_correspondence m (sub_nat_to_imported m)
            (n - m) (sub_nat_to_imported (n - m))
            (sub_nat_rel_canonical m) (sub_nat_rel_canonical (n - m))))).
  - have Hlt : (n < m)%N by rewrite ltnNge Hmn.
    have Hnm : (n <= m)%N := ltnW Hlt.
    rewrite big_geq //.
    have HleL := prop_to_sprop _ _
      (sub_nat_le_correspondence n (sub_nat_to_imported n)
        m (sub_nat_to_imported m)
        (sub_nat_rel_canonical n) (sub_nat_rel_canonical m)) Hnm.
    unfold bc_target_bigCat_nat.
    apply imported_eq_to_coq_eq.
    exact (sub_imported_eq_sym _ _
      (ImportedBigcat.Prosa_Validation_BigcatInterface_production_bigCat_of_le
        T (sub_nat_to_imported m) (sub_nat_to_imported n) fL HleL)).
Qed.

Lemma bc_bigCatNat_related (T : Type) (f : nat -> seq T)
    (m n : nat) :
  BcListRel (\cat_(m <= i < n) f i)
    (bc_target_bigCat_nat (sub_nat_to_imported m)
      (sub_nat_to_imported n) (bc_nat_family_to_imported f)).
Proof.
  exact (bc_bigCatNat_related_rel T f (bc_nat_family_to_imported f)
    m n (bc_nat_family_canonical T f)).
Qed.

Lemma bc_bigCatNat_related_any (T : Type)
    (fR : nat -> seq T) (fL : Lean.Nat -> ImportedBigcat.List T)
    (mR nR : nat) (mL nL : Lean.Nat) :
  BcNatFamilyRel fR fL -> SubNatRel mR mL -> SubNatRel nR nL ->
  BcListRel (\cat_(mR <= i < nR) fR i)
    (bc_target_bigCat_nat mL nL fL).
Proof.
  intros Hf Hm Hn. unfold BcListRel.
  exact (sub_imported_eq_trans _ _ _
    (bc_bigCatNat_related_rel T fR fL mR nR Hf)
    (sub_imported_eq_congr2
      (fun m n => bc_target_bigCat_nat m n fL) _ _ _ _ Hm Hn)).
Qed.

(** Artifact-local half-open interval sum.  This realizes the normalized
    [size_big_nat] target without importing the Lean theorem proof graph. *)
Definition bc_target_one : Lean.Nat :=
  ImportedBigcat.OfNat_ofNat_inst1 Lean.Nat (Lean.Nat_succ Lean.Nat_zero)
    (ImportedBigcat.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition bc_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedBigcat.Nat_sub a b.

Lemma bc_target_sub_succ_prop (a b : Lean.Nat) :
  Logic.eq (bc_target_sub a (Lean.Nat_succ b))
    (ImportedBigcat.Nat_pred (bc_target_sub a b)).
Proof. reflexivity. Qed.

Lemma bc_target_zero_sub_prop (b : nat) :
  Logic.eq (bc_target_sub Lean.Nat_zero (sub_nat_to_imported b))
    Lean.Nat_zero.
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rw bc_target_sub_succ_prop IH. reflexivity.
Qed.

Lemma bc_target_succ_sub_succ_prop (a b : nat) :
  Logic.eq
    (bc_target_sub (Lean.Nat_succ (sub_nat_to_imported a))
      (Lean.Nat_succ (sub_nat_to_imported b)))
    (bc_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rw !bc_target_sub_succ_prop. exact (f_equal ImportedBigcat.Nat_pred IH).
Qed.

Lemma bc_target_sub_canonical_prop (a b : nat) :
  Logic.eq
    (bc_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  induction b as [|b IH] in a |- *.
  - destruct a; reflexivity.
  - destruct a as [|a].
    + exact (bc_target_zero_sub_prop b.+1).
    + rw bc_target_succ_sub_succ_prop. exact (IH a).
Qed.

Lemma bc_target_range_succ_prop (start len step : Lean.Nat) :
  Logic.eq
    (ImportedBigcat.List_range' start (Lean.Nat_succ len) step)
    (ImportedBigcat.List_cons_inst1 Lean.Nat start
      (ImportedBigcat.List_range' (Lean.Nat_add start step) len step)).
Proof. reflexivity. Qed.

Lemma bc_target_map_cons_prop {A B : Type} (f : A -> B) (x : A)
    (xs : ImportedBigcat.List_inst1 A) :
  Logic.eq
    (ImportedBigcat.List_map_inst3 A B f
      (ImportedBigcat.List_cons_inst1 A x xs))
    (ImportedBigcat.List_cons_inst1 B (f x)
      (ImportedBigcat.List_map_inst3 A B f xs)).
Proof. reflexivity. Qed.

Lemma bc_target_foldr_cons_prop {A B : Type} (f : A -> B -> B)
    (z : B) (x : A) (xs : ImportedBigcat.List_inst1 A) :
  Logic.eq
    (ImportedBigcat.List_foldr_inst3 A B f z
      (ImportedBigcat.List_cons_inst1 A x xs))
    (f x (ImportedBigcat.List_foldr_inst3 A B f z xs)).
Proof. reflexivity. Qed.

Fixpoint bc_nat_seq_to_imported (xs : seq nat) :
    ImportedBigcat.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedBigcat.List_nil_inst1 Lean.Nat
  | x :: xs' => ImportedBigcat.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported x) (bc_nat_seq_to_imported xs')
  end.

Lemma bc_target_range_iota_prop (start len : nat) :
  Logic.eq
    (ImportedBigcat.List_range'
      (sub_nat_to_imported start) (sub_nat_to_imported len) bc_target_one)
    (bc_nat_seq_to_imported (iota start len)).
Proof.
  elim: len start => [|len IH] start.
  - reflexivity.
  - cbn [sub_nat_to_imported iota bc_nat_seq_to_imported].
    rw bc_target_range_succ_prop.
    have Hstart : Logic.eq
        (Lean.Nat_add (sub_nat_to_imported start) bc_target_one)
        (sub_nat_to_imported start.+1) by reflexivity.
    rw Hstart (IH start.+1). reflexivity.
Qed.

Definition BcNatFunRel (fR : nat -> nat)
    (fL : Lean.Nat -> Lean.Nat) : SProp := SubNatFunRel fR fL.

Lemma bc_target_map_nat_related
    (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat)
    (HF : BcNatFunRel FR FL) (xs : seq nat) :
  Lean.eq (bc_nat_seq_to_imported (map FR xs))
    (ImportedBigcat.List_map_inst3 Lean.Nat Lean.Nat FL
      (bc_nat_seq_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - cbn [bc_nat_seq_to_imported map].
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr2 (ImportedBigcat.List_cons_inst1 Lean.Nat)
        _ _ _ _
        (HF x (sub_nat_to_imported x) (sub_nat_rel_canonical x)) IH)
      (sub_imported_eq_sym _ _
        (coq_eq_to_imported_eq _ _
          (bc_target_map_cons_prop FL (sub_nat_to_imported x)
            (bc_nat_seq_to_imported xs))))).
Qed.

Definition bc_target_list_sum
    (xs : ImportedBigcat.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedBigcat.List_foldr_inst3 Lean.Nat Lean.Nat
    Lean.Nat_add Lean.Nat_zero xs.

Lemma bc_target_list_sum_converted_prop (xs : seq nat) :
  Logic.eq (bc_target_list_sum (bc_nat_seq_to_imported xs))
    (sub_nat_to_imported (foldr addn O xs)).
Proof.
  induction xs as [|x xs IH].
  - reflexivity.
  - cbn [bc_nat_seq_to_imported foldr].
    unfold bc_target_list_sum in IH |- *.
    rw bc_target_foldr_cons_prop IH.
    exact (imported_eq_to_coq_eq _ _
      (sub_imported_eq_sym _ _
        (sub_add_correspondence x (sub_nat_to_imported x)
          (foldr addn O xs) (sub_nat_to_imported (foldr addn O xs))
          (sub_nat_rel_canonical x)
          (sub_nat_rel_canonical (foldr addn O xs))))).
Qed.

Lemma bc_mathcomp_big_seq_as_fold (xs : seq nat) (F : nat -> nat) :
  Logic.eq (\sum_(i <- xs) F i) (foldr addn O (map F xs)).
Proof.
  elim: xs => [|x xs IH].
  - rw big_nil. reflexivity.
  - rw big_cons. cbn [map foldr]. now rw IH.
Qed.

Definition bc_target_interval_sum
    (m n : Lean.Nat) (F : Lean.Nat -> Lean.Nat) : Lean.Nat :=
  bc_target_list_sum
    (ImportedBigcat.List_map_inst3 Lean.Nat Lean.Nat F
      (ImportedBigcat.List_range' m (bc_target_sub n m) bc_target_one)).

Lemma bc_interval_sum_related
    (m n : nat) (F : nat -> nat) (FL : Lean.Nat -> Lean.Nat) :
  BcNatFunRel F FL ->
  SubNatRel (\sum_(m <= i < n) F i)
    (bc_target_interval_sum (sub_nat_to_imported m)
      (sub_nat_to_imported n) FL).
Proof.
  intro HF. unfold bc_target_interval_sum.
  unfold SubNatRel. apply coq_eq_to_imported_eq.
  rw bc_target_sub_canonical_prop bc_target_range_iota_prop.
  have Hmap := bc_target_map_nat_related F FL HF (iota m (n - m)).
  have HmapP := imported_eq_to_coq_eq _ _ Hmap.
  rewrite -HmapP.
  rw bc_target_list_sum_converted_prop.
  rw /index_iota bc_mathcomp_big_seq_as_fold.
  reflexivity.
Qed.

Lemma bc_nat_length_family_related (T : Type) (F : nat -> seq T) :
  BcNatFunRel (fun i => size (F i))
    (fun i => bc_target_length (bc_nat_family_to_imported F i)).
Proof.
  intros iR iL Hi. exact (bc_length_related T (F iR)
    (bc_nat_family_to_imported F iL)
    (bc_nat_family_canonical T F iR iL Hi)).
Qed.

(** MathComp ordinal / imported Lean [Fin] boundary and canonical finite
    enumeration used by [bigCatFin]. *)
Definition bc_target_fin_zero (n : Lean.Nat) :
    Fin (Lean.Nat_add n bc_target_one) :=
  ImportedBigcat.OfNat_ofNat_inst1
    (Fin (Lean.Nat_add n bc_target_one)) Lean.Nat_zero
    (ImportedBigcat.Fin_instOfNat
      (Lean.Nat_add n bc_target_one)
      (ImportedBigcat.instNeZeroNatHAdd_1 n bc_target_one
        (ImportedBigcat.Nat_instNeZeroSucc Lean.Nat_zero))
      Lean.Nat_zero).

Definition bc_target_fin_succ (n : Lean.Nat)
    (i : Fin n) :
    Fin (Lean.Nat_add n bc_target_one) :=
  ImportedBigcat.Fin_succ n i.

Definition BcOrdRel (n : nat) (iR : 'I_n)
    (iL : Fin (sub_nat_to_imported n)) : SProp :=
  SubNatRel (nat_of_ord iR)
    (ImportedBigcat.Fin_val (sub_nat_to_imported n) iL).

Definition bc_ord_to_fin (n : nat) (i : 'I_n) :
    Fin (sub_nat_to_imported n).
Proof.
  refine (Fin_mk (sub_nat_to_imported n)
    (sub_nat_to_imported (nat_of_ord i)) _).
  exact (prop_to_sprop _ _
    (bc_nat_lt_correspondence (nat_of_ord i)
      (sub_nat_to_imported (nat_of_ord i)) n (sub_nat_to_imported n)
      (sub_nat_rel_canonical (nat_of_ord i)) (sub_nat_rel_canonical n))
    (ltn_ord i)).
Defined.

Lemma bc_ord_rel_canonical (n : nat) (i : 'I_n) :
  BcOrdRel n i (bc_ord_to_fin n i).
Proof. exact (@Lean.eq_refl _ _). Qed.

Definition bc_fin_to_ord (n : nat)
    (i : Fin (sub_nat_to_imported n)) : 'I_n.
Proof.
  refine (@Ordinal n
    (sub_nat_to_rocq
      (ImportedBigcat.Fin_val (sub_nat_to_imported n) i)) _).
  exact (sprop_to_prop _ _
    (bc_nat_lt_correspondence
      (sub_nat_to_rocq
        (ImportedBigcat.Fin_val (sub_nat_to_imported n) i))
      (ImportedBigcat.Fin_val (sub_nat_to_imported n) i)
      n (sub_nat_to_imported n)
      (sub_nat_rel_surjective
        (ImportedBigcat.Fin_val (sub_nat_to_imported n) i))
      (sub_nat_rel_canonical n))
    (ImportedBigcat.Fin_isLt (sub_nat_to_imported n) i)).
Defined.

Definition bc_ord_family_to_imported {T : Type} (n : nat)
    (f : 'I_n -> seq T) :
    Fin (sub_nat_to_imported n) -> ImportedBigcat.List T :=
  fun i => bc_to_imported (f (bc_fin_to_ord n i)).

Definition BcOrdFamilyRel {T : Type} (n : nat)
    (fR : 'I_n -> seq T)
    (fL : Fin (sub_nat_to_imported n) ->
      ImportedBigcat.List T) : SProp :=
  forall iR iL, BcOrdRel n iR iL -> BcListRel (fR iR) (fL iL).

Lemma bc_ord_family_canonical (T : Type) (n : nat)
    (f : 'I_n -> seq T) :
  BcOrdFamilyRel n f (bc_ord_family_to_imported n f).
Proof.
  intros iR iL Hi. unfold BcListRel, bc_ord_family_to_imported.
  apply coq_eq_to_imported_eq. apply f_equal. apply f_equal. apply val_inj.
  unfold BcOrdRel, SubNatRel in Hi. cbn.
  have HiP := imported_eq_to_coq_eq _ _ Hi.
  have Hdecoded := f_equal sub_nat_to_rocq HiP.
  rewrite (sub_nat_rocq_roundtrip (nat_of_ord iR)) in Hdecoded.
  exact Hdecoded.
Qed.

Definition bc_target_bigCatFin {T : Type} (n : Lean.Nat)
    (f : Fin n -> ImportedBigcat.List T) :
    ImportedBigcat.List T :=
  ImportedBigcat.Prosa_Util_Bigcat_bigCatFin T n f.

Lemma bc_bigCatFin_succ_step (T : Type) (n : nat)
    (fR : 'I_n.+1 -> seq T)
    (fL : Fin (sub_nat_to_imported n.+1) -> ImportedBigcat.List T) :
  BcListRel (fR ord0)
      (fL (bc_target_fin_zero (sub_nat_to_imported n))) ->
  BcListRel (\cat_(i < n) fR (lift ord0 i))
      (bc_target_bigCatFin (sub_nat_to_imported n)
        (fun i => fL (bc_target_fin_succ (sub_nat_to_imported n) i))) ->
  BcListRel
    (fR ord0 ++ \cat_(i < n) fR (lift ord0 i))
    (bc_target_bigCatFin (sub_nat_to_imported n.+1) fL).
Proof.
  intros Hhead Htail.
  have Happ := bc_append_related T
    (fR ord0) (\cat_(i < n) fR (lift ord0 i))
    (fL (bc_target_fin_zero (sub_nat_to_imported n)))
    (bc_target_bigCatFin (sub_nat_to_imported n)
      (fun i => fL (bc_target_fin_succ (sub_nat_to_imported n) i)))
    Hhead Htail.
  unfold BcListRel, bc_target_bigCatFin in Happ |- *.
  exact (sub_imported_eq_trans _ _ _ Happ
    (sub_imported_eq_sym _ _
      (ImportedBigcat.Prosa_Validation_BigcatInterface_production_bigCatFin_succ
        T (sub_nat_to_imported n) fL))).
Qed.

Lemma bc_bigCatFin_related_rel (T : Type) (n : nat)
    (fR : 'I_n -> seq T)
    (fL : Fin (sub_nat_to_imported n) -> ImportedBigcat.List T) :
  BcOrdFamilyRel n fR fL ->
  BcListRel (\cat_(i < n) fR i)
    (bc_target_bigCatFin (sub_nat_to_imported n) fL).
Proof.
  induction n as [|n IH].
  - intro Hf. rewrite big_ord0.
    unfold BcListRel, bc_target_bigCatFin.
    exact (sub_imported_eq_sym _ _
      (ImportedBigcat.Prosa_Validation_BigcatInterface_production_bigCatFin_zero
        T fL)).
  - intro Hf. rewrite big_ord_recl.
    exact (bc_bigCatFin_succ_step T n fR fL
      (Hf ord0 (bc_target_fin_zero (sub_nat_to_imported n))
        (@Lean.eq_refl _ _))
      (IH (fun i => fR (lift ord0 i))
        (fun i => fL (bc_target_fin_succ (sub_nat_to_imported n) i))
        (fun iR iL Hi => Hf (lift ord0 iR)
          (bc_target_fin_succ (sub_nat_to_imported n) iL)
          (sub_imported_eq_congr Lean.Nat_succ _ _ Hi)))).
Qed.

Lemma bc_bigCatFin_related (T : Type) (n : nat)
    (f : 'I_n -> seq T) :
  BcListRel (\cat_(i < n) f i)
    (bc_target_bigCatFin (sub_nat_to_imported n)
      (bc_ord_family_to_imported n f)).
Proof.
  exact (bc_bigCatFin_related_rel T n f (bc_ord_family_to_imported n f)
    (bc_ord_family_canonical T n f)).
Qed.

Lemma bc_and_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P /\ Q) (And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p q]. exact (And_intro PL QL
      (prop_to_sprop _ _ HP p) (prop_to_sprop _ _ HQ q)).
  - intros [p q]. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ HP p).
    + exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma bc_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. apply (prop_to_sprop _ _ HQ).
    exact (H (sprop_to_prop _ _ HP p)).
  - intro H. apply strictly_inhabits. intro p.
    apply (sprop_to_prop _ _ HQ).
    exact (H (prop_to_sprop _ _ HP p)).
Qed.

Lemma bc_forall_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (HP x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _ (HP x) (HL x)).
Qed.

Lemma bc_exists_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (ImportedBigcat.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (ImportedBigcat.Exists_intro T PL x
      (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x.
    exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma bc_forall_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL ->
    PropSPropRel (PR nR) (PL nL)) ->
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

Lemma bc_exists_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL ->
    PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (exists nR, PR nR) (ImportedBigcat.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [nR Hn]. exact (ImportedBigcat.Exists_intro Lean.Nat PL
      (sub_nat_to_imported nR)
      (prop_to_sprop _ _
        (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) Hn)).
  - intros [nL Hn]. apply strictly_inhabits.
    exists (sub_nat_to_rocq nL).
    exact (sprop_to_prop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL)) Hn).
Qed.

Print Assumptions bc_membership_correspondence.
Print Assumptions bc_decide_mem_related.
Print Assumptions bc_filter_related.
Print Assumptions bc_flatMap_related.
Print Assumptions bc_bigCatSeqAll_related.
Print Assumptions bc_bigCatSeq_related.
Print Assumptions bc_uniq_correspondence.
Print Assumptions bc_length_related.
Print Assumptions bc_bigCatNat_related.
