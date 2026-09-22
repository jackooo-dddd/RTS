From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop ssrfun.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBigop.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Artifact-local realization of the already approved Bool, eqType and
    seq/List representation relations for [ImportedBigop].  The mathematical
    relations are reused; these adapters are necessarily artifact-local
    because rocq-lean-import seals each export in its own module. *)

Definition bo_false_to_strict (H : ImportedBigop.False) :
    StrictlyInhabited Logic.False := match H with end.

Definition bo_false_elim (Q : SProp) (H : ImportedBigop.False) : Q :=
  match H return Q with end.

Definition bo_coq_false_to_target (H : Logic.False) :
    ImportedBigop.False := match H return ImportedBigop.False with end.

Definition bo_bool_to_imported (b : bool) : ImportedBigop.Bool :=
  match b with
  | true => ImportedBigop.Bool_true
  | false => ImportedBigop.Bool_false
  end.

Definition bo_bool_to_rocq (b : ImportedBigop.Bool) : bool :=
  match b with
  | ImportedBigop.Bool_true => true
  | ImportedBigop.Bool_false => false
  end.

Definition BoBoolRel (bR : bool) (bL : ImportedBigop.Bool) : SProp :=
  Lean.eq (bo_bool_to_imported bR) bL.

Lemma bo_bool_source_roundtrip (b : bool) :
  Logic.eq (bo_bool_to_rocq (bo_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma bo_bool_target_roundtrip (b : ImportedBigop.Bool) :
  Lean.eq (bo_bool_to_imported (bo_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma bo_bool_eq_correspondence bR bL cR cL :
  BoBoolRel bR bL -> BoBoolRel cR cL ->
  PropSPropRel (Logic.eq bR cR) (Lean.eq bL cL).
Proof.
  intros Hb Hc. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Hb) Hc).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (bo_bool_to_imported bR)
        (bo_bool_to_imported cR) :=
      sub_imported_eq_trans _ _ _ Hb
        (sub_imported_eq_trans _ _ _ Heq (sub_imported_eq_sym _ _ Hc)).
    have Hdecoded := f_equal bo_bool_to_rocq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (bo_bool_source_roundtrip bR) in Hdecoded.
    rewrite (bo_bool_source_roundtrip cR) in Hdecoded.
    exact Hdecoded.
Qed.

Fixpoint bo_to_imported {T : Type} (xs : seq T) : ImportedBigop.List T :=
  match xs with
  | [::] => ImportedBigop.List_nil T
  | x :: xs' => ImportedBigop.List_cons T x (bo_to_imported xs')
  end.

Fixpoint bo_to_rocq {T : Type} (xs : ImportedBigop.List T) : seq T :=
  match xs with
  | ImportedBigop.List_nil => [::]
  | ImportedBigop.List_cons x xs' => x :: bo_to_rocq xs'
  end.

Definition BoListRel {T : Type} (xsR : seq T)
    (xsL : ImportedBigop.List T) : SProp :=
  Lean.eq (bo_to_imported xsR) xsL.

Lemma bo_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (bo_to_rocq (bo_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma bo_list_target_roundtrip {T : Type} (xs : ImportedBigop.List T) :
  Lean.eq (bo_to_imported (bo_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ (ImportedBigop.List_nil T)).
  - exact (sub_imported_eq_congr
      (ImportedBigop.List_cons T x) _ _ IH).
Qed.

Definition bo_decidable_eq (T : eqType) : ImportedBigop.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedBigop.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedBigop.Decidable_isFalse (Lean.eq x y)
        (fun HL => bo_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Definition bo_target_mem {T : Type} (x : T)
    (xs : ImportedBigop.List T) : SProp :=
  ImportedBigop.Membership_mem T (ImportedBigop.List T)
    (ImportedBigop.List_instMembership T) xs x.

Definition bo_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedBigop.List T) :
    Lean.eq xs ys -> ImportedBigop.List_Mem T x xs ->
    ImportedBigop.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedBigop.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition bo_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedBigop.List T) : Logic.eq x y ->
    ImportedBigop.List_Mem T x (ImportedBigop.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedBigop.List_Mem T x (ImportedBigop.List_cons T z xs) with
    | Logic.eq_refl => ImportedBigop.List_Mem_head T x xs
    end.

Inductive BoTruth : SProp := bo_truth_intro.
Inductive BoFalse : SProp := .

Definition BoBoolTruth (b : bool) : SProp :=
  match b with true => BoTruth | false => BoFalse end.

Definition bo_truth_false_elim (Q : SProp) (H : BoBoolTruth false) : Q :=
  match H return Q with end.

Definition bo_prop_to_truth (b : bool) : is_true b -> BoBoolTruth b :=
  match b return is_true b -> BoBoolTruth b with
  | true => fun _ => bo_truth_intro
  | false => fun H =>
      match H in Logic.eq _ z return
        match z with true => BoFalse | false => BoTruth end
      with Logic.eq_refl => bo_truth_intro end
  end.

Definition bo_truth_to_strict_prop (b : bool) :
    BoBoolTruth b -> StrictlyInhabited (is_true b) :=
  match b return BoBoolTruth b -> StrictlyInhabited (is_true b) with
  | true => fun _ => strictly_inhabits (Logic.eq_refl true)
  | false => fun H => match H with end
  end.

Definition bo_or_left_truth (a b : bool) :
    BoBoolTruth a -> BoBoolTruth (a || b) :=
  match a, b return BoBoolTruth a -> BoBoolTruth (a || b) with
  | true, _ => fun _ => bo_truth_intro
  | false, true => fun _ => bo_truth_intro
  | false, false => fun H => H
  end.

Definition bo_or_right_truth (a b : bool) :
    BoBoolTruth b -> BoBoolTruth (a || b) :=
  match a, b return BoBoolTruth b -> BoBoolTruth (a || b) with
  | true, _ => fun _ => bo_truth_intro
  | false, true => fun _ => bo_truth_intro
  | false, false => fun H => H
  end.

Definition bo_eq_refl_truth (T : eqType) (x : T) : BoBoolTruth (x == x).
Proof. rewrite eqxx. exact bo_truth_intro. Defined.

Fixpoint bo_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    BoBoolTruth (x \in xs) -> ImportedBigop.List_Mem T x (bo_to_imported xs) :=
  match xs as xs0 return BoBoolTruth (x \in xs0) ->
      ImportedBigop.List_Mem T x (bo_to_imported xs0) with
  | [::] => bo_truth_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        BoBoolTruth (b || (x \in ys)) ->
        ImportedBigop.List_Mem T x
          (ImportedBigop.List_cons T y (bo_to_imported ys)) with
      | ReflectT Hxy => fun _ => bo_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedBigop.List_Mem_tail T x y _
          (bo_seq_mem_forward x ys H)
      end
  end.

Fixpoint bo_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedBigop.List T) (H : ImportedBigop.List_Mem T x xs) :
    BoBoolTruth (x \in bo_to_rocq xs) :=
  match H with
  | ImportedBigop.List_Mem_head ys => bo_or_left_truth _ _ (bo_eq_refl_truth T x)
  | ImportedBigop.List_Mem_tail y ys Htail =>
      bo_or_right_truth _ _ (bo_imported_mem_decoded x ys Htail)
  end.

Definition bo_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    BoBoolTruth (x \in xs) -> BoBoolTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return BoBoolTruth (x \in zs) with
    | Logic.eq_refl => Htruth
    end.

Definition bo_imported_mem_backward {T : eqType} (x : T) (xs : seq T)
    (H : ImportedBigop.List_Mem T x (bo_to_imported xs)) :
    BoBoolTruth (x \in xs) :=
  bo_mem_truth_transport x _ _ (bo_list_source_roundtrip xs)
    (bo_imported_mem_decoded x (bo_to_imported xs) H).

Lemma bo_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedBigop.List T) :
  BoListRel xsR xsL -> PropSPropRel (x \in xsR) (bo_target_mem x xsL).
Proof.
  intro Hlist. apply prop_sprop_rel_intro.
  - intro Hmem. unfold bo_target_mem.
    apply (bo_list_mem_transport x _ _ Hlist).
    apply bo_seq_mem_forward. exact (bo_prop_to_truth _ Hmem).
  - intro Hmem. apply bo_truth_to_strict_prop.
    apply bo_imported_mem_backward. unfold bo_target_mem in Hmem.
    exact (bo_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hlist) Hmem).
Qed.

Definition BoPredRel {T : Type} (PR : T -> bool)
    (PL : T -> ImportedBigop.Bool) : SProp :=
  forall x, BoBoolRel (PR x) (PL x).

Definition bo_pred_to_imported {T : Type} (PR : T -> bool) :
    T -> ImportedBigop.Bool := fun x => bo_bool_to_imported (PR x).

Definition bo_pred_to_rocq {T : Type} (PL : T -> ImportedBigop.Bool) :
    T -> bool := fun x => bo_bool_to_rocq (PL x).

Lemma bo_pred_canonical {T : Type} (PR : T -> bool) :
  BoPredRel PR (bo_pred_to_imported PR).
Proof. intro x. exact (@Lean.eq_refl _ _). Qed.

Lemma bo_pred_surjective {T : Type} (PL : T -> ImportedBigop.Bool) :
  BoPredRel (bo_pred_to_rocq PL) PL.
Proof. intro x. exact (bo_bool_target_roundtrip (PL x)). Qed.

Definition bo_target_decide_eq (T : eqType) (x y : T) : ImportedBigop.Bool :=
  ImportedBigop.Decidable_decide (Lean.eq x y) (bo_decidable_eq T x y).

Lemma bo_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedBigop.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  BoBoolRel b (ImportedBigop.Decidable_decide Q d).
Proof.
  intro Hrel. unfold BoBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (bo_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (bo_false_elim _ (bo_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Lemma bo_decide_eq_related (T : eqType) (x y : T) :
  BoBoolRel (x == y) (bo_target_decide_eq T x y).
Proof.
  apply bo_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - intro Hxy. move/eqP: Hxy => Hxy.
    exact (coq_eq_to_imported_eq x y Hxy).
  - intro Hxy. apply strictly_inhabits. apply/eqP.
    exact (imported_eq_to_coq_eq x y Hxy).
Qed.

(** [uniq] / imported [List.Nodup]. *)
Definition bo_nodup_transport {T : Type} (xs ys : ImportedBigop.List T) :
    Lean.eq xs ys -> ImportedBigop.List_Nodup T xs ->
    ImportedBigop.List_Nodup T ys :=
  fun Hxy H =>
    match Hxy in Lean.eq _ zs return ImportedBigop.List_Nodup T zs with
    | Lean.eq_refl => H
    end.

Definition bo_and_left_truth (a b : bool) :
    BoBoolTruth (a && b) -> BoBoolTruth a :=
  match a, b return BoBoolTruth (a && b) -> BoBoolTruth a with
  | true, _ => fun _ => bo_truth_intro
  | false, _ => fun H => H
  end.

Definition bo_and_right_truth (a b : bool) :
    BoBoolTruth (a && b) -> BoBoolTruth b :=
  match a, b return BoBoolTruth (a && b) -> BoBoolTruth b with
  | true, true => fun _ => bo_truth_intro
  | true, false => fun H => H
  | false, true => fun _ => bo_truth_intro
  | false, false => fun H => H
  end.

Definition bo_neg_mem_contra (b : bool) :
    BoBoolTruth (~~ b) -> BoBoolTruth b -> ImportedBigop.False :=
  match b return BoBoolTruth (~~ b) -> BoBoolTruth b -> ImportedBigop.False with
  | true => fun H _ => match H with end
  | false => fun _ H => match H with end
  end.

Fixpoint bo_uniq_truth_forward (T : eqType) (xs : seq T) :
    BoBoolTruth (uniq xs) -> ImportedBigop.List_Nodup T (bo_to_imported xs).
Proof.
  destruct xs as [|x xs].
  - intro Hnil. exact (ImportedBigop.List_Pairwise_nil T (ImportedBigop.Ne T)).
  - intro Huniq. apply ImportedBigop.List_Pairwise_cons.
    + intros y Hy Hxy.
      have HyR := sprop_to_prop _ _
        (bo_membership_correspondence T y xs (bo_to_imported xs)
          (@Lean.eq_refl _ _)) Hy.
      have Hcoq : Logic.eq x y := imported_eq_to_coq_eq x y Hxy.
      subst y.
      exact (bo_neg_mem_contra (x \in xs)
        (bo_and_left_truth _ _ Huniq) (bo_prop_to_truth _ HyR)).
    + exact (bo_uniq_truth_forward T xs (bo_and_right_truth _ _ Huniq)).
Defined.

Definition bo_uniq_forward (T : eqType) (xs : seq T) :
    uniq xs -> ImportedBigop.List_Nodup T (bo_to_imported xs) :=
  fun H => bo_uniq_truth_forward T xs (bo_prop_to_truth _ H).

Definition bo_strict_uniq_transport (T : eqType) (xs ys : seq T) :
    Logic.eq xs ys -> StrictlyInhabited (uniq xs) ->
    StrictlyInhabited (uniq ys) :=
  fun H Huniq =>
    match H in Logic.eq _ zs return StrictlyInhabited (uniq zs) with
    | Logic.eq_refl => Huniq
    end.

Lemma bo_imported_nodup_backward (T : eqType) (xs : ImportedBigop.List T) :
  ImportedBigop.List_Nodup T xs -> StrictlyInhabited (uniq (bo_to_rocq xs)).
Proof.
  intro Hnodup. induction Hnodup as [|y ys Hhead Htail IH].
  - exact (strictly_inhabits (Logic.eq_refl true)).
  - destruct IH as [IHuniq]. apply strictly_inhabits.
    apply/andP. split; last exact IHuniq.
    apply/negP. intro Hmem.
    have HmemL := prop_to_sprop _ _
      (bo_membership_correspondence T y (bo_to_rocq ys) ys
        (bo_list_target_roundtrip ys)) Hmem.
    have Hneq := Hhead y HmemL.
    exact (interpret_strict Logic.False
      (bo_false_to_strict (Hneq (@Lean.eq_refl T y)))).
Qed.

Lemma bo_uniq_correspondence (T : eqType)
    (xsR : seq T) (xsL : ImportedBigop.List T) :
  BoListRel xsR xsL ->
  PropSPropRel (uniq xsR) (ImportedBigop.List_Nodup T xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Huniq. exact (bo_nodup_transport _ _ Hxs
      (bo_uniq_forward T xsR Huniq)).
  - intro Hnodup.
    have Hcanonical := bo_nodup_transport _ _
      (sub_imported_eq_sym _ _ Hxs) Hnodup.
    have Hstrict := bo_imported_nodup_backward T (bo_to_imported xsR) Hcanonical.
    exact (bo_strict_uniq_transport T _ _ (bo_list_source_roundtrip xsR) Hstrict).
Qed.

(** Exact source-shape recursion, used only to expose the MathComp bigop
    computation before relating it to the imported Lean body. *)
Fixpoint bo_source_bigSeq {R X : Type} (idx : R) (op : R -> R -> R)
    (P : X -> bool) (F : X -> R) (xs : seq X) : R :=
  match xs with
  | [::] => idx
  | x :: xs' => if P x then op (F x) (bo_source_bigSeq idx op P F xs')
                else bo_source_bigSeq idx op P F xs'
  end.

Lemma bo_source_bigSeq_is_bigop (R : Type) (idx : R)
    (op : Monoid.law idx) (X : eqType) (P : pred X)
    (F : X -> R) (xs : seq X) :
  Logic.eq (bo_source_bigSeq idx op P F xs)
    (\big[op/idx]_(j <- xs | P j) F j).
Proof.
  induction xs as [|x xs IH].
  - by rewrite big_nil.
  - rewrite big_cons. cbn. case: (P x); cbn; first by rewrite IH.
    exact IH.
Qed.

Definition bo_target_bigSeq (R X : Type) (idx : R) (op : R -> R -> R)
    (P : X -> ImportedBigop.Bool) (F : X -> R)
    (xs : ImportedBigop.List X) : R :=
  ImportedBigop.Prosa_Util_Bigop_bigSeq R X idx op P F xs.

Lemma bo_bigSeq_canonical_related (R : Type) (idx : R)
    (op : R -> R -> R) (X : Type) (PR : X -> bool)
    (PL : X -> ImportedBigop.Bool) (F : X -> R) (xs : seq X) :
  BoPredRel PR PL ->
  Lean.eq (bo_source_bigSeq idx op PR F xs)
    (bo_target_bigSeq R X idx op PL F (bo_to_imported xs)).
Proof.
  intro HP. induction xs as [|x xs IH].
  - exact (sub_imported_eq_sym _ _
      (ImportedBigop.Prosa_Validation_BigopInterface_production_bigSeq_nil
        R X idx op PL F)).
  - have Heq :=
      ImportedBigop.Prosa_Validation_BigopInterface_production_bigSeq_cons
        R X idx op PL F x (bo_to_imported xs).
    have HeqC := imported_eq_to_coq_eq _ _ Heq.
    unfold bo_target_bigSeq in IH |- *.
    rewrite HeqC.
    cbn [bo_source_bigSeq].
    have HPxC := imported_eq_to_coq_eq _ _ (HP x).
    destruct (PR x) eqn:HPR; cbn in HPxC.
    + rewrite <- HPxC. cbn.
      exact (sub_imported_eq_congr (op (F x)) _ _ IH).
    + rewrite <- HPxC. cbn. exact IH.
Qed.

Lemma bo_bigSeq_related (R : Type) (idx : R) (op : R -> R -> R)
    (X : Type) (PR : X -> bool) (PL : X -> ImportedBigop.Bool)
    (F : X -> R) (xsR : seq X) (xsL : ImportedBigop.List X) :
  BoPredRel PR PL -> BoListRel xsR xsL ->
  Lean.eq (bo_source_bigSeq idx op PR F xsR)
    (bo_target_bigSeq R X idx op PL F xsL).
Proof.
  intros HP Hxs.
  exact (sub_imported_eq_trans _ _ _
    (bo_bigSeq_canonical_related R idx op X PR PL F xsR HP)
    (sub_imported_eq_congr (bo_target_bigSeq R X idx op PL F) _ _ Hxs)).
Qed.

Lemma bo_bigop_related (R : Type) (idx : R) (op : Monoid.law idx)
    (X : eqType) (PR : X -> bool) (PL : X -> ImportedBigop.Bool)
    (F : X -> R) (xsR : seq X) (xsL : ImportedBigop.List X) :
  BoPredRel PR PL -> BoListRel xsR xsL ->
  Lean.eq (\big[op/idx]_(j <- xsR | PR j) F j)
    (bo_target_bigSeq R X idx op PL F xsL).
Proof.
  intros HP Hxs.
  exact (sub_imported_eq_trans _ _ _
    (coq_eq_to_imported_eq _ _
      (Logic.eq_sym (bo_source_bigSeq_is_bigop R idx op X PR F xsR)))
    (bo_bigSeq_related R idx op X PR PL F xsR xsL HP Hxs)).
Qed.

(** The exact source monoid laws transported to the imported target equality. *)
Definition bo_target_assoc (R : Type) (op : R -> R -> R) : SProp :=
  forall x y z, Lean.eq (op x (op y z)) (op (op x y) z).

Definition bo_target_left_id (R : Type) (idx : R)
    (op : R -> R -> R) : SProp :=
  forall x, Lean.eq (op idx x) x.

Definition bo_target_right_id (R : Type) (idx : R)
    (op : R -> R -> R) : SProp :=
  forall x, Lean.eq (op x idx) x.

Definition bo_assoc_from_monoid (R : Type) (idx : R)
    (op : Monoid.law idx) : bo_target_assoc R op :=
  fun x y z => coq_eq_to_imported_eq _ _ (Monoid.mulmA op x y z).

Definition bo_left_id_from_monoid (R : Type) (idx : R)
    (op : Monoid.law idx) : bo_target_left_id R idx op :=
  fun x => coq_eq_to_imported_eq _ _ (Monoid.mul1m op x).

Definition bo_right_id_from_monoid (R : Type) (idx : R)
    (op : Monoid.law idx) : bo_target_right_id R idx op :=
  fun x => coq_eq_to_imported_eq _ _ (Monoid.mulm1 op x).

Print Assumptions bo_membership_correspondence.
Print Assumptions bo_uniq_correspondence.
Print Assumptions bo_bigop_related.
Print Assumptions bo_assoc_from_monoid.
