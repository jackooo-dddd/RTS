From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From prosa Require Import classic.util.find_seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicFindSeq.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicFindSeqBase ClassicFindSeqList.

Module I := ImportedClassicFindSeq.
Local Open Scope nat_scope.

(** Certificates for [classic/util/find_seq.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: elements of an [eqType] identified (its Lean [DecidableEq] the
    eqType's decision procedure); sequences elementwise ([ClListRel]); options
    constructor-wise ([cl_opt]); natural numbers by [SubNatRel]; Boolean
    predicates [T -> bool] pointwise; all with two-way totals.

    [findP P l] against the Lean [findP P L] (structural recursion, unfolded one
    constructor at a time by conversion); MathComp [find p s] against
    [List.findIdx p L] through [findIdx.go] with its accumulator; [has p s]
    against [List.any L p].

    Statements: the source side is the exact elaborated type of the pinned
    lemma (via [type of]; the source proof is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Operations *)

Lemma cfs_opt_eq {A : Type} (o1 o2 : option A) : PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := f_equal cl_unopt (imported_eq_to_coq_eq _ _ E).
    by rewrite !cl_unopt_opt in E'.
Qed.

Lemma cfs_not (P : Prop) (PL : SProp) : PropSPropRel P PL -> PropSPropRel (~ P) (I.Not PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros N HL. exact (ct_coq_false_to_target (N (sprop_to_prop _ _ H HL))).
  - intro N. apply strictly_inhabits. intro p.
    exact (interpret_strict _ (ct_target_false_to_strict (N (prop_to_sprop _ _ H p)))).
Qed.

Lemma cfs_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, (forall a, CtBoolRel (pR a) (pL a)) -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H (fun a => ct_l2b (pL a)) pL (fun a => ct_bool_surjective _)) (HR _)).
  - intro HL. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ (H pR (fun a => ct_b2l (pR a)) (fun a => ct_bool_canonical _)) (HL _)).
Qed.

Theorem findP_correspondence (T : eqType) (pR : T -> bool) (pL : T -> I.Bool)
    (Hp : forall a, CtBoolRel (pR a) (pL a)) (l : seq T) :
  Logic.eq (cl_opt (findP pR l)) (I.Prosa_Classic_Util_FindSeq_findP T (ct_decidable_eq T) pL (cl_map cid l)).
Proof.
  elim: l => [|a l IH] //=.
  have -> : Logic.eq (I.Prosa_Classic_Util_FindSeq_findP T (ct_decidable_eq T) pL (I.List_cons T a (cl_map cid l)))
      (match pL a with
       | I.Bool_true => I.Option_some T a
       | I.Bool_false => I.Prosa_Classic_Util_FindSeq_findP T (ct_decidable_eq T) pL (cl_map cid l) end).
  { cbn. by case: (pL a). }
  rewrite (ct_bool_rel_logic _ _ (Hp a)) -IH. by case: (pR a).
Qed.

Lemma cfs_findIdx_go (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall a, CtBoolRel (pR a) (pL a)) :
  forall (s : seq T) n,
  Logic.eq (I.List_findIdx_go T pL (cl_map cid s) (sub_nat_to_imported n)) (sub_nat_to_imported (n + find pR s)).
Proof.
  elim => [|y s IH] n.
  - by rewrite addn0.
  - have -> : Logic.eq (I.List_findIdx_go T pL (cl_map cid (y :: s)) (sub_nat_to_imported n))
       (match pL y with
        | I.Bool_true => sub_nat_to_imported n
        | I.Bool_false => I.List_findIdx_go T pL (cl_map cid s) (sub_nat_to_imported n.+1) end).
    { cbn. by case: (pL y). }
    rewrite (ct_bool_rel_logic _ _ (Hp y)) /=. case: (pR y) => /=.
    + by rewrite addn0.
    + rewrite (IH n.+1). by rewrite addSnnS.
Qed.

Lemma cfs_find (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall a, CtBoolRel (pR a) (pL a)) s sL :
  ClListRel cid s sL -> SubNatRel (find pR s) (I.List_findIdx T pL sL).
Proof. intro H. destruct H. apply: cl_lean_eq. exact (Logic.eq_sym (cfs_findIdx_go T pR pL Hp s 0)). Qed.

Lemma cfs_any_logic (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall a, CtBoolRel (pR a) (pL a)) s :
  Logic.eq (I.List_any T (cl_map cid s) pL) (ct_b2l (has pR s)).
Proof.
  elim: s => [|a s IH] //=.
  have -> : Logic.eq (I.List_any T (I.List_cons T a (cl_map cid s)) pL)
      (I.Bool_or (pL a) (I.List_any T (cl_map cid s) pL)) by [].
  rewrite (ct_bool_rel_logic _ _ (Hp a)) IH. by case: (pR a).
Qed.

Lemma cfs_any (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall a, CtBoolRel (pR a) (pL a)) s :
  CtBoolRel (has pR s) (I.List_any T (cl_map cid s) pL).
Proof. unfold CtBoolRel. rewrite (cfs_any_logic T pR pL Hp s). exact (@Lean.eq_refl _ _). Qed.

Lemma cfs_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl_forall_list cid cid (fun _ => Logic.eq_refl _) PR PL). Qed.

Lemma cfs_cat (T : Type) s1 s2 L1 L2 : ClListRel (B := T) cid s1 L1 -> ClListRel cid s2 L2 ->
  ClListRel cid (s1 ++ s2)
    (I.HAppend_hAppend (I.List T) (I.List T) (I.List T) (I.instHAppendOfAppend (I.List T) (I.List_instAppend T)) L1 L2).
Proof. intros H1 H2. destruct H1, H2. apply: coq_eq_to_imported_eq. exact (cl_cat cid s1 s2). Qed.

Lemma cfs_eq_pred (T : eqType) (x : T) :
  forall a, CtBoolRel (a == x) (I.Decidable_decide (Lean.eq a x) (ct_decidable_eq T a x)).
Proof. intro a. exact (ct_decide_eq T a x). Qed.

Lemma cfs_ne (T : eqType) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (cfs_not _ _ (ct_eq_rel T x y)). Qed.

Lemma cfs_find_eq (T : eqType) pR pL (Hp : forall a, CtBoolRel (pR a) (pL a)) l (o : option T) :
  PropSPropRel (Logic.eq (findP pR l) o)
    (Lean.eq (I.Prosa_Classic_Util_FindSeq_findP T (ct_decidable_eq T) pL (cl_map cid l)) (cl_opt o)).
Proof. rewrite -(findP_correspondence T pR pL Hp l). exact (cfs_opt_eq _ _). Qed.

Lemma cfs_mem (T : eqType) (x : T) s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cfs_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_findP_FIFO (T : eqType) : Prop := ltac:(type_of_term (@findP_FIFO T)).
Definition tgt_findP_FIFO (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_FindSeq_findP_FIFO T (ct_decidable_eq T))).
Theorem findP_FIFO_correspondence (T : eqType) : PropSPropRel (src_findP_FIFO T) (tgt_findP_FIFO T).
Proof.
  unfold src_findP_FIFO, tgt_findP_FIFO.
  apply: cfs_forall_pred => pR pL Hp. apply: cfs_forall_list => l L H.
  apply: ct_forall_identity => x. apply: ct_forall_identity => y.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hp y)).
  apply: ct_imp; first exact (cfs_mem T y l L H).
  apply: ct_imp; first exact (cfs_ne T x y).
  apply: ct_imp.
  - destruct H. exact (cfs_find_eq T pR pL Hp l (Some x)).
  - exact (sub_nat_lt_correspondence _ _ _ _ (cfs_find T _ _ (cfs_eq_pred T x) l L H)
                                         (cfs_find T _ _ (cfs_eq_pred T y) l L H)).
Qed.

Definition src_find_uniql (T : eqType) : Prop := ltac:(type_of_term (@find_uniql T)).
Definition tgt_find_uniql (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_FindSeq_find_uniql T (ct_decidable_eq T))).
Theorem find_uniql_correspondence (T : eqType) : PropSPropRel (src_find_uniql T) (tgt_find_uniql T).
Proof.
  unfold src_find_uniql, tgt_find_uniql.
  apply: ct_forall_identity => x. apply: cfs_forall_list => l1 L1 H1. apply: cfs_forall_list => l2 L2 H2.
  apply: ct_imp; first exact (cfs_uniq T _ _ (cfs_cat T l1 l2 L1 L2 H1 H2)).
  apply: ct_imp; first exact (cfs_mem T x l2 L2 H2).
  exact (cfs_not _ _ (cfs_mem T x l1 L1 H1)).
Qed.

Definition src_find_uniq (T : eqType) : Prop := ltac:(type_of_term (@find_uniq T)).
Definition tgt_find_uniq (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_FindSeq_find_uniq T (ct_decidable_eq T))).
Theorem find_uniq_correspondence (T : eqType) : PropSPropRel (src_find_uniq T) (tgt_find_uniq T).
Proof.
  unfold src_find_uniq, tgt_find_uniq.
  apply: ct_forall_identity => x. apply: cfs_forall_list => l1 L1 H1. apply: cfs_forall_list => l2 L2 H2.
  apply: ct_imp; first exact (cfs_uniq T _ _ (cfs_cat T l1 l2 L1 L2 H1 H2)).
  apply: ct_imp; first exact (cfs_mem T x l2 L2 H2).
  destruct H1. exact (ct_bool_false _ _ (cfs_any T _ _ (cfs_eq_pred T x) l1)).
Qed.

Definition src_findP_in_seq (T : eqType) : Prop := ltac:(type_of_term (@findP_in_seq T)).
Definition tgt_findP_in_seq (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_FindSeq_findP_in_seq T (ct_decidable_eq T))).
Theorem findP_in_seq_correspondence (T : eqType) : PropSPropRel (src_findP_in_seq T) (tgt_findP_in_seq T).
Proof.
  unfold src_findP_in_seq, tgt_findP_in_seq.
  apply: cfs_forall_pred => pR pL Hp. apply: cfs_forall_list => l L H. apply: ct_forall_identity => x.
  apply: ct_imp.
  - destruct H. exact (cfs_find_eq T pR pL Hp l (Some x)).
  - exact (ct_and _ _ _ _ (ct_bool_truth _ _ (Hp x)) (cfs_mem T x l L H)).
Qed.

Definition src_findP_notSome_in_seq (T : eqType) : Prop := ltac:(type_of_term (@findP_notSome_in_seq T)).
Definition tgt_findP_notSome_in_seq (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_FindSeq_findP_notSome_in_seq T (ct_decidable_eq T))).
Theorem findP_notSome_in_seq_correspondence (T : eqType) :
  PropSPropRel (src_findP_notSome_in_seq T) (tgt_findP_notSome_in_seq T).
Proof.
  unfold src_findP_notSome_in_seq, tgt_findP_notSome_in_seq.
  apply: cfs_forall_pred => pR pL Hp. apply: cfs_forall_list => l L H. apply: ct_forall_identity => x.
  destruct H.
  apply: ct_imp.
  - apply: ct_bool_truth. apply: ct_bool_not. apply: ct_decide_bool.
    rewrite -(findP_correspondence T pR pL Hp l).
    apply prop_sprop_rel_intro.
    + move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
    + intro E. apply strictly_inhabits. apply/eqP.
      have E' := f_equal cl_unopt (imported_eq_to_coq_eq _ _ E). by rewrite cl_unopt_opt in E'.
  - apply: ct_imp; first exact (cfs_mem T x l _ (@Lean.eq_refl _ _)).
    apply: ct_or; first exact (cfs_not _ _ (ct_bool_truth _ _ (Hp x))).
    apply: ct_exists_identity => y. exact (cfs_find_eq T pR pL Hp l (Some y)).
Qed.
