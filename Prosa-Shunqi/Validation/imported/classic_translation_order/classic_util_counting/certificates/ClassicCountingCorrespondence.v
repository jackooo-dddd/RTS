From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
From prosa Require Import classic.util.counting.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicCounting.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicCountingBase ClassicCountingList ClassicCountingOrd.

Module I := ImportedClassicCounting.
Local Open Scope nat_scope.

(** Certificates for [classic/util/counting.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: elements of an [eqType] identified (its Lean [DecidableEq] the
    eqType's decision procedure); sequences elementwise ([ClListRel]); natural
    numbers by [SubNatRel]; ordinals by their values ([CoOrdRel]); Boolean
    predicates pointwise; all with two-way totals.

    Computation: [count P l] against [List.countP P l] by structural induction
    through [countP.go] and its accumulator; [[exists x in 'I_n, P y x]]
    against [(List.finRange n).any (P y)] by the accepted ord_quantifier route
    (exported equation [ClassicCountingInterface.finRange_any]).

    Statements: the source side is the exact elaborated type of the pinned
    lemma (via [type of]; the source proof is not used). *)

Ltac type_of_term t := let T := type of t in exact T.

Lemma cn_countP_go (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL x)) :
  forall (s : seq T) n,
  Logic.eq (I.List_countP_go T pL (cl_map cid s) (sub_nat_to_imported n)) (sub_nat_to_imported (n + count pR s)).
Proof.
  elim => [|x s IH] n.
  - by rewrite addn0.
  - have -> : Logic.eq (I.List_countP_go T pL (cl_map cid (x :: s)) (sub_nat_to_imported n))
        (match pL x with
         | I.Bool_true => I.List_countP_go T pL (cl_map cid s) (sub_nat_to_imported n.+1)
         | I.Bool_false => I.List_countP_go T pL (cl_map cid s) (sub_nat_to_imported n) end).
    { cbn. destruct (pL x); reflexivity. }
    rewrite (ct_bool_rel_logic _ _ (Hp x)) (IH n.+1) (IH n).
    change (count pR (x :: s)) with (pR x + count pR s).
    case: (pR x).
    + by rewrite addSnnS add1n.
    + by rewrite add0n.
Qed.

Lemma cn_count (T : Type) pR pL (Hp : forall x, CtBoolRel (pR x) (pL x)) s sL : ClListRel (B := T) cid s sL ->
  SubNatRel (count pR s) (I.List_countP T pL sL).
Proof.
  intro H. destruct H. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  exact (cn_countP_go T pR pL Hp s 0).
Qed.

Lemma cn_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl_forall_list cid cid (fun _ => Logic.eq_refl _) PR PL). Qed.

Lemma cn_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cn_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cn_forall_pred (A : Type) (PR : (A -> bool) -> Prop) (PL : (A -> I.Bool) -> SProp) :
  (forall pR pL, (forall a, CtBoolRel (pR a) (pL a)) -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H (fun a => ct_l2b (pL a)) pL (fun a => ct_bool_surjective _)) (HR _)).
  - intro HL. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ (H pR (fun a => ct_b2l (pR a)) (fun a => ct_bool_canonical _)) (HL _)).
Qed.

Definition src_count_or (T : eqType) : Prop := ltac:(type_of_term (@count_or T)).
Definition tgt_count_or (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Counting_count_or T (ct_decidable_eq T))).
Theorem count_or_correspondence (T : eqType) : PropSPropRel (src_count_or T) (tgt_count_or T).
Proof.
  unfold src_count_or, tgt_count_or.
  apply: cn_forall_list => l L H. apply: cn_forall_pred => P PL HP. apply: cn_forall_pred => Q QL HQ.
  apply: sub_nat_le_correspondence.
  - apply: (cn_count T _ _ _ l L H) => x. exact (ct_bool_or _ _ _ _ (HP x) (HQ x)).
  - exact (sub_add_correspondence _ _ _ _ (cn_count T _ _ HP l L H) (cn_count T _ _ HQ l L H)).
Qed.

Definition src_sub_in_count (T : eqType) : Prop := ltac:(type_of_term (@sub_in_count T)).
Definition tgt_sub_in_count (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Counting_sub_in_count T (ct_decidable_eq T))).
Theorem sub_in_count_correspondence (T : eqType) : PropSPropRel (src_sub_in_count T) (tgt_sub_in_count T).
Proof.
  unfold src_sub_in_count, tgt_sub_in_count.
  apply: cn_forall_list => l L H. apply: cn_forall_pred => P1 P1L H1. apply: cn_forall_pred => P2 P2L H2.
  apply: ct_imp.
  - apply: ct_forall_identity => x.
    apply: ct_imp; first exact (cn_mem T x l L H).
    exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (H1 x)) (ct_bool_truth _ _ (H2 x))).
  - exact (sub_nat_le_correspondence _ _ _ _ (cn_count T _ _ H1 l L H) (cn_count T _ _ H2 l L H)).
Qed.

Definition src_count_sub_uniqr (T : eqType) : Prop := ltac:(type_of_term (@count_sub_uniqr T)).
Definition tgt_count_sub_uniqr (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Counting_count_sub_uniqr T (ct_decidable_eq T))).
Theorem count_sub_uniqr_correspondence (T : eqType) : PropSPropRel (src_count_sub_uniqr T) (tgt_count_sub_uniqr T).
Proof.
  unfold src_count_sub_uniqr, tgt_count_sub_uniqr.
  apply: cn_forall_list => l1 L1 H1. apply: cn_forall_list => l2 L2 H2. apply: cn_forall_pred => P PL HP.
  apply: ct_imp; first exact (cn_uniq T l1 L1 H1).
  apply: ct_imp.
  - rewrite /sub_mem. apply: ct_forall_identity => x. exact (ct_imp _ _ _ _ (cn_mem T x l1 L1 H1) (cn_mem T x l2 L2 H2)).
  - exact (sub_nat_le_correspondence _ _ _ _ (cn_count T _ _ HP l1 L1 H1) (cn_count T _ _ HP l2 L2 H2)).
Qed.

Definition src_count_pred_inj (T : eqType) : Prop := ltac:(type_of_term (@count_pred_inj T)).
Definition tgt_count_pred_inj (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Counting_count_pred_inj T (ct_decidable_eq T))).
Theorem count_pred_inj_correspondence (T : eqType) : PropSPropRel (src_count_pred_inj T) (tgt_count_pred_inj T).
Proof.
  unfold src_count_pred_inj, tgt_count_pred_inj.
  apply: cn_forall_list => l L H. apply: cn_forall_pred => P PL HP.
  apply: ct_imp; first exact (cn_uniq T l L H).
  apply: ct_imp.
  - apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
    apply: ct_imp; first exact (ct_bool_truth _ _ (HP x1)).
    exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (HP x2)) (ct_eq_rel T x1 x2)).
  - exact (sub_nat_le_correspondence _ _ _ _ (cn_count T _ _ HP l L H) (sub_nat_rel_canonical 1)).
Qed.

(** Families [T -> 'I_n -> bool] against [T -> Fin n -> Bool], pointwise on related ordinals. *)
Definition CnFamRel (T : Type) nR nL (PR : T -> 'I_nR -> bool) (PL : T -> Fin nL -> I.Bool) : SProp :=
  forall x o oL, CoOrdRel nR nL o oL -> CtBoolRel (PR x o) (PL x oL).

Lemma cn_forall_fam (T : Type) nR nL (Hn : SubNatRel nR nL) (PR : (T -> 'I_nR -> bool) -> Prop) (PL : (T -> Fin nL -> I.Bool) -> SProp) :
  (forall pR pL, CnFamRel T nR nL pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  apply (co_forall_cover_sprop _ _ (CnFamRel T nR nL)
    (fun pR x oL => ct_b2l (pR x (co_fin_to_ord nR nL Hn oL))) (fun pL x oR => ct_l2b (pL x (co_ord_to_fin nR nL Hn oR)))).
  - intros pR x oR oL Ho. rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)). exact (ct_bool_canonical _).
  - intros pL x oR oL Ho. rewrite -(co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho). exact (ct_bool_surjective _).
Qed.

Definition src_count_exists (T : eqType) : Prop := ltac:(type_of_term (@count_exists T)).
Definition tgt_count_exists (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Counting_count_exists T (ct_decidable_eq T))).
Theorem count_exists_correspondence (T : eqType) : PropSPropRel (src_count_exists T) (tgt_count_exists T).
Proof.
  unfold src_count_exists, tgt_count_exists.
  apply: cn_forall_list => l L H. apply: ct_forall_nat => nR nL Hn. apply: (cn_forall_fam T nR nL Hn) => P PL HP.
  apply: ct_imp; first exact (cn_uniq T l L H).
  apply: ct_imp.
  - apply: (co_forall_ord nR nL Hn) => y yL Hy. apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
    apply: ct_imp; first exact (ct_bool_truth _ _ (HP x1 _ _ Hy)).
    exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (HP x2 _ _ Hy)) (ct_eq_rel T x1 x2)).
  - apply: sub_nat_le_correspondence; last exact Hn.
    apply: (cn_count T _ _ _ l L H) => y. exact (co_exists_rel nR nL Hn (P y) (PL y) (HP y)).
Qed.
