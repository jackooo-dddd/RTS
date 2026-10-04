From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From prosa Require Import classic.util.sorting.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicSorting.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicSortingBase ClassicSortingList.

Module I := ImportedClassicSorting.
Local Open Scope nat_scope.

(** Certificates for [classic/util/sorting.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: elements of an [eqType] identified (its Lean [DecidableEq] the
    eqType's decision procedure); sequences elementwise ([ClListRel]); natural
    numbers by [SubNatRel]; Boolean relations and functions [T -> nat]
    pointwise; all with two-way totals.

    [sorted leT s] against [List.IsChain (fun a b => leT a b = true) s]:
    forward by induction along [path], backward by recursion on the list with
    term-level inversion of [IsChain] ([cs_chain_head], [cs_chain_tail]).
    [(size s).-1] against [length - 1] (truncated subtraction, [subn1]).

    Statements: the source side is the exact elaborated type of the pinned
    lemma (via [type of]; the source proof is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

Inductive CsTrue : SProp := cs_true_intro.

Section Chain.
Variables (T : Type) (leR : T -> T -> bool) (leL : T -> T -> I.Bool).
Hypothesis HR : forall a b, CtBoolRel (leR a b) (leL a b).
Notation RL := (fun a b : T => Lean.eq (leL a b) I.Bool_true).

Definition cs_chain_head (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) : RL x y :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons a (I.List_cons b _) => RL a b | _ => CsTrue end) with
  | I.List_IsChain_nil => cs_true_intro
  | I.List_IsChain_singleton _ => cs_true_intro
  | I.List_IsChain_cons_cons a b l h _ => h
  end.

Definition cs_chain_tail (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) :
    I.List_IsChain T RL (I.List_cons T y l) :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons _ (I.List_cons b l') => I.List_IsChain T RL (I.List_cons T b l') | _ => CsTrue end) with
  | I.List_IsChain_nil => cs_true_intro
  | I.List_IsChain_singleton _ => cs_true_intro
  | I.List_IsChain_cons_cons a b l _ t => t
  end.

Fixpoint cs_path_forward (x : T) (s : seq T) : path leR x s -> I.List_IsChain T RL (I.List_cons T x (cl_map cid s)) :=
  match s as s0 return path leR x s0 -> I.List_IsChain T RL (I.List_cons T x (cl_map cid s0)) with
  | [::] => fun _ => I.List_IsChain_singleton T RL x
  | y :: s' => fun H =>
      I.List_IsChain_cons_cons T RL x y (cl_map cid s')
        (prop_to_sprop _ _ (ct_bool_truth _ _ (HR x y)) (elimTF andP H).1)
        (cs_path_forward y s' (elimTF andP H).2)
  end.

Fixpoint cs_path_backward (x : T) (s : seq T) : I.List_IsChain T RL (I.List_cons T x (cl_map cid s)) -> StrictlyInhabited (path leR x s) :=
  match s as s0 return I.List_IsChain T RL (I.List_cons T x (cl_map cid s0)) -> StrictlyInhabited (path leR x s0) with
  | [::] => fun _ => strictly_inhabits (Logic.eq_refl true)
  | y :: s' => fun H =>
      match cs_path_backward y s' (cs_chain_tail x y _ H) with
      | strictly_inhabits Hp =>
          strictly_inhabits (introT andP (conj (sprop_to_prop _ _ (ct_bool_truth _ _ (HR x y)) (cs_chain_head x y _ H)) Hp))
      end
  end.

Lemma cs_sorted s : PropSPropRel (sorted leR s) (I.List_IsChain T RL (cl_map cid s)).
Proof.
  apply prop_sprop_rel_intro; destruct s as [|x s].
  - intros _. exact (I.List_IsChain_nil T RL).
  - exact (cs_path_forward x s).
  - intros _. exact (strictly_inhabits (Logic.eq_refl true)).
  - exact (cs_path_backward x s).
Qed.
End Chain.

Lemma cs_sorted_rel (T : Type) leR leL (HR : forall a b, CtBoolRel (leR a b) (leL a b)) s sL : ClListRel cid s sL ->
  PropSPropRel (sorted leR s) (I.List_IsChain T (fun a b => Lean.eq (leL a b) I.Bool_true) sL).
Proof. intro H. destruct H. exact (cs_sorted T leR leL HR s). Qed.

Lemma cs_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl_forall_list cid cid (fun _ => Logic.eq_refl _) PR PL). Qed.

Lemma cs_forall_rel (A : Type) (PR : (A -> A -> bool) -> Prop) (PL : (A -> A -> I.Bool) -> SProp) :
  (forall pR pL, (forall a b, CtBoolRel (pR a b) (pL a b)) -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H (fun a b => ct_l2b (pL a b)) pL (fun a b => ct_bool_surjective _)) (HR _)).
  - intro HL. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ (H pR (fun a b => ct_b2l (pR a b)) (fun a b => ct_bool_canonical _)) (HL _)).
Qed.

Lemma cs_transitive (T : Type) (R : T -> T -> bool) RL (HR : forall a b, CtBoolRel (R a b) (RL a b)) :
  PropSPropRel (transitive R)
    (forall y x z, Lean.eq (RL x y) I.Bool_true -> Lean.eq (RL y z) I.Bool_true -> Lean.eq (RL x z) I.Bool_true).
Proof.
  rewrite /transitive. apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (HR x y)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (HR y z)) (ct_bool_truth _ _ (HR x z))).
Qed.

Lemma cs_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Lemma cs_pred (T : Type) s sL : ClListRel (B := T) cid s sL ->
  SubNatRel (size s).-1 (ct_sub (I.List_length T sL) (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro H. rewrite -subn1. exact (ct_sub_rel _ _ _ _ (cs_size T s sL H) (sub_nat_rel_canonical 1)). Qed.

Lemma cs_nth (T : Type) (x0 : T) s sL nR nL : ClListRel cid s sL -> SubNatRel nR nL ->
  Logic.eq (nth x0 s nR) (I.List_getD T sL nL x0).
Proof. intros H Hn. destruct H. rewrite -(imported_eq_to_coq_eq _ _ Hn). exact (cl_nth cid x0 s nR). Qed.

Lemma cs_succ nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                    (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro H. have := sub_add_correspondence _ _ 1 _ H (sub_nat_rel_canonical 1). by rewrite addn1. Qed.

Lemma cs_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cs_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cs_antisym (T : eqType) leR leL (HR : forall a b, CtBoolRel (leR a b) (leL a b)) s sL : ClListRel cid s sL ->
  PropSPropRel (list.antisymmetric_over_list leR s)
    (I.Prosa_Classic_Util_List_antisymmetric_over_list T (ct_decidable_eq T) leL sL).
Proof.
  intro Hs. apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: ct_imp; first exact (cs_mem T x1 s sL Hs).
  apply: ct_imp; first exact (cs_mem T x2 s sL Hs).
  apply: ct_imp; first exact (ct_bool_truth _ _ (HR x1 x2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (HR x2 x1)).
  exact (ct_eq_rel T x1 x2).
Qed.

Lemma cs_rcons (T : Type) s sL (x : T) : ClListRel cid s sL ->
  ClListRel cid (rcons s x)
    (I.HAppend_hAppend (I.List T) (I.List T) (I.List T) (I.instHAppendOfAppend (I.List T) (I.List_instAppend T))
       sL (I.List_cons T x (I.List_nil T))).
Proof. intro H. destruct H. apply: coq_eq_to_imported_eq. exact (cl_rcons cid s x). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_sort_ordered (T : eqType) : Prop := ltac:(type_of_term (@sort_ordered T)).
Definition tgt_sort_ordered (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Sorting_sort_ordered T (ct_decidable_eq T))).
Theorem sort_ordered_correspondence (T : eqType) : PropSPropRel (src_sort_ordered T) (tgt_sort_ordered T).
Proof.
  unfold src_sort_ordered, tgt_sort_ordered.
  apply: cs_forall_rel => leR leL HR. apply: cs_forall_list => xs XS H. apply: ct_forall_identity => d.
  apply: ct_forall_nat => i iL Hi.
  apply: ct_imp; first exact (cs_sorted_rel T leR leL HR xs XS H).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hi (cs_pred T xs XS H)).
  rewrite (cs_nth T d xs XS _ _ H Hi) (cs_nth T d xs XS _ _ H (cs_succ _ _ Hi)). exact (ct_bool_truth _ _ (HR _ _)).
Qed.

Definition src_sorted_rcons_prefix (T : eqType) : Prop := ltac:(type_of_term (@sorted_rcons_prefix T)).
Definition tgt_sorted_rcons_prefix (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Sorting_sorted_rcons_prefix T (ct_decidable_eq T))).
Theorem sorted_rcons_prefix_correspondence (T : eqType) : PropSPropRel (src_sorted_rcons_prefix T) (tgt_sorted_rcons_prefix T).
Proof.
  unfold src_sorted_rcons_prefix, tgt_sorted_rcons_prefix.
  apply: cs_forall_rel => leR leL HR. apply: cs_forall_list => xs XS H. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cs_sorted_rel T leR leL HR _ _ (cs_rcons T xs XS x H)) (cs_sorted_rel T leR leL HR xs XS H)).
Qed.

Definition src_order_sorted_rcons (T : eqType) : Prop := ltac:(type_of_term (@order_sorted_rcons T)).
Definition tgt_order_sorted_rcons (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Sorting_order_sorted_rcons T (ct_decidable_eq T))).
Theorem order_sorted_rcons_correspondence (T : eqType) : PropSPropRel (src_order_sorted_rcons T) (tgt_order_sorted_rcons T).
Proof.
  unfold src_order_sorted_rcons, tgt_order_sorted_rcons.
  apply: cs_forall_rel => leR leL HR. apply: cs_forall_list => xs XS H.
  apply: ct_imp; first exact (cs_transitive T leR leL HR).
  apply: ct_forall_identity => x. apply: ct_forall_identity => lst.
  apply: ct_imp; first exact (cs_sorted_rel T leR leL HR _ _ (cs_rcons T xs XS lst H)).
  exact (ct_imp _ _ _ _ (cs_mem T x xs XS H) (ct_bool_truth _ _ (HR x lst))).
Qed.

Definition src_sorted_lt_idx_implies_rel (T : eqType) : Prop := ltac:(type_of_term (@sorted_lt_idx_implies_rel T)).
Definition tgt_sorted_lt_idx_implies_rel (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Sorting_sorted_lt_idx_implies_rel T (ct_decidable_eq T))).
Theorem sorted_lt_idx_implies_rel_correspondence (T : eqType) :
  PropSPropRel (src_sorted_lt_idx_implies_rel T) (tgt_sorted_lt_idx_implies_rel T).
Proof.
  unfold src_sorted_lt_idx_implies_rel, tgt_sorted_lt_idx_implies_rel.
  apply: cs_forall_rel => leR leL HR. apply: cs_forall_list => xs XS H. apply: ct_forall_identity => d.
  apply: ct_imp; first exact (cs_transitive T leR leL HR).
  apply: ct_forall_nat => i1 i1L H1. apply: ct_forall_nat => i2 i2L H2.
  apply: ct_imp; first exact (cs_sorted_rel T leR leL HR xs XS H).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ H1 H2).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ H2 (cs_size T xs XS H)).
  rewrite (cs_nth T d xs XS _ _ H H1) (cs_nth T d xs XS _ _ H H2). exact (ct_bool_truth _ _ (HR _ _)).
Qed.

Definition src_sorted_rel_implies_le_idx (T : eqType) : Prop := ltac:(type_of_term (@sorted_rel_implies_le_idx T)).
Definition tgt_sorted_rel_implies_le_idx (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Sorting_sorted_rel_implies_le_idx T (ct_decidable_eq T))).
Theorem sorted_rel_implies_le_idx_correspondence (T : eqType) :
  PropSPropRel (src_sorted_rel_implies_le_idx T) (tgt_sorted_rel_implies_le_idx T).
Proof.
  unfold src_sorted_rel_implies_le_idx, tgt_sorted_rel_implies_le_idx.
  apply: cs_forall_rel => leR leL HR. apply: cs_forall_list => xs XS H. apply: ct_forall_identity => d.
  apply: ct_imp; first exact (cs_transitive T leR leL HR).
  apply: ct_forall_nat => i1 i1L H1. apply: ct_forall_nat => i2 i2L H2.
  apply: ct_imp; first exact (cs_uniq T xs XS H).
  apply: ct_imp; first exact (cs_antisym T leR leL HR xs XS H).
  apply: ct_imp; first exact (cs_sorted_rel T leR leL HR xs XS H).
  apply: ct_imp.
  - rewrite (cs_nth T d xs XS _ _ H H1) (cs_nth T d xs XS _ _ H H2). exact (ct_bool_truth _ _ (HR _ _)).
  - apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ H1 (cs_size T xs XS H)).
    exact (ct_imp _ _ _ _ (sub_nat_lt_correspondence _ _ _ _ H2 (cs_size T xs XS H)) (sub_nat_le_correspondence _ _ _ _ H1 H2)).
Qed.

Lemma cs_forall_natfun (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall FR FL, (forall x, SubNatRel (FR x) (FL x)) -> PropSPropRel (PR FR) (PL FL)) ->
  PropSPropRel (forall F, PR F) (forall F, PL F).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR FL. exact (prop_to_sprop _ _ (H (fun x => sub_nat_to_rocq (FL x)) FL (fun x => sub_nat_rel_surjective _)) (HR _)).
  - intro HL. apply strictly_inhabits. intro FR.
    exact (sprop_to_prop _ _ (H FR (fun x => sub_nat_to_imported (FR x)) (fun x => sub_nat_rel_canonical _)) (HL _)).
Qed.

Lemma cs_fn_nth (T : Type) FR FL (HF : forall x : T, SubNatRel (FR x) (FL x)) d xs XS (H : ClListRel cid xs XS) nR nL :
  SubNatRel nR nL -> SubNatRel (FR (nth d xs nR)) (FL (I.List_getD T XS nL d)).
Proof. intro Hn. rewrite -(cs_nth T d xs XS _ _ H Hn). exact (HF _). Qed.

Definition src_prev_le_next : Prop := ltac:(type_of_term @prev_le_next).
Definition tgt_prev_le_next : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Sorting_prev_le_next).
Theorem prev_le_next_correspondence : PropSPropRel src_prev_le_next tgt_prev_le_next.
Proof.
  unfold src_prev_le_next, tgt_prev_le_next.
  apply: ct_forall_identity => T. apply: cs_forall_natfun => FR FL HF.
  apply: cs_forall_list => xs XS H. apply: ct_forall_identity => d.
  apply: ct_forall_nat => i iL Hi. apply: ct_forall_nat => k kL Hk.
  pose HFn := cs_fn_nth T FR FL HF d xs XS H.
  apply: ct_imp.
  - apply: ct_forall_nat => j jL Hj.
    exact (ct_imp _ _ _ _ (sub_nat_lt_correspondence _ _ _ _ Hj (cs_pred T xs XS H))
             (sub_nat_le_correspondence _ _ _ _ (HFn _ _ Hj) (HFn _ _ (cs_succ _ _ Hj)))).
  - have Hik := sub_add_correspondence _ _ _ _ Hi Hk.
    exact (ct_imp _ _ _ _ (sub_nat_le_correspondence _ _ _ _ Hik (cs_pred T xs XS H))
             (sub_nat_le_correspondence _ _ _ _ (HFn _ _ Hi) (HFn _ _ Hik))).
Qed.
