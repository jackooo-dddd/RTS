From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq bigop.
From prosa Require Import classic.util.sum.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicSum.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicSumBase ClassicSumList.

Module I := ImportedClassicSum.
Local Open Scope nat_scope.

(** Certificates for [classic/util/sum.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: elements of [eqType]s identified (their Lean [DecidableEq] the
    eqTypes' decision procedures); sequences elementwise; natural numbers by
    [SubNatRel]; Boolean predicates and functions to [nat] pointwise; all with
    two-way totals.

    The Lean [Finset.Ico] sums of six statements are exported in the projected
    form [List.foldr Nat.add 0 (List.map f r)], [r = List.range' m (n - m) 1]
    (filtered by [decide (P i = true)] for filtered sums), guarded in the export
    root by kernel-checked [Eq.refl] equations (see
    [ClassicSumInterface] and planning/classic_policy/tool_changes.md).  They
    are related to MathComp's [\sum_(m <= i < n | P i) F i] (a fold over
    [index_iota m n]) by structural induction; [sumSeq]/[sumFiltered] (the
    accepted v0.6 helpers) likewise.

    Statements: the source side is the exact elaborated type of the pinned
    lemma (via [type of]; the source proof is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

Lemma cs_nat_logic nR nL : SubNatRel nR nL -> Logic.eq nL (sub_nat_to_imported nR).
Proof. intro H. exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ H)). Qed.

(* ------------------------------------------------------------------ *)
(** * Folds over natural-number lists *)

Fixpoint cs_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cs_natl s') end.

Lemma cs_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cs_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cs_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cs_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cs_natl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cs_natl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cs_filter1 (pR : nat -> bool) (pL : Lean.Nat -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL (sub_nat_to_imported x))) : forall s,
  Logic.eq (cs_natl (filter pR s)) (I.List_filter_inst1 Lean.Nat pL (cs_natl s)).
Proof.
  elim => [|x s IH] //=.
  have -> : Logic.eq (I.List_filter_inst1 Lean.Nat pL (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported x) (cs_natl s)))
      (match pL (sub_nat_to_imported x) with
       | I.Bool_true => I.List_cons_inst1 Lean.Nat (sub_nat_to_imported x) (I.List_filter_inst1 Lean.Nat pL (cs_natl s))
       | I.Bool_false => I.List_filter_inst1 Lean.Nat pL (cs_natl s) end).
  { cbn. destruct (pL (sub_nat_to_imported x)); reflexivity. }
  rewrite (ct_bool_rel_logic _ _ (Hp x)) -IH. by case: (pR x).
Qed.

Lemma cs_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Lemma cs_big_filter_fold (xs : seq nat) (P : pred nat) (F : nat -> nat) :
  Logic.eq (\sum_(i <- xs | P i) F i) (foldr addn 0 (map F (filter P xs))).
Proof. by rewrite -big_filter cs_big_fold. Qed.

Definition CsFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cs_fun_canonical FR FL (HF : CsFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cs_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cs_sub_canon a b : Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof. exact (ct_sub_canonical a b). Qed.

(** [\sum_(m <= i < n) F i] against the projected Lean fold. *)
Lemma cs_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CsFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cs_nat_logic _ _ Hm) (cs_nat_logic _ _ Hn) cs_sub_canon cs_iota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cs_foldr_add FL FR (cs_fun_canonical FR FL HF)).
  by rewrite cs_big_fold.
Qed.

Lemma cs_ico_filter mR mL nR nL (PR : pred nat) PL (HP : forall kR kL, SubNatRel kR kL -> CtBoolRel (PR kR) (PL kL)) FR FL
    (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CsFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR | PR i) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL
          (I.List_filter_inst1 Lean.Nat (fun i => I.Decidable_decide (Lean.eq (PL i) I.Bool_true) (I.instDecidableEqBool (PL i) I.Bool_true))
             (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero))))).
Proof.
  rewrite (cs_nat_logic _ _ Hm) (cs_nat_logic _ _ Hn) cs_sub_canon cs_iota_range.
  rewrite -(cs_filter1 PR _ (fun x => ct_decide_bool _ _ _ (ct_bool_truth _ _ (HP _ _ (sub_nat_rel_canonical x))))).
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cs_foldr_add FL FR (cs_fun_canonical FR FL HF)).
  by rewrite cs_big_filter_fold.
Qed.

(** [sumSeq] / [sumFiltered] (accepted v0.6 helpers). *)
Lemma cs_sumSeq (T : Type) (FR : T -> nat) (FL : T -> Lean.Nat) (HF : forall x, SubNatRel (FR x) (FL x)) : forall l,
  SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq T (cl_map cid l) FL).
Proof.
  intro l. induction l as [|x l IH]; first by rewrite big_nil; exact (sub_nat_rel_canonical 0).
  rewrite big_cons.
  change (SubNatRel (FR x + \sum_(j <- l) FR j) (Lean.Nat_add (FL x) (I.Prosa_Util_Sum_sumSeq T (cl_map cid l) FL))).
  exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cs_sumSeq_rel (T : Type) FR FL (HF : forall x, SubNatRel (FR x) (FL x)) l L : ClListRel (B := T) cid l L ->
  SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq T L FL).
Proof. intro H. destruct H. exact (cs_sumSeq T FR FL HF l). Qed.

Lemma cs_sumFiltered_rel (T : Type) (PR : T -> bool) PL (HP : forall x, CtBoolRel (PR x) (PL x)) FR FL
    (HF : forall x, SubNatRel (FR x) (FL x)) l L : ClListRel (B := T) cid l L ->
  SubNatRel (\sum_(i <- l | PR i) FR i) (I.Prosa_Util_Sum_sumFiltered T L PL FL).
Proof.
  intro H. destruct H. rewrite -big_filter.
  have E := cl_filter cid PR PL HP l.
  change (SubNatRel (\sum_(i <- filter PR l) FR i) (I.Prosa_Util_Sum_sumSeq T (I.List_filter T PL (cl_map cid l)) FL)).
  rewrite -E. exact (cs_sumSeq T FR FL HF _).
Qed.

(* ------------------------------------------------------------------ *)
(** * Covers and leaves *)

Lemma cs_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl_forall_list cid cid (fun _ => Logic.eq_refl _) PR PL). Qed.

Lemma cs_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cs_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cs_forall_tfun (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall FR FL, (forall x, SubNatRel (FR x) (FL x)) -> PropSPropRel (PR FR) (PL FL)) -> PropSPropRel (forall F, PR F) (forall F, PL F).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR FL. exact (prop_to_sprop _ _ (H (fun x => sub_nat_to_rocq (FL x)) FL (fun x => sub_nat_rel_surjective _)) (HR _)).
  - intro HL. apply strictly_inhabits. intro FR.
    exact (sprop_to_prop _ _ (H FR (fun x => sub_nat_to_imported (FR x)) (fun x => sub_nat_rel_canonical _)) (HL _)).
Qed.

Lemma cs_natfun_target_total FL : CsFunRel (fun a => sub_nat_to_rocq (FL (sub_nat_to_imported a))) FL.
Proof. intros a aL Ha. rewrite (cs_nat_logic _ _ Ha). exact (sub_nat_rel_surjective _). Qed.

Lemma cs_natfun_source_total FR : CsFunRel FR (fun aL => sub_nat_to_imported (FR (sub_nat_to_rocq aL))).
Proof.
  intros a aL Ha. rewrite (cs_nat_logic _ _ Ha) sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma cs_forall_natfun (PR : (nat -> nat) -> Prop) (PL : (Lean.Nat -> Lean.Nat) -> SProp) :
  (forall FR FL, CsFunRel FR FL -> PropSPropRel (PR FR) (PL FL)) -> PropSPropRel (forall F, PR F) (forall F, PL F).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR FL. exact (prop_to_sprop _ _ (H _ _ (cs_natfun_target_total FL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro FR. exact (sprop_to_prop _ _ (H _ _ (cs_natfun_source_total FR)) (HL _)).
Qed.

Definition CsPredRel (PR : nat -> bool) (PL : Lean.Nat -> I.Bool) : SProp :=
  forall kR kL, SubNatRel kR kL -> CtBoolRel (PR kR) (PL kL).

Lemma cs_pred_target_total PL : CsPredRel (fun k => ct_l2b (PL (sub_nat_to_imported k))) PL.
Proof. intros k kL Hk. rewrite (cs_nat_logic _ _ Hk). exact (ct_bool_surjective _). Qed.

Lemma cs_pred_source_total PR : CsPredRel PR (fun kL => ct_b2l (PR (sub_nat_to_rocq kL))).
Proof. intros k kL Hk. rewrite (cs_nat_logic _ _ Hk) sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cs_forall_pred (PR : pred nat -> Prop) (PL : (Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CsPredRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H _ _ (cs_pred_target_total pL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro pR. exact (sprop_to_prop _ _ (H _ _ (cs_pred_source_total pR)) (HL _)).
Qed.

Lemma cs_forall_tpred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, (forall a, CtBoolRel (pR a) (pL a)) -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H (fun a => ct_l2b (pL a)) pL (fun a => ct_bool_surjective _)) (HR _)).
  - intro HL. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ (H pR (fun a => ct_b2l (pR a)) (fun a => ct_bool_canonical _)) (HL _)).
Qed.

Lemma cs_range_rel a aL x xL b bL : SubNatRel a aL -> SubNatRel x xL -> SubNatRel b bL ->
  CtBoolRel (a <= x < b) (I.Bool_and (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat aL xL) (I.Nat_decLe aL xL))
                                     (I.Decidable_decide (I.LT_lt_inst1 Lean.Nat I.instLTNat xL bL) (I.Nat_decLt xL bL))).
Proof. intros Ha Hx Hb. exact (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Ha Hx) (ct_decide_lt _ _ _ _ Hx Hb)). Qed.

Lemma cs_succ nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                    (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro H. have := sub_add_correspondence _ _ 1 _ H (sub_nat_rel_canonical 1). by rewrite addn1. Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_sum_seq_diff (T : eqType) : Prop := ltac:(type_of_term (@sum_seq_diff T)).
Definition tgt_sum_seq_diff (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Sum_sum_seq_diff T (ct_decidable_eq T))).
Theorem sum_seq_diff_correspondence (T : eqType) : PropSPropRel (src_sum_seq_diff T) (tgt_sum_seq_diff T).
Proof.
  unfold src_sum_seq_diff, tgt_sum_seq_diff.
  apply: cs_forall_list => rs RS H. apply: cs_forall_tfun => FR FL HF. apply: cs_forall_tfun => GR GL HG.
  apply: ct_imp.
  - apply: ct_forall_identity => i. exact (ct_imp _ _ _ _ (cs_mem T i rs RS H) (sub_nat_le_correspondence _ _ _ _ (HG i) (HF i))).
  - apply: sub_nat_eq_correspondence.
    + apply: (cs_sumSeq_rel T _ _ _ rs RS H) => i. exact (ct_sub_rel _ _ _ _ (HF i) (HG i)).
    + exact (ct_sub_rel _ _ _ _ (cs_sumSeq_rel T FR FL HF rs RS H) (cs_sumSeq_rel T GR GL HG rs RS H)).
Qed.

Definition src_sum_diff : Prop := ltac:(type_of_term @sum_diff).
Definition tgt_sum_diff : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Sum_sum_diff).
Theorem sum_diff_correspondence : PropSPropRel src_sum_diff tgt_sum_diff.
Proof.
  unfold src_sum_diff, tgt_sum_diff.
  apply: ct_forall_nat => n nL Hn. apply: cs_forall_natfun => FR FL HF. apply: cs_forall_natfun => GR GL HG.
  have H0 : SubNatRel 0 (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) := sub_nat_rel_canonical 0.
  apply: ct_imp.
  - apply: ct_forall_nat => i iL Hi.
    exact (ct_imp _ _ _ _ (sub_nat_lt_correspondence _ _ _ _ Hi Hn) (sub_nat_le_correspondence _ _ _ _ (HG _ _ Hi) (HF _ _ Hi))).
  - apply: sub_nat_eq_correspondence.
    + apply: (cs_ico _ _ _ _ _ _ H0 Hn) => k kL Hk. exact (ct_sub_rel _ _ _ _ (HF _ _ Hk) (HG _ _ Hk)).
    + exact (ct_sub_rel _ _ _ _ (cs_ico _ _ _ _ _ _ H0 Hn HF) (cs_ico _ _ _ _ _ _ H0 Hn HG)).
Qed.

Definition src_extend_sum : Prop := ltac:(type_of_term @extend_sum).
Definition tgt_extend_sum : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Sum_extend_sum).
Theorem extend_sum_correspondence : PropSPropRel src_extend_sum tgt_extend_sum.
Proof.
  unfold src_extend_sum, tgt_extend_sum.
  apply: ct_forall_nat => t1 t1L H1. apply: ct_forall_nat => t2 t2L H2.
  apply: ct_forall_nat => t1' t1L' H1'. apply: ct_forall_nat => t2' t2L' H2'. apply: cs_forall_natfun => FR FL HF.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1' H1).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H2 H2').
  exact (sub_nat_le_correspondence _ _ _ _ (cs_ico _ _ _ _ _ _ H1 H2 HF) (cs_ico _ _ _ _ _ _ H1' H2' HF)).
Qed.

Definition src_leq_sum_nat : Prop := ltac:(type_of_term @leq_sum_nat).
Definition tgt_leq_sum_nat : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Sum_leq_sum_nat).
Theorem leq_sum_nat_correspondence : PropSPropRel src_leq_sum_nat tgt_leq_sum_nat.
Proof.
  unfold src_leq_sum_nat, tgt_leq_sum_nat.
  apply: ct_forall_nat => m mL Hm. apply: ct_forall_nat => n nL Hn. apply: cs_forall_pred => PR PL HP.
  apply: cs_forall_natfun => E1 E1L H1. apply: cs_forall_natfun => E2 E2L H2.
  apply: ct_imp.
  - apply: ct_forall_nat => i iL Hi.
    apply: ct_imp; first exact (ct_bool_truth _ _ (cs_range_rel _ _ _ _ _ _ Hm Hi Hn)).
    exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (HP _ _ Hi)) (sub_nat_le_correspondence _ _ _ _ (H1 _ _ Hi) (H2 _ _ Hi))).
  - exact (sub_nat_le_correspondence _ _ _ _ (cs_ico_filter _ _ _ _ _ _ HP _ _ Hm Hn H1) (cs_ico_filter _ _ _ _ _ _ HP _ _ Hm Hn H2)).
Qed.

Lemma cs_one_rel : CsFunRel (fun _ => 1) (fun _ => I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)).
Proof. intros k kL Hk. exact (sub_nat_rel_canonical 1). Qed.

Definition src_leq_sum1_smaller_range : Prop := ltac:(type_of_term @leq_sum1_smaller_range).
Definition tgt_leq_sum1_smaller_range : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Sum_leq_sum1_smaller_range).
Theorem leq_sum1_smaller_range_correspondence : PropSPropRel src_leq_sum1_smaller_range tgt_leq_sum1_smaller_range.
Proof.
  unfold src_leq_sum1_smaller_range, tgt_leq_sum1_smaller_range.
  apply: ct_forall_nat => m mL Hm. apply: ct_forall_nat => n nL Hn.
  apply: cs_forall_pred => PR PL HP. apply: cs_forall_pred => QR QL HQ.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => b bL Hb.
  apply: ct_imp.
  - apply: ct_forall_nat => i iL Hi.
    apply: ct_imp; first exact (ct_and _ _ _ _ (ct_bool_truth _ _ (cs_range_rel _ _ _ _ _ _ Hm Hi Hn)) (ct_bool_truth _ _ (HP _ _ Hi))).
    exact (ct_and _ _ _ _ (ct_bool_truth _ _ (cs_range_rel _ _ _ _ _ _ Ha Hi Hb)) (ct_bool_truth _ _ (HQ _ _ Hi))).
  - exact (sub_nat_le_correspondence _ _ _ _ (cs_ico_filter _ _ _ _ _ _ HP _ _ Hm Hn cs_one_rel)
                                             (cs_ico_filter _ _ _ _ _ _ HQ _ _ Ha Hb cs_one_rel)).
Qed.

Definition src_leq_pred_sum (T : eqType) : Prop := ltac:(type_of_term (@leq_pred_sum T)).
Definition tgt_leq_pred_sum (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Sum_leq_pred_sum T (ct_decidable_eq T))).
Theorem leq_pred_sum_correspondence (T : eqType) : PropSPropRel (src_leq_pred_sum T) (tgt_leq_pred_sum T).
Proof.
  unfold src_leq_pred_sum, tgt_leq_pred_sum.
  apply: cs_forall_list => r R H. apply: cs_forall_tpred => P1 P1L H1. apply: cs_forall_tpred => P2 P2L H2.
  apply: cs_forall_tfun => FR FL HF.
  apply: ct_imp.
  - apply: ct_forall_identity => i. exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (H1 i)) (ct_bool_truth _ _ (H2 i))).
  - exact (sub_nat_le_correspondence _ _ _ _ (cs_sumFiltered_rel T _ _ H1 FR FL HF r R H) (cs_sumFiltered_rel T _ _ H2 FR FL HF r R H)).
Qed.

Definition src_sum_le_summation_range : Prop := ltac:(type_of_term @sum.sum_le_summation_range).
Definition tgt_sum_le_summation_range : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Sum_sum_le_summation_range).
Theorem sum_le_summation_range_correspondence : PropSPropRel src_sum_le_summation_range tgt_sum_le_summation_range.
Proof.
  unfold src_sum_le_summation_range, tgt_sum_le_summation_range.
  apply: cs_forall_natfun => fR fL Hf. apply: ct_forall_nat => t tL Ht. apply: ct_forall_nat => d dL Hd.
  have Htd := sub_add_correspondence _ _ _ _ Ht Hd.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (cs_ico _ _ _ _ _ _ Ht Htd Hf) Hd).
  apply: ct_exists_nat => x xL Hx.
  exact (ct_and _ _ _ _ (ct_bool_truth _ _ (cs_range_rel _ _ _ _ _ _ Ht Hx Htd)) (sub_nat_eq_correspondence _ _ _ _ (Hf _ _ Hx) (sub_nat_rel_canonical 0))).
Qed.

Lemma cs_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Lemma cs_pred_size (T : Type) s sL : ClListRel (B := T) cid s sL ->
  SubNatRel (size s).-1 (ct_sub (I.List_length T sL) (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro H. rewrite -subn1. exact (ct_sub_rel _ _ _ _ (cs_size T s sL H) (sub_nat_rel_canonical 1)). Qed.

Lemma cs_fn_nth (T : Type) FR FL (HF : forall x : T, SubNatRel (FR x) (FL x)) d xs XS (H : ClListRel cid xs XS) nR nL :
  SubNatRel nR nL -> SubNatRel (FR (nth d xs nR)) (FL (I.List_getD T XS nL d)).
Proof.
  intro Hn. destruct H. rewrite -(imported_eq_to_coq_eq _ _ Hn) -(cl_nth cid d xs nR). exact (HF _).
Qed.

Definition src_telescoping_sum : Prop := ltac:(type_of_term @telescoping_sum).
Definition tgt_telescoping_sum : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Sum_telescoping_sum).
Theorem telescoping_sum_correspondence : PropSPropRel src_telescoping_sum tgt_telescoping_sum.
Proof.
  unfold src_telescoping_sum, tgt_telescoping_sum.
  apply: ct_forall_identity => T. apply: cs_forall_tfun => FR FL HF.
  apply: cs_forall_list => r R H. apply: ct_forall_identity => x0.
  have Hp := cs_pred_size T r R H.
  pose HFn := cs_fn_nth T FR FL HF x0 r R H.
  apply: ct_imp.
  - apply: ct_forall_nat => i iL Hi.
    exact (ct_imp _ _ _ _ (sub_nat_lt_correspondence _ _ _ _ Hi Hp) (sub_nat_le_correspondence _ _ _ _ (HFn _ _ Hi) (HFn _ _ (cs_succ _ _ Hi)))).
  - apply: sub_nat_eq_correspondence.
    + exact (ct_sub_rel _ _ _ _ (HFn _ _ Hp) (HFn _ _ (sub_nat_rel_canonical 0))).
    + apply: (cs_ico _ _ _ _ _ _ (sub_nat_rel_canonical 0) Hp) => k kL Hk.
      exact (ct_sub_rel _ _ _ _ (HFn _ _ (cs_succ _ _ Hk)) (HFn _ _ Hk)).
Qed.

Definition src_leq_sum_sub_uniq (T : eqType) : Prop := ltac:(type_of_term (@sum.leq_sum_sub_uniq T)).
Definition tgt_leq_sum_sub_uniq (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Sum_leq_sum_sub_uniq T (ct_decidable_eq T))).
Theorem leq_sum_sub_uniq_correspondence (T : eqType) : PropSPropRel (src_leq_sum_sub_uniq T) (tgt_leq_sum_sub_uniq T).
Proof.
  unfold src_leq_sum_sub_uniq, tgt_leq_sum_sub_uniq.
  apply: cs_forall_list => r1 R1 H1. apply: cs_forall_list => r2 R2 H2. apply: cs_forall_tfun => FR FL HF.
  apply: ct_imp; first exact (cs_uniq T r1 R1 H1).
  apply: ct_imp.
  - rewrite /sub_mem. apply: ct_forall_identity => x. exact (ct_imp _ _ _ _ (cs_mem T x r1 R1 H1) (cs_mem T x r2 R2 H2)).
  - exact (sub_nat_le_correspondence _ _ _ _ (cs_sumSeq_rel T FR FL HF r1 R1 H1) (cs_sumSeq_rel T FR FL HF r2 R2 H2)).
Qed.
