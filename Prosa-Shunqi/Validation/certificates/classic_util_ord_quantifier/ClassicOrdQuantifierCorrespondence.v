From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
From prosa Require Import classic.util.ord_quantifier.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicOrdQuantifier.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicOrdQuantifierBase.

Module I := ImportedClassicOrdQuantifier.
Local Open Scope nat_scope.

(** Certificates for [classic/util/ord_quantifier.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: natural numbers by the accepted [SubNatRel]; ordinals ['I_nR] and
    Lean [Fin nL] by their values ([CoOrdRel]); Boolean predicates on ordinals
    pointwise on related ordinals; all with two-way totals.

    Computation: MathComp's [[exists x in 'I_n, P x]] / [[forall x in 'I_n, P x]]
    are rewritten (MathComp [existsP]/[hasP]/[forallP]/[allP]) into [has] /
    [all] over [iota 0 n]; the Lean [List.any]/[List.all] over [List.finRange n]
    are rewritten by the exported kernel-checked Lean equations
    [ClassicOrdQuantifierInterface.finRange_any]/[finRange_all] (used as
    propositional equations) into searches over [List.range' 0 n]; the two are
    related by structural induction (as for the accepted [classic/util/pick.v]).
    [widen_ord]/[Fin.castSucc] and [ord_max]/[Fin.last] preserve values. *)

Ltac type_of_term t := let T := type of t in exact T.

Lemma co_nat_logic nR nL : SubNatRel nR nL -> Logic.eq nL (sub_nat_to_imported nR).
Proof. intro H. exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ H)). Qed.

Lemma co_nat_input nR nL : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof. intro H. rewrite (co_nat_logic _ _ H). exact (sub_nat_rocq_roundtrip nR). Qed.

(* ------------------------------------------------------------------ *)
(** * Ordinals *)

Definition CoOrdRel (nR : nat) (nL : Lean.Nat) (oR : 'I_nR) (oL : Fin nL) : SProp :=
  SubNatRel (nat_of_ord oR) (I.Fin_val nL oL).

Definition co_ord_to_fin nR nL (Hn : SubNatRel nR nL) (oR : 'I_nR) : Fin nL :=
  Fin_mk nL (sub_nat_to_imported (nat_of_ord oR))
    (prop_to_sprop _ _ (sub_nat_lt_correspondence (nat_of_ord oR) _ nR nL (sub_nat_rel_canonical _) Hn) (ltn_ord oR)).

Definition co_fin_to_ord nR nL (Hn : SubNatRel nR nL) (oL : Fin nL) : 'I_nR :=
  @Ordinal nR (sub_nat_to_rocq (I.Fin_val nL oL))
    (sprop_to_prop _ _ (sub_nat_lt_correspondence _ (I.Fin_val nL oL) nR nL
       (sub_nat_rel_surjective (I.Fin_val nL oL)) Hn) (I.Fin_isLt nL oL)).

Lemma co_ord_canonical nR nL (Hn : SubNatRel nR nL) oR : CoOrdRel nR nL oR (co_ord_to_fin nR nL Hn oR).
Proof. exact (sub_nat_rel_canonical _). Qed.

Lemma co_ord_surjective nR nL (Hn : SubNatRel nR nL) oL : CoOrdRel nR nL (co_fin_to_ord nR nL Hn oL) oL.
Proof. exact (sub_nat_rel_surjective _). Qed.

Lemma co_ord_eq nR nL oR pR oL : CoOrdRel nR nL oR oL -> CoOrdRel nR nL pR oL -> Logic.eq oR pR.
Proof. intros H1 H2. apply: ord_inj. rewrite -(co_nat_input _ _ H1) -(co_nat_input _ _ H2). reflexivity. Qed.

Lemma co_fin_eq nL (a b : Fin nL) : Logic.eq (I.Fin_val nL a) (I.Fin_val nL b) -> Logic.eq a b.
Proof. destruct a as [va pa], b as [vb pb]. cbn. intro E. destruct E. reflexivity. Qed.

Lemma co_fin_rel_eq nR nL oR oL pL : CoOrdRel nR nL oR oL -> CoOrdRel nR nL oR pL -> Logic.eq oL pL.
Proof.
  intros H1 H2. apply: co_fin_eq.
  rewrite -(imported_eq_to_coq_eq _ _ H1) -(imported_eq_to_coq_eq _ _ H2). reflexivity.
Qed.

Definition CoOrdPredRel nR nL (PR : 'I_nR -> bool) (PL : Fin nL -> I.Bool) : SProp :=
  forall oR oL, CoOrdRel nR nL oR oL -> CtBoolRel (PR oR) (PL oL).

Lemma co_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma co_forall_ord_pred nR nL (Hn : SubNatRel nR nL) (PR : pred 'I_nR -> Prop) (PL : (Fin nL -> I.Bool) -> SProp) :
  (forall pR pL, CoOrdPredRel nR nL pR pL -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  apply (co_forall_cover_sprop _ _ (CoOrdPredRel nR nL)
    (fun pR oL => ct_b2l (pR (co_fin_to_ord nR nL Hn oL))) (fun pL oR => ct_l2b (pL (co_ord_to_fin nR nL Hn oR)))).
  - intros pR oR oL Ho. rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)). exact (ct_bool_canonical _).
  - intros pL oR oL Ho. rewrite -(co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho). exact (ct_bool_surjective _).
Qed.

(* ------------------------------------------------------------------ *)
(** * Searches over [iota] and [List.range'] *)

Definition co_ord_family (nR : nat) (Q : 'I_nR -> bool) (dflt : bool) (k : nat) : bool :=
  if insub k is Some o then Q o else dflt.

Definition co_target_family (nL : Lean.Nat) (q : Fin nL -> I.Bool) (dflt : I.Bool) (k : Lean.Nat) : I.Bool :=
  I.dite I.Bool (I.LT_lt_inst1 Lean.Nat I.instLTNat k nL) (I.Nat_decLt k nL) (fun h => q (Fin_mk nL k h)) (fun _ => dflt).

Lemma co_family_related (nR : nat) (Q : 'I_nR -> bool) (q : Fin (sub_nat_to_imported nR) -> I.Bool)
    (HQ : CoOrdPredRel nR (sub_nat_to_imported nR) Q q) (dflt : bool) :
  forall kR, Logic.eq (co_target_family (sub_nat_to_imported nR) q (ct_b2l dflt) (sub_nat_to_imported kR))
                      (ct_b2l (co_ord_family nR Q dflt kR)).
Proof.
  intro kR. unfold co_target_family, co_ord_family.
  have Hlt := sub_nat_lt_correspondence kR _ nR _ (sub_nat_rel_canonical kR) (sub_nat_rel_canonical nR).
  destruct (I.Nat_decLt (sub_nat_to_imported kR) (sub_nat_to_imported nR)) as [h|h]; cbn.
  - have Hge : Logic.eq (kR < nR) false.
    { apply/negbTE/negP. move=> Hsrc. exact (interpret_strict _ (ct_target_false_to_strict (h (prop_to_sprop _ _ Hlt Hsrc)))). }
    by rewrite (@insubF _ _ _ kR Hge).
  - have Hsrc : kR < nR := sprop_to_prop _ _ Hlt h.
    rewrite (insubT (fun x => x < nR) Hsrc) /=. apply: ct_bool_rel_logic. apply: HQ. exact (sub_nat_rel_canonical kR).
Qed.

Definition co_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma co_all_iota (fR : nat -> bool) (fL : Lean.Nat -> I.Bool)
    (Hf : forall kR, Logic.eq (fL (sub_nat_to_imported kR)) (ct_b2l (fR kR))) :
  forall nR sR, Logic.eq
    (I.List_all_inst1 Lean.Nat (I.List_range' (sub_nat_to_imported sR) (sub_nat_to_imported nR) co_one) fL)
    (ct_b2l (all fR (iota sR nR))).
Proof.
  elim => [|n IH] sR; first reflexivity.
  change (Logic.eq (I.Bool_and (fL (sub_nat_to_imported sR))
      (I.List_all_inst1 Lean.Nat (I.List_range' (sub_nat_to_imported (S sR)) (sub_nat_to_imported n) co_one) fL))
    (ct_b2l (fR sR && all fR (iota (S sR) n)))).
  rewrite Hf IH. by case: (fR sR).
Qed.

Lemma co_any_iota (fR : nat -> bool) (fL : Lean.Nat -> I.Bool)
    (Hf : forall kR, Logic.eq (fL (sub_nat_to_imported kR)) (ct_b2l (fR kR))) :
  forall nR sR, Logic.eq
    (I.List_any_inst1 Lean.Nat (I.List_range' (sub_nat_to_imported sR) (sub_nat_to_imported nR) co_one) fL)
    (ct_b2l (has fR (iota sR nR))).
Proof.
  elim => [|n IH] sR; first reflexivity.
  change (Logic.eq (I.Bool_or (fL (sub_nat_to_imported sR))
      (I.List_any_inst1 Lean.Nat (I.List_range' (sub_nat_to_imported (S sR)) (sub_nat_to_imported n) co_one) fL))
    (ct_b2l (fR sR || has fR (iota (S sR) n)))).
  rewrite Hf IH. by case: (fR sR).
Qed.

(** Source rewrites. *)
Lemma co_exists_iota (nR : nat) (Q : 'I_nR -> bool) :
  Logic.eq [exists x in 'I_nR, Q x] (has (co_ord_family nR Q false) (iota 0 nR)).
Proof.
  apply/existsP/hasP.
  - move=> [x /andP [_ Hx]]. exists (nat_of_ord x); first by rewrite mem_iota add0n ltn_ord.
    by rewrite /co_ord_family valK.
  - move=> [k Hk]. rewrite mem_iota add0n in Hk. move/andP: Hk => [_ Hk].
    rewrite /co_ord_family insubT => Hq. by exists (Ordinal Hk).
Qed.

Lemma co_forall_iota (nR : nat) (Q : 'I_nR -> bool) :
  Logic.eq [forall x in 'I_nR, Q x] (all (co_ord_family nR Q true) (iota 0 nR)).
Proof.
  apply/forallP/allP.
  - move=> H k. rewrite mem_iota add0n => /andP [_ Hk]. rewrite /co_ord_family insubT. exact: (implyP (H _)).
  - move=> H x. apply/implyP => _. have := H (nat_of_ord x). rewrite mem_iota add0n ltn_ord /co_ord_family valK. by apply.
Qed.

Lemma co_exists_rel nR nL (Hn : SubNatRel nR nL) Q q (HQ : CoOrdPredRel nR nL Q q) :
  CtBoolRel [exists x in 'I_nR, Q x] (I.List_any_inst1 (Fin nL) (I.List_finRange nL) q).
Proof.
  have E := co_nat_logic _ _ Hn. subst nL. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicOrdQuantifierInterface_finRange_any (sub_nat_to_imported nR) q)).
  rewrite co_exists_iota.
  exact (co_any_iota (co_ord_family nR Q false) (co_target_family (sub_nat_to_imported nR) q I.Bool_false)
           (co_family_related nR Q q HQ false) nR O).
Qed.

Lemma co_forall_rel nR nL (Hn : SubNatRel nR nL) Q q (HQ : CoOrdPredRel nR nL Q q) :
  CtBoolRel [forall x in 'I_nR, Q x] (I.List_all_inst1 (Fin nL) (I.List_finRange nL) q).
Proof.
  have E := co_nat_logic _ _ Hn. subst nL. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicOrdQuantifierInterface_finRange_all (sub_nat_to_imported nR) q)).
  rewrite co_forall_iota.
  exact (co_all_iota (co_ord_family nR Q true) (co_target_family (sub_nat_to_imported nR) q I.Bool_true)
           (co_family_related nR Q q HQ true) nR O).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Lemma co_succ nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL co_one).
Proof. intro H. have := sub_add_correspondence _ _ 1 _ H (sub_nat_rel_canonical 1). by rewrite addn1. Qed.

Lemma co_widen_rel nR nL (x : 'I_nR) (xL : Fin nL) : CoOrdRel nR nL x xL ->
  CoOrdRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL co_one)
    (widen_ord (leqnSn nR) x) (I.Fin_castSucc nL xL).
Proof. exact (fun H => H). Qed.

Lemma co_last_rel nR nL : SubNatRel nR nL ->
  CoOrdRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL co_one)
    ord_max (I.Fin_last nL).
Proof. exact (fun H => H). Qed.

Definition src_exists_ord0 : Prop := ltac:(type_of_term @exists_ord0).
Definition tgt_exists_ord0 : SProp := ltac:(type_of_term I.Prosa_Classic_Util_OrdQuantifier_exists_ord0).
Theorem exists_ord0_correspondence : PropSPropRel src_exists_ord0 tgt_exists_ord0.
Proof.
  unfold src_exists_ord0, tgt_exists_ord0.
  apply: (co_forall_ord_pred 0 _ (sub_nat_rel_canonical 0)) => PR PL HP.
  exact (ct_bool_eq _ _ false I.Bool_false (co_exists_rel 0 _ (sub_nat_rel_canonical 0) PR PL HP) (@Lean.eq_refl _ _)).
Qed.

Definition src_forall_ord0 : Prop := ltac:(type_of_term @forall_ord0).
Definition tgt_forall_ord0 : SProp := ltac:(type_of_term I.Prosa_Classic_Util_OrdQuantifier_forall_ord0).
Theorem forall_ord0_correspondence : PropSPropRel src_forall_ord0 tgt_forall_ord0.
Proof.
  unfold src_forall_ord0, tgt_forall_ord0.
  apply: (co_forall_ord_pred 0 _ (sub_nat_rel_canonical 0)) => PR PL HP.
  exact (ct_bool_truth _ _ (co_forall_rel 0 _ (sub_nat_rel_canonical 0) PR PL HP)).
Qed.

Definition src_exists_recr : Prop := ltac:(type_of_term @exists_recr).
Definition tgt_exists_recr : SProp := ltac:(type_of_term I.Prosa_Classic_Util_OrdQuantifier_exists_recr).
Theorem exists_recr_correspondence : PropSPropRel src_exists_recr tgt_exists_recr.
Proof.
  unfold src_exists_recr, tgt_exists_recr.
  apply: ct_forall_nat => nR nL Hn. have Hs := co_succ _ _ Hn.
  apply: (co_forall_ord_pred _ _ Hs) => PR PL HP.
  apply: ct_bool_eq; first exact (co_exists_rel _ _ Hs PR PL HP).
  apply: ct_bool_or; last exact (HP _ _ (co_last_rel _ _ Hn)).
  apply: (co_exists_rel _ _ Hn) => oR oL Ho. exact (HP _ _ (co_widen_rel _ _ _ _ Ho)).
Qed.

Definition src_forall_recr : Prop := ltac:(type_of_term @forall_recr).
Definition tgt_forall_recr : SProp := ltac:(type_of_term I.Prosa_Classic_Util_OrdQuantifier_forall_recr).
Theorem forall_recr_correspondence : PropSPropRel src_forall_recr tgt_forall_recr.
Proof.
  unfold src_forall_recr, tgt_forall_recr.
  apply: ct_forall_nat => nR nL Hn. have Hs := co_succ _ _ Hn.
  apply: (co_forall_ord_pred _ _ Hs) => PR PL HP.
  apply: ct_bool_eq; first exact (co_forall_rel _ _ Hs PR PL HP).
  apply: ct_bool_and; last exact (HP _ _ (co_last_rel _ _ Hn)).
  apply: (co_forall_rel _ _ Hn) => oR oL Ho. exact (HP _ _ (co_widen_rel _ _ _ _ Ho)).
Qed.
