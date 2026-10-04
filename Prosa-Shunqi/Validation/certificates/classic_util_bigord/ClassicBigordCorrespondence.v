From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.util.bigord.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicBigord.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicBigordBase.

Module I := ImportedClassicBigord.

(** Certificates for [classic/util/bigord.v] (ProsaBuddy classic, commit f692cb7).

    Inputs.  Type parameters, operations and identities are identified;
    natural numbers by the accepted [SubNatRel]; an ordinal ['I_nR] and a Lean
    [Fin nL] by their values ([CbOrdRel], as for the accepted multiprocessor
    processors); functions on ordinals / naturals pointwise on related
    arguments; sequences of ordinals elementwise ([CbOrdListRel]).  Every
    relation has two-way totals (used by the covers [cb_forall_*]).

    Computation.  [\big[op/idx]_(i <- r | P i) F i] is related to the accepted
    v0.6 helper [bigSeq idx op P F r] by structural induction on [r]
    ([cb_big_rel]).  MathComp's [index_enum 'I_n] and Lean's [List.finRange n]
    are related through their value lists [iota 0 n] / [List.range' 0 n]
    (MathComp [val_enum_ord]; exported kernel-checked Lean equation
    [ClassicBigordInterface.finRange_map_val], used as a propositional
    equation).

    Statements.  The source side is the exact elaborated type of the pinned
    lemma (via [type of]; the source proof is not used). *)

Ltac type_of_term t := let T := type of t in exact T.

Inductive CbTrue : SProp := cb_true_intro.
Inductive CbFalse : SProp := .

Lemma cb_nat_logic nR nL : SubNatRel nR nL -> Logic.eq nL (sub_nat_to_imported nR).
Proof. intro H. exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ H)). Qed.

Lemma cb_nat_input nR nL : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof. intro H. rewrite (cb_nat_logic _ _ H). exact (sub_nat_rocq_roundtrip nR). Qed.

(* ------------------------------------------------------------------ *)
(** * Ordinals *)

Definition CbOrdRel (nR : nat) (nL : Lean.Nat) (oR : 'I_nR) (oL : Fin nL) : SProp :=
  SubNatRel (nat_of_ord oR) (I.Fin_val nL oL).

Definition cb_ord_to_fin nR nL (Hn : SubNatRel nR nL) (oR : 'I_nR) : Fin nL :=
  Fin_mk nL (sub_nat_to_imported (nat_of_ord oR))
    (prop_to_sprop _ _ (sub_nat_lt_correspondence (nat_of_ord oR) _ nR nL (sub_nat_rel_canonical _) Hn)
       (ltn_ord oR)).

Definition cb_fin_to_ord nR nL (Hn : SubNatRel nR nL) (oL : Fin nL) : 'I_nR :=
  @Ordinal nR (sub_nat_to_rocq (I.Fin_val nL oL))
    (sprop_to_prop _ _ (sub_nat_lt_correspondence _ (I.Fin_val nL oL) nR nL
       (sub_nat_rel_surjective (I.Fin_val nL oL)) Hn) (I.Fin_isLt nL oL)).

Lemma cb_ord_canonical nR nL (Hn : SubNatRel nR nL) oR : CbOrdRel nR nL oR (cb_ord_to_fin nR nL Hn oR).
Proof. exact (sub_nat_rel_canonical _). Qed.

Lemma cb_ord_surjective nR nL (Hn : SubNatRel nR nL) oL : CbOrdRel nR nL (cb_fin_to_ord nR nL Hn oL) oL.
Proof. exact (sub_nat_rel_surjective _). Qed.

(** Related ordinals are determined by each other. *)
Lemma cb_ord_eq nR nL oR pR oL : CbOrdRel nR nL oR oL -> CbOrdRel nR nL pR oL -> Logic.eq oR pR.
Proof.
  intros H1 H2. apply: ord_inj. rewrite -(cb_nat_input _ _ H1) -(cb_nat_input _ _ H2). reflexivity.
Qed.

Lemma cb_fin_eq nL (a b : Fin nL) : Logic.eq (I.Fin_val nL a) (I.Fin_val nL b) -> Logic.eq a b.
Proof. destruct a as [va pa], b as [vb pb]. cbn. intro E. destruct E. reflexivity. Qed.

Lemma cb_fin_rel_eq nR nL oR oL pL : CbOrdRel nR nL oR oL -> CbOrdRel nR nL oR pL -> Logic.eq oL pL.
Proof.
  intros H1 H2. apply: cb_fin_eq.
  rewrite -(imported_eq_to_coq_eq _ _ H1) -(imported_eq_to_coq_eq _ _ H2). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * [fun_ord_to_nat] *)

Lemma cb_fon_case_lt nR T (x0 : T) (f : 'I_nR -> T) x (b : bool) (e : (x < nR)%nat = b) (H : (x < nR)%nat) :
  (if b as b0 return (x < nR)%nat = b0 -> T then fun LT => f (Ordinal LT) else fun _ => x0) e = f (Ordinal H).
Proof. destruct b; last by rewrite H in e. by congr f; apply: val_inj. Qed.

Lemma cb_fon_case_ge nR T (x0 : T) (f : 'I_nR -> T) x (b : bool) (e : (x < nR)%nat = b) (H : ~~ (x < nR)%nat) :
  (if b as b0 return (x < nR)%nat = b0 -> T then fun LT => f (Ordinal LT) else fun _ => x0) e = x0.
Proof. destruct b; last by []. by rewrite e in H. Qed.

Theorem fun_ord_to_nat_correspondence nR nL (Hn : SubNatRel nR nL) (T : Type) (x0 : T)
    (fR : 'I_nR -> T) (fL : Fin nL -> T)
    (Hf : forall oR oL, CbOrdRel nR nL oR oL -> Logic.eq (fR oR) (fL oL))
    xR xL (Hx : SubNatRel xR xL) :
  Logic.eq (@fun_ord_to_nat nR T x0 fR xR) (I.Prosa_Classic_Util_Bigord_fun_ord_to_nat nL T x0 fL xL).
Proof.
  have Hlt := sub_nat_lt_correspondence _ _ _ _ Hx Hn.
  unfold I.Prosa_Classic_Util_Bigord_fun_ord_to_nat.
  destruct (I.Nat_decLt xL nL) as [h|h]; cbn.
  - have Hge : ~~ (xR < nR)%nat.
    { apply/negP => Hs. exact (interpret_strict _ (ct_target_false_to_strict (h (prop_to_sprop _ _ Hlt Hs)))). }
    exact (cb_fon_case_ge nR T x0 fR xR (xR < nR)%nat erefl Hge).
  - have Hs : (xR < nR)%nat := sprop_to_prop _ _ Hlt h.
    refine (Logic.eq_trans (cb_fon_case_lt nR T x0 fR xR (xR < nR)%nat erefl Hs) _).
    apply: Hf. exact Hx.
Qed.

(* ------------------------------------------------------------------ *)
(** * Sequences of ordinals and natural numbers *)

Fixpoint CbOrdListRel nR nL (rR : seq 'I_nR) (rL : I.List_inst1 (Fin nL)) : SProp :=
  match rR, rL with
  | [::], I.List_nil_inst1 => CbTrue
  | xR :: rR', I.List_cons_inst1 xL rL' => And (CbOrdRel nR nL xR xL) (CbOrdListRel nR nL rR' rL')
  | _, _ => CbFalse
  end.

Fixpoint cb_ords_to_target nR nL (Hn : SubNatRel nR nL) (rR : seq 'I_nR) : I.List_inst1 (Fin nL) :=
  match rR with
  | [::] => I.List_nil_inst1 _
  | x :: r => I.List_cons_inst1 _ (cb_ord_to_fin nR nL Hn x) (cb_ords_to_target nR nL Hn r)
  end.

Fixpoint cb_ords_to_source nR nL (Hn : SubNatRel nR nL) (rL : I.List_inst1 (Fin nL)) : seq 'I_nR :=
  match rL with
  | I.List_nil_inst1 => [::]
  | I.List_cons_inst1 x r => cb_fin_to_ord nR nL Hn x :: cb_ords_to_source nR nL Hn r
  end.

Lemma cb_ords_canonical nR nL Hn rR : CbOrdListRel nR nL rR (cb_ords_to_target nR nL Hn rR).
Proof.
  induction rR as [|x r IH]; first exact cb_true_intro.
  exact (And_intro _ _ (cb_ord_canonical nR nL Hn x) IH).
Qed.

Lemma cb_ords_surjective nR nL Hn rL : CbOrdListRel nR nL (cb_ords_to_source nR nL Hn rL) rL.
Proof.
  induction rL as [|x r IH]; first exact cb_true_intro.
  exact (And_intro _ _ (cb_ord_surjective nR nL Hn x) IH).
Qed.

Fixpoint cb_natlist (l : seq nat) : I.List_inst1 Lean.Nat :=
  match l with
  | [::] => I.List_nil_inst1 _
  | x :: r => I.List_cons_inst1 _ (sub_nat_to_imported x) (cb_natlist r)
  end.

Definition cb_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cb_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cb_one) (cb_natlist (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cb_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cb_natlist (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cb_map_val_rel nR nL : forall (rR : seq 'I_nR) (rL : I.List_inst1 (Fin nL)),
  Logic.eq (I.List_map_inst3 (Fin nL) Lean.Nat (I.Fin_val nL) rL) (cb_natlist (map (@nat_of_ord nR) rR)) ->
  CbOrdListRel nR nL rR rL.
Proof.
  intro rR. induction rR as [|xR rR IH]; intros rL E; destruct rL as [|xL rL].
  - exact cb_true_intro.
  - change (Logic.eq (I.List_cons_inst1 _ (I.Fin_val nL xL) (I.List_map_inst3 (Fin nL) Lean.Nat (I.Fin_val nL) rL))
      (I.List_nil_inst1 _)) in E. have F : Logic.False by discriminate E. destruct F.
  - have F : Logic.False by discriminate E. destruct F.
  - change (Logic.eq (I.List_cons_inst1 _ (I.Fin_val nL xL) (I.List_map_inst3 (Fin nL) Lean.Nat (I.Fin_val nL) rL))
      (I.List_cons_inst1 _ (sub_nat_to_imported xR) (cb_natlist (map (@nat_of_ord nR) rR)))) in E.
    injection E as E1 E2. split.
    + exact (coq_eq_to_imported_eq _ _ (Logic.eq_sym E1)).
    + exact (IH _ E2).
Qed.

Lemma cb_index_enum_vals nR : Logic.eq (map (@nat_of_ord nR) (index_enum 'I_nR)) (iota 0 nR).
Proof.
  rewrite -val_enum_ord -deprecated_filter_index_enum.
  congr map. by apply/esym/all_filterP/allP.
Qed.

Lemma cb_index_enum_rel nR nL (Hn : SubNatRel nR nL) :
  CbOrdListRel nR nL (index_enum 'I_nR) (I.List_finRange nL).
Proof.
  have E := cb_nat_logic _ _ Hn. subst nL.
  apply: cb_map_val_rel.
  rewrite (imported_eq_to_coq_eq _ _
    (I.Prosa_Validation_ClassicBigordInterface_finRange_map_val (sub_nat_to_imported nR))).
  rewrite cb_index_enum_vals. exact (cb_iota_range nR O).
Qed.

(* ------------------------------------------------------------------ *)
(** * Big operators *)

Lemma cb_bigSeq_cons (T X : Type) idx op (P : X -> I.Bool) (F : X -> T) x xs :
  Logic.eq (I.Prosa_Util_Bigop_bigSeq_inst2 T X idx op P F (I.List_cons_inst1 X x xs))
    (match P x with
     | I.Bool_true => op (F x) (I.Prosa_Util_Bigop_bigSeq_inst2 T X idx op P F xs)
     | I.Bool_false => I.Prosa_Util_Bigop_bigSeq_inst2 T X idx op P F xs
     end).
Proof. cbn. destruct (P x); reflexivity. Qed.

Lemma cb_big_rel (T : Type) nR nL op (idx : T) (PR : 'I_nR -> bool) (PL : Fin nL -> I.Bool)
    (FR : 'I_nR -> T) (FL : Fin nL -> T)
    (HP : forall oR oL, CbOrdRel nR nL oR oL -> CtBoolRel (PR oR) (PL oL))
    (HF : forall oR oL, CbOrdRel nR nL oR oL -> Logic.eq (FR oR) (FL oL)) :
  forall rR rL, CbOrdListRel nR nL rR rL ->
  Logic.eq (\big[op/idx]_(i <- rR | PR i) FR i) (I.Prosa_Util_Bigop_bigSeq_inst2 T (Fin nL) idx op PL FL rL).
Proof.
  elim => [|xR rR IH] [|xL rL] H.
  - by rewrite big_nil.
  - destruct H.
  - destruct H.
  - destruct H as [Hx Hr]. rewrite big_cons cb_bigSeq_cons (ct_bool_rel_logic _ _ (HP _ _ Hx)) (IH _ Hr).
    case: (PR xR) => //=. by rewrite (HF _ _ Hx).
Qed.

(* ------------------------------------------------------------------ *)
(** * Covers *)

Lemma cb_forall_cover_prop (A B : Type) (Rel : A -> B -> Prop) (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma cb_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma cb_forall_ord nR nL (Hn : SubNatRel nR nL) (PR : 'I_nR -> Prop) (PL : Fin nL -> SProp) :
  (forall oR oL, CbOrdRel nR nL oR oL -> PropSPropRel (PR oR) (PL oL)) ->
  PropSPropRel (forall o, PR o) (forall o, PL o).
Proof.
  exact (cb_forall_cover_sprop _ _ (CbOrdRel nR nL) (cb_ord_to_fin nR nL Hn) (cb_fin_to_ord nR nL Hn)
    (cb_ord_canonical nR nL Hn) (cb_ord_surjective nR nL Hn) PR PL).
Qed.

Lemma cb_forall_ords nR nL (Hn : SubNatRel nR nL) (PR : seq 'I_nR -> Prop) (PL : I.List_inst1 (Fin nL) -> SProp) :
  (forall rR rL, CbOrdListRel nR nL rR rL -> PropSPropRel (PR rR) (PL rL)) ->
  PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cb_forall_cover_sprop _ _ (CbOrdListRel nR nL) (cb_ords_to_target nR nL Hn)
    (cb_ords_to_source nR nL Hn) (cb_ords_canonical nR nL Hn) (cb_ords_surjective nR nL Hn) PR PL).
Qed.

Definition CbOrdPredRel nR nL (PR : 'I_nR -> bool) (PL : Fin nL -> I.Bool) : SProp :=
  forall oR oL, CbOrdRel nR nL oR oL -> CtBoolRel (PR oR) (PL oL).

Lemma cb_forall_ord_pred nR nL (Hn : SubNatRel nR nL) (PR : pred 'I_nR -> Prop) (PL : (Fin nL -> I.Bool) -> SProp) :
  (forall pR pL, CbOrdPredRel nR nL pR pL -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  apply (cb_forall_cover_sprop _ _ (CbOrdPredRel nR nL)
    (fun pR oL => ct_b2l (pR (cb_fin_to_ord nR nL Hn oL))) (fun pL oR => ct_l2b (pL (cb_ord_to_fin nR nL Hn oR)))).
  - intros pR oR oL Ho. rewrite (cb_ord_eq _ _ _ _ _ Ho (cb_ord_surjective nR nL Hn oL)). exact (ct_bool_canonical _).
  - intros pL oR oL Ho. rewrite -(cb_fin_rel_eq _ _ _ _ _ (cb_ord_canonical nR nL Hn oR) Ho). exact (ct_bool_surjective _).
Qed.

Definition CbOrdFunRel nR nL (T : Type) (fR : 'I_nR -> T) (fL : Fin nL -> T) : Prop :=
  forall oR oL, CbOrdRel nR nL oR oL -> Logic.eq (fR oR) (fL oL).

Lemma cb_forall_ord_fun nR nL (Hn : SubNatRel nR nL) (T : Type) (PR : ('I_nR -> T) -> Prop)
    (PL : (Fin nL -> T) -> SProp) :
  (forall fR fL, CbOrdFunRel nR nL T fR fL -> PropSPropRel (PR fR) (PL fL)) ->
  PropSPropRel (forall f, PR f) (forall f, PL f).
Proof.
  apply (cb_forall_cover_prop _ _ (CbOrdFunRel nR nL T)
    (fun fR oL => fR (cb_fin_to_ord nR nL Hn oL)) (fun fL oR => fL (cb_ord_to_fin nR nL Hn oR))).
  - intros fR oR oL Ho. by rewrite (cb_ord_eq _ _ _ _ _ Ho (cb_ord_surjective nR nL Hn oL)).
  - intros fL oR oL Ho. by rewrite (cb_fin_rel_eq _ _ _ _ _ (cb_ord_canonical nR nL Hn oR) Ho).
Qed.

Definition CbNatFunRel (T : Type) (fR : nat -> T) (fL : Lean.Nat -> T) : Prop :=
  forall xR xL, SubNatRel xR xL -> Logic.eq (fR xR) (fL xL).

Lemma cb_forall_nat_fun (T : Type) (PR : (nat -> T) -> Prop) (PL : (Lean.Nat -> T) -> SProp) :
  (forall fR fL, CbNatFunRel T fR fL -> PropSPropRel (PR fR) (PL fL)) ->
  PropSPropRel (forall f, PR f) (forall f, PL f).
Proof.
  apply (cb_forall_cover_prop _ _ (CbNatFunRel T)
    (fun fR xL => fR (sub_nat_to_rocq xL)) (fun fL xR => fL (sub_nat_to_imported xR))).
  - intros fR xR xL Hx. by rewrite (cb_nat_input _ _ Hx).
  - intros fL xR xL Hx. by rewrite (cb_nat_logic _ _ Hx).
Qed.

Lemma cb_eq_T (T : Type) (aR aL bR bL : T) :
  Logic.eq aR aL -> Logic.eq bR bL -> PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros -> ->. apply prop_sprop_rel_intro.
  - exact (coq_eq_to_imported_eq _ _).
  - intro H. exact (strictly_inhabits (imported_eq_to_coq_eq _ _ H)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_eq_fun_ord_to_nat : Prop := ltac:(type_of_term @eq_fun_ord_to_nat).
Definition tgt_eq_fun_ord_to_nat : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Bigord_eq_fun_ord_to_nat).
Theorem eq_fun_ord_to_nat_correspondence : PropSPropRel src_eq_fun_ord_to_nat tgt_eq_fun_ord_to_nat.
Proof.
  unfold src_eq_fun_ord_to_nat, tgt_eq_fun_ord_to_nat.
  apply: ct_forall_nat => nR nL Hn. apply: ct_forall_identity => T. apply: ct_forall_identity => x0.
  apply: (cb_forall_ord_fun nR nL Hn T) => fR fL Hf. apply: (cb_forall_ord nR nL Hn) => xR xL Hx.
  apply: cb_eq_T; last exact (Hf _ _ Hx).
  exact (fun_ord_to_nat_correspondence nR nL Hn T x0 fR fL Hf _ _ Hx).
Qed.

Definition src_eq_bigr_ord : Prop := ltac:(type_of_term @eq_bigr_ord).
Definition tgt_eq_bigr_ord : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Bigord_eq_bigr_ord).
Theorem eq_bigr_ord_correspondence : PropSPropRel src_eq_bigr_ord tgt_eq_bigr_ord.
Proof.
  unfold src_eq_bigr_ord, tgt_eq_bigr_ord.
  apply: ct_forall_identity => T. apply: ct_forall_nat => nR nL Hn.
  apply: ct_forall_identity => op. apply: ct_forall_identity => idx.
  apply: (cb_forall_ords nR nL Hn) => rR rL Hr. apply: (cb_forall_ord_pred nR nL Hn) => PR PL HP.
  apply: (cb_forall_nat_fun T) => F1R F1L HF1. apply: (cb_forall_ord_fun nR nL Hn T) => F2R F2L HF2.
  apply: ct_imp.
  - apply: (cb_forall_ord nR nL Hn) => iR iL Hi.
    exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (HP _ _ Hi)) (cb_eq_T _ _ _ _ _ (HF1 _ _ Hi) (HF2 _ _ Hi))).
  - apply: cb_eq_T.
    + exact (cb_big_rel T nR nL op idx PR PL (fun i => F1R i) (fun i => F1L (I.Fin_val nL i)) HP
               (fun oR oL Ho => HF1 _ _ Ho) rR rL Hr).
    + exact (cb_big_rel T nR nL op idx PR PL F2R F2L HP HF2 rR rL Hr).
Qed.

Definition src_big_mkord_ord : Prop := ltac:(type_of_term @big_mkord_ord).
Definition tgt_big_mkord_ord : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Bigord_big_mkord_ord).
Theorem big_mkord_ord_correspondence : PropSPropRel src_big_mkord_ord tgt_big_mkord_ord.
Proof.
  unfold src_big_mkord_ord, tgt_big_mkord_ord.
  apply: ct_forall_identity => T. apply: ct_forall_nat => nR nL Hn.
  apply: ct_forall_identity => op. apply: ct_forall_identity => idx. apply: ct_forall_identity => x0.
  apply: (cb_forall_ord_pred nR nL Hn) => PR PL HP. apply: (cb_forall_ord_fun nR nL Hn T) => FR FL HF.
  have Hr := cb_index_enum_rel nR nL Hn.
  apply: cb_eq_T.
  - exact (cb_big_rel T nR nL op idx PR PL FR FL HP HF _ _ Hr).
  - apply: (cb_big_rel T nR nL op idx PR PL _ _ HP _ _ _ Hr) => oR oL Ho.
    exact (fun_ord_to_nat_correspondence nR nL Hn T x0 FR FL HF _ _ Ho).
Qed.
