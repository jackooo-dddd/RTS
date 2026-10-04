From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.util.bigcat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicBigcat.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicBigcatBase ClassicBigcatList.

Module I := ImportedClassicBigcat.
Local Open Scope nat_scope.

(** Certificates for [classic/util/bigcat.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: elements of an [eqType] identified (its Lean [DecidableEq] the
    eqType's decision procedure); natural numbers by [SubNatRel]; ordinals and
    [Fin] by their values ([CoOrdRel], from the accepted ord_quantifier
    certificate); sequences elementwise ([ClListRel]); ordinal-indexed
    families pointwise on related ordinals; all with two-way totals.

    Computation: [\big[op/idx]_(i < n) F i] is a right fold of the value family
    [co_fam F] over [iota 0 n] ([co_big_ord], MathComp [big_cons],
    [val_enum_ord]); the Lean [bigCatFin f] and [∑ i : Fin n, F i] are rewritten
    by the exported kernel-checked equations [ClassicBigcatInterface.bigCatFin_range']
    / [fin_sum_range'] (used as propositional equations) into folds over
    [List.range' 0 n] of the [dite] family [co_tfam]; the families are related
    pointwise ([co_fam_related]) and the folds structurally.

    Statements: the source side is the exact elaborated type of the pinned
    lemma (via [type of]; the source proof is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Ordinals (from the accepted ord_quantifier certificate) *)

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


Lemma co_forall_ord nR nL (Hn : SubNatRel nR nL) (PR : 'I_nR -> Prop) (PL : Fin nL -> SProp) :
  (forall oR oL, CoOrdRel nR nL oR oL -> PropSPropRel (PR oR) (PL oL)) -> PropSPropRel (forall o, PR o) (forall o, PL o).
Proof.
  exact (co_forall_cover_sprop _ _ (CoOrdRel nR nL) (co_ord_to_fin nR nL Hn) (co_fin_to_ord nR nL Hn)
    (co_ord_canonical nR nL Hn) (co_ord_surjective nR nL Hn) PR PL).
Qed.

Lemma co_exists_ord nR nL (Hn : SubNatRel nR nL) (PR : 'I_nR -> Prop) (PL : Fin nL -> SProp) :
  (forall oR oL, CoOrdRel nR nL oR oL -> PropSPropRel (PR oR) (PL oL)) -> PropSPropRel (exists o, PR o) (I.Exists (Fin nL) PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [o Ho]. exact (I.Exists_intro _ PL _ (prop_to_sprop _ _ (H _ _ (co_ord_canonical nR nL Hn o)) Ho)).
  - intros [oL Ho]. apply strictly_inhabits. exists (co_fin_to_ord nR nL Hn oL).
    exact (sprop_to_prop _ _ (H _ _ (co_ord_surjective nR nL Hn oL)) Ho).
Qed.

Lemma co_ord_eq_rel nR nL o1 o2 l1 l2 : CoOrdRel nR nL o1 l1 -> CoOrdRel nR nL o2 l2 ->
  PropSPropRel (Logic.eq o1 o2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. apply prop_sprop_rel_intro.
  - intros ->. rewrite (co_fin_rel_eq _ _ _ _ _ H1 H2). exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := imported_eq_to_coq_eq _ _ E. subst l2. exact (co_ord_eq _ _ _ _ _ H1 H2).
Qed.

(** Ordinal-indexed families of sequences. *)
Definition CoFamRel nR nL (T : Type) (fR : 'I_nR -> seq T) (fL : Fin nL -> I.List T) : SProp :=
  forall oR oL, CoOrdRel nR nL oR oL -> ClListRel cid (fR oR) (fL oL).

Lemma co_forall_fam nR nL (Hn : SubNatRel nR nL) (T : Type) (PR : ('I_nR -> seq T) -> Prop) (PL : (Fin nL -> I.List T) -> SProp) :
  (forall fR fL, CoFamRel nR nL T fR fL -> PropSPropRel (PR fR) (PL fL)) -> PropSPropRel (forall f, PR f) (forall f, PL f).
Proof.
  have Hcd : forall l : I.List T, Logic.eq (cl_map cid (cl_unmap cid l)) l := cl_map_unmap cid cid (fun _ => Logic.eq_refl _).
  apply (co_forall_cover_sprop _ _ (CoFamRel nR nL T)
    (fun fR oL => cl_map cid (fR (co_fin_to_ord nR nL Hn oL))) (fun fL oR => cl_unmap cid (fL (co_ord_to_fin nR nL Hn oR)))).
  - intros fR oR oL Ho. rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)). exact (@Lean.eq_refl _ _).
  - intros fL oR oL Ho. rewrite -(co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho).
    apply: coq_eq_to_imported_eq. exact (Hcd _).
Qed.

(* ------------------------------------------------------------------ *)
(** * Big operators over ordinals as folds over [iota] *)

Definition co_fam {nR : nat} {A : Type} (F : 'I_nR -> A) (d : A) (k : nat) : A :=
  if insub k is Some o then F o else d.

Definition co_tfam {nL : Lean.Nat} {B : Type} (F : Fin nL -> B) (d : B) (k : Lean.Nat) : B :=
  I.dite B (I.LT_lt_inst1 Lean.Nat I.instLTNat k nL) (I.Nat_decLt k nL) (fun h => F (Fin_mk nL k h)) (fun _ => d).

Lemma co_fam_related (nR : nat) {A B : Type} (c : A -> B) (FR : 'I_nR -> A) (FL : Fin (sub_nat_to_imported nR) -> B) (dA : A)
    (HF : forall o oL, CoOrdRel nR (sub_nat_to_imported nR) o oL -> Logic.eq (FL oL) (c (FR o))) :
  forall k, Logic.eq (co_tfam FL (c dA) (sub_nat_to_imported k)) (c (co_fam FR dA k)).
Proof.
  intro k. unfold co_tfam, co_fam.
  have Hlt := sub_nat_lt_correspondence k _ nR _ (sub_nat_rel_canonical k) (sub_nat_rel_canonical nR).
  destruct (I.Nat_decLt (sub_nat_to_imported k) (sub_nat_to_imported nR)) as [h|h]; cbn.
  - have Hge : Logic.eq (k < nR) false.
    { apply/negbTE/negP. move=> Hsrc. exact (interpret_strict _ (ct_target_false_to_strict (h (prop_to_sprop _ _ Hlt Hsrc)))). }
    by rewrite (@insubF _ _ _ k Hge).
  - have Hsrc : k < nR := sprop_to_prop _ _ Hlt h.
    rewrite (insubT (fun x => x < nR) Hsrc) /=. apply: HF. exact (sub_nat_rel_canonical k).
Qed.

Lemma co_big_seq_ord {R : Type} (op : R -> R -> R) (idx : R) nR (F : 'I_nR -> R) (d : R) (s : seq 'I_nR) :
  Logic.eq (\big[op/idx]_(i <- s) F i) (foldr op idx (map (co_fam F d) (map (@nat_of_ord nR) s))).
Proof. elim: s => [|o s IH]; first by rewrite big_nil. by rewrite big_cons IH /= /co_fam valK. Qed.

Lemma co_index_enum_vals nR : Logic.eq (map (@nat_of_ord nR) (index_enum 'I_nR)) (iota 0 nR).
Proof.
  rewrite -val_enum_ord -deprecated_filter_index_enum.
  congr map. by apply/esym/all_filterP/allP.
Qed.

Lemma co_big_ord {R : Type} (op : R -> R -> R) (idx : R) nR (F : 'I_nR -> R) (d : R) :
  Logic.eq (\big[op/idx]_(i < nR) F i) (foldr op idx (map (co_fam F d) (iota 0 nR))).
Proof. rewrite -co_index_enum_vals -co_big_seq_ord. by []. Qed.

Fixpoint co_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (co_natl s') end.

Definition co_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma co_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) co_one) (co_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) co_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (co_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma co_map_inst1 {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (co_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (co_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma co_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma co_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma co_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cl_cat. reflexivity.
Qed.

Lemma co_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))
                        (I.List_map_inst3 Lean.Nat Lean.Nat f (co_natl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))
              (I.List_map_inst3 Lean.Nat Lean.Nat f (co_natl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma co_bigcat_rel (T : Type) nR nL (Hn : SubNatRel nR nL) fR fL (Hf : CoFamRel nR nL T fR fL) :
  ClListRel cid (\big[cat/[::]]_(i < nR) fR i) (I.Prosa_Util_Bigcat_bigCatFin T nL fL).
Proof.
  have E := co_nat_logic _ _ Hn. subst nL. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicBigcatInterface_bigCatFin_range' T (sub_nat_to_imported nR) fL)).
  rewrite (co_big_ord _ _ _ _ [::]).
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (co_iota_range nR 0) co_map_inst1.
  rewrite (co_cl_map_ext _ (fun k => cl_map cid (co_fam fR [::] k))
             (co_fam_related nR (cl_map cid) fR fL [::] (fun o oL Ho => cl_list_logic _ _ _ (Hf o oL Ho)))).
  rewrite (co_cl_map_comp (co_fam fR [::]) (cl_map cid)) co_flatten.
  have -> : forall L : seq (seq T), Logic.eq (foldr cat [::] L) (flatten L) by [].
  reflexivity.
Qed.

Lemma co_sum_rel nR nL (Hn : SubNatRel nR nL) (FR : 'I_nR -> nat) (FL : Fin nL -> Lean.Nat)
    (HF : forall o oL, CoOrdRel nR nL o oL -> SubNatRel (FR o) (FL oL)) :
  SubNatRel (\sum_(i < nR) FR i)
    (I.Finset_sum_inst3 (Fin nL) Lean.Nat I.Nat_instAddCommMonoid (I.Finset_univ_inst1 (Fin nL) (I.Fin_fintype nL)) (fun i => FL i)).
Proof.
  have E := co_nat_logic _ _ Hn. subst nL. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicBigcatInterface_fin_sum_range' (sub_nat_to_imported nR) FL)).
  rewrite (co_big_ord _ _ _ _ 0).
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (co_iota_range nR 0).
  apply: co_foldr_add => k.
  exact (co_fam_related nR sub_nat_to_imported FR FL 0 (fun o oL Ho => cl_nat_logic _ _ (HF o oL Ho)) k).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Lemma cb_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cb_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cb_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Definition src_mem_bigcat_ord (T : eqType) : Prop := ltac:(type_of_term (@bigcat.mem_bigcat_ord T)).
Definition tgt_mem_bigcat_ord (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Bigcat_mem_bigcat_ord T (ct_decidable_eq T))).
Theorem mem_bigcat_ord_correspondence (T : eqType) : PropSPropRel (src_mem_bigcat_ord T) (tgt_mem_bigcat_ord T).
Proof.
  unfold src_mem_bigcat_ord, tgt_mem_bigcat_ord.
  apply: ct_forall_identity => x. apply: ct_forall_nat => nR nL Hn.
  apply: (co_forall_ord nR nL Hn) => j jL Hj. apply: (co_forall_fam nR nL Hn T) => fR fL Hf.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hj Hn).
  exact (ct_imp _ _ _ _ (cb_mem T x _ _ (Hf _ _ Hj)) (cb_mem T x _ _ (co_bigcat_rel T nR nL Hn fR fL Hf))).
Qed.

Definition src_mem_bigcat_ord_exists (T : eqType) : Prop := ltac:(type_of_term (@mem_bigcat_ord_exists T)).
Definition tgt_mem_bigcat_ord_exists (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Bigcat_mem_bigcat_ord_exists T (ct_decidable_eq T))).
Theorem mem_bigcat_ord_exists_correspondence (T : eqType) :
  PropSPropRel (src_mem_bigcat_ord_exists T) (tgt_mem_bigcat_ord_exists T).
Proof.
  unfold src_mem_bigcat_ord_exists, tgt_mem_bigcat_ord_exists.
  apply: ct_forall_identity => x. apply: ct_forall_nat => nR nL Hn. apply: (co_forall_fam nR nL Hn T) => fR fL Hf.
  apply: ct_imp; first exact (cb_mem T x _ _ (co_bigcat_rel T nR nL Hn fR fL Hf)).
  apply: (co_exists_ord nR nL Hn) => i iL Hi. exact (cb_mem T x _ _ (Hf _ _ Hi)).
Qed.

Definition src_bigcat_ord_uniq (T : eqType) : Prop := ltac:(type_of_term (@bigcat_ord_uniq T)).
Definition tgt_bigcat_ord_uniq (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Bigcat_bigcat_ord_uniq T (ct_decidable_eq T))).
Theorem bigcat_ord_uniq_correspondence (T : eqType) : PropSPropRel (src_bigcat_ord_uniq T) (tgt_bigcat_ord_uniq T).
Proof.
  unfold src_bigcat_ord_uniq, tgt_bigcat_ord_uniq.
  apply: ct_forall_nat => nR nL Hn. apply: (co_forall_fam nR nL Hn T) => fR fL Hf.
  apply: ct_imp.
  - apply: (co_forall_ord nR nL Hn) => i iL Hi. exact (cb_uniq T _ _ (Hf _ _ Hi)).
  - apply: ct_imp; last exact (cb_uniq T _ _ (co_bigcat_rel T nR nL Hn fR fL Hf)).
    apply: ct_forall_identity => x.
    apply: (co_forall_ord nR nL Hn) => i1 i1L H1. apply: (co_forall_ord nR nL Hn) => i2 i2L H2.
    apply: ct_imp; first exact (cb_mem T x _ _ (Hf _ _ H1)).
    exact (ct_imp _ _ _ _ (cb_mem T x _ _ (Hf _ _ H2)) (co_ord_eq_rel _ _ _ _ _ _ H1 H2)).
Qed.

Lemma cb_map_rel (T T' : Type) (g : T -> T') s sL : ClListRel cid s sL -> ClListRel (B := T') cid (map g s) (I.List_map T T' g sL).
Proof. intro H. destruct H. exact (coq_eq_to_imported_eq _ _ (cl_map_op cid cid g g (fun _ => Logic.eq_refl _) s)). Qed.

Definition src_map_bigcat_ord : Prop := ltac:(type_of_term @map_bigcat_ord).
Definition tgt_map_bigcat_ord : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Bigcat_map_bigcat_ord).
Theorem map_bigcat_ord_correspondence : PropSPropRel src_map_bigcat_ord tgt_map_bigcat_ord.
Proof.
  unfold src_map_bigcat_ord, tgt_map_bigcat_ord.
  apply: ct_forall_identity => T. apply: ct_forall_identity => T'.
  apply: ct_forall_nat => nR nL Hn. apply: (co_forall_fam nR nL Hn T) => fR fL Hf. apply: ct_forall_identity => g.
  have Hl := cb_map_rel T T' g _ _ (co_bigcat_rel T nR nL Hn fR fL Hf).
  have Hr := co_bigcat_rel T' nR nL Hn (fun i => map g (fR i)) (fun i => I.List_map T T' g (fL i))
               (fun o oL Ho => cb_map_rel T T' g _ _ (Hf o oL Ho)).
  rewrite (cl_list_logic _ _ _ Hl) (cl_list_logic _ _ _ Hr). apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := f_equal (cl_unmap cid) (imported_eq_to_coq_eq _ _ E).
    by rewrite !(cl_unmap_map cid cid (fun _ => Logic.eq_refl _)) in E'.
Qed.

Definition src_size_bigcat_ord : Prop := ltac:(type_of_term @size_bigcat_ord).
Definition tgt_size_bigcat_ord : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Bigcat_size_bigcat_ord).
Theorem size_bigcat_ord_correspondence : PropSPropRel src_size_bigcat_ord tgt_size_bigcat_ord.
Proof.
  unfold src_size_bigcat_ord, tgt_size_bigcat_ord.
  apply: ct_forall_identity => T. apply: ct_forall_nat => nR nL Hn. apply: (co_forall_fam nR nL Hn T) => fR fL Hf.
  apply: sub_nat_eq_correspondence; first exact (cb_size T _ _ (co_bigcat_rel T nR nL Hn fR fL Hf)).
  apply: (co_sum_rel nR nL Hn) => o oL Ho. exact (cb_size T _ _ (Hf _ _ Ho)).
Qed.

Definition src_size_bigcat_ord_max : Prop := ltac:(type_of_term @size_bigcat_ord_max).
Definition tgt_size_bigcat_ord_max : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Bigcat_size_bigcat_ord_max).
Theorem size_bigcat_ord_max_correspondence : PropSPropRel src_size_bigcat_ord_max tgt_size_bigcat_ord_max.
Proof.
  unfold src_size_bigcat_ord_max, tgt_size_bigcat_ord_max.
  apply: ct_forall_identity => T. apply: ct_forall_nat => nR nL Hn. apply: (co_forall_fam nR nL Hn T) => fR fL Hf.
  apply: ct_forall_nat => mR mL Hm.
  apply: ct_imp.
  - apply: (co_forall_ord nR nL Hn) => o oL Ho. exact (sub_nat_le_correspondence _ _ _ _ (cb_size T _ _ (Hf _ _ Ho)) Hm).
  - exact (sub_nat_le_correspondence _ _ _ _ (cb_size T _ _ (co_bigcat_rel T nR nL Hn fR fL Hf))
             (sub_mul_correspondence _ _ _ _ Hm Hn)).
Qed.
