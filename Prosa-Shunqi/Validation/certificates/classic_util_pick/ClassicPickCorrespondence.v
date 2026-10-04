From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
From prosa Require Import classic.util.pick.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicPick.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence.

Module I := ImportedClassicPick.

(** Certificates for [classic/util/pick.v] (ProsaBuddy classic, commit f692cb7).

    Inputs.  Natural numbers are related by the accepted [SubNatRel]; Booleans
    by [CpBoolRel] (constructor-wise); an ordinal ['I_nR] and a Lean [Fin nL] by
    their values ([CpOrdRel], as for the accepted multiprocessor processors);
    options of ordinals constructor-wise ([CpOptOrdRel]); Boolean predicates and
    relations pointwise on related arguments.  All carriers have two-way totals.

    Computation.  MathComp's [pick P] on ['I_n] is [ohead (enum P)] and
    [[forall j, P j]] quantifies over [enum 'I_n]; both are rewritten (by the
    MathComp lemmas [val_enum_ord], [forallP], [allP]) into searches over
    [iota 0 n].  The Lean translation searches [List.finRange n]; the exported,
    kernel-checked Lean equations of [ClassicPickInterface] ([default0_find?],
    [finRange_all]) rewrite those into searches over [List.range' 0 n]; the two
    searches are then related by structural induction.  The Lean equations are
    used as propositional equations (transport), never as definitional
    unfoldings.

    Statements.  The source side of each statement certificate is the exact
    elaborated type of the pinned source lemma (via [type of]; the source proof
    is not used), the target side the type of the imported Lean theorem; they
    are related by structural combinators over the related inputs. *)

Ltac type_of_term t := let T := type of t in exact T.

(* ------------------------------------------------------------------ *)
(** * Booleans *)

Definition cp_b2l (b : bool) : I.Bool := if b then I.Bool_true else I.Bool_false.
Definition cp_l2b (b : I.Bool) : bool :=
  match b with I.Bool_true => Datatypes.true | I.Bool_false => Datatypes.false end.

Definition CpBoolRel (bR : bool) (bL : I.Bool) : SProp := Lean.eq (cp_b2l bR) bL.

Lemma cp_bool_rel_canonical (b : bool) : CpBoolRel b (cp_b2l b).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma cp_bool_rel_surjective (b : I.Bool) : CpBoolRel (cp_l2b b) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma cp_bool_rel_logic bR bL : CpBoolRel bR bL -> Logic.eq bL (cp_b2l bR).
Proof. intro H. exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ H)). Qed.

Lemma cp_bool_l2b_b2l (b : bool) : Logic.eq (cp_l2b (cp_b2l b)) b.
Proof. by case: b. Qed.

Lemma cp_bool_b2l_l2b (b : I.Bool) : Logic.eq (cp_b2l (cp_l2b b)) b.
Proof. by case: b. Qed.

Lemma cp_b2l_and (a b : bool) : Logic.eq (cp_b2l (a && b)) (I.Bool_and (cp_b2l a) (cp_b2l b)).
Proof. by case: a; case: b. Qed.

Lemma cp_b2l_or (a b : bool) : Logic.eq (cp_b2l (a || b)) (I.Bool_or (cp_b2l a) (cp_b2l b)).
Proof. by case: a; case: b. Qed.

Lemma cp_b2l_not (a : bool) : Logic.eq (cp_b2l (~~ a)) (I.Bool_not (cp_b2l a)).
Proof. by case: a. Qed.

Lemma cp_bool_truth bR bL :
  CpBoolRel bR bL -> PropSPropRel (is_true bR) (Lean.eq bL I.Bool_true).
Proof.
  intro H. have E := cp_bool_rel_logic _ _ H. subst bL.
  apply prop_sprop_rel_intro.
  - intro Ht. destruct bR; [exact (@Lean.eq_refl _ _) | discriminate Ht].
  - intro HL. apply strictly_inhabits. destruct bR; [reflexivity|].
    have E := imported_eq_to_coq_eq _ _ HL. discriminate E.
Qed.

(* ------------------------------------------------------------------ *)
(** * Natural numbers *)

Lemma cp_nat_logic nR nL : SubNatRel nR nL -> Logic.eq nL (sub_nat_to_imported nR).
Proof. intro H. exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ H)). Qed.

Lemma cp_nat_lt nR nL mR mL : SubNatRel nR nL -> SubNatRel mR mL ->
  PropSPropRel (is_true (ltn nR mR)) (I.LT_lt_inst1 Lean.Nat I.instLTNat nL mL).
Proof. intros Hn Hm. exact (sub_nat_lt_correspondence nR nL mR mL Hn Hm). Qed.

Lemma cp_nat_le nR nL mR mL : SubNatRel nR nL -> SubNatRel mR mL ->
  PropSPropRel (is_true (leq nR mR)) (I.LE_le_inst1 Lean.Nat I.instLENat nL mL).
Proof. intros Hn Hm. exact (sub_nat_le_correspondence nR nL mR mL Hn Hm). Qed.

(** Lean's [decide (a ≤ b)] against MathComp's [leq]. *)
Lemma cp_decide_le_related aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL ->
  CpBoolRel (leq aR bR)
    (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat aL bL) (I.Nat_decLe aL bL)).
Proof.
  intros Ha Hb. have Hle := cp_nat_le aR aL bR bL Ha Hb.
  destruct (I.Nat_decLe aL bL) as [h|h].
  - have Hf : Logic.eq (leq aR bR) false.
    { apply/negbTE/negP. move=> Hsrc.
      exact (match h (prop_to_sprop _ _ Hle Hsrc) return Logic.False with end). }
    rewrite Hf. exact (@Lean.eq_refl _ _).
  - have Hsrc : is_true (leq aR bR) := sprop_to_prop _ _ Hle h.
    rewrite Hsrc. exact (@Lean.eq_refl _ _).
Qed.

(* ------------------------------------------------------------------ *)
(** * Ordinals and [Fin] *)

Definition CpOrdRel (nR : nat) (nL : Lean.Nat) (oR : 'I_nR) (oL : Fin nL) : SProp :=
  SubNatRel (nat_of_ord oR) (I.Fin_val nL oL).

Definition cp_ord_to_fin (nR : nat) (nL : Lean.Nat) (Hn : SubNatRel nR nL) (oR : 'I_nR) : Fin nL :=
  Fin_mk nL (sub_nat_to_imported (nat_of_ord oR))
    (prop_to_sprop _ _ (cp_nat_lt (nat_of_ord oR) _ nR nL (sub_nat_rel_canonical _) Hn) (ltn_ord oR)).

Definition cp_fin_to_ord (nR : nat) (nL : Lean.Nat) (Hn : SubNatRel nR nL) (oL : Fin nL) : 'I_nR :=
  @Ordinal nR (sub_nat_to_rocq (I.Fin_val nL oL))
    (sprop_to_prop _ _
      (cp_nat_lt _ (I.Fin_val nL oL) nR nL (sub_nat_rel_surjective (I.Fin_val nL oL)) Hn)
      (I.Fin_isLt nL oL)).

Lemma cp_ord_rel_canonical nR nL (Hn : SubNatRel nR nL) (oR : 'I_nR) :
  CpOrdRel nR nL oR (cp_ord_to_fin nR nL Hn oR).
Proof. exact (sub_nat_rel_canonical _). Qed.

Lemma cp_ord_rel_surjective nR nL (Hn : SubNatRel nR nL) (oL : Fin nL) :
  CpOrdRel nR nL (cp_fin_to_ord nR nL Hn oL) oL.
Proof. exact (sub_nat_rel_surjective _). Qed.

(** The source family of a predicate on ['I_nR], read on all naturals. *)
Definition cp_ord_family (nR : nat) (Q : 'I_nR -> bool) (dflt : bool) (k : nat) : bool :=
  if insub k is Some o then Q o else dflt.

(** Its target counterpart, exactly as in the exported Lean equations. *)
Definition cp_target_family (nL : Lean.Nat) (q : Fin nL -> I.Bool) (dflt : I.Bool) (k : Lean.Nat) : I.Bool :=
  I.dite I.Bool (I.LT_lt_inst1 Lean.Nat I.instLTNat k nL) (I.Nat_decLt k nL)
    (fun h => q (Fin_mk nL k h)) (fun _ => dflt).

Lemma cp_family_related (nR : nat) (Q : 'I_nR -> bool) (q : Fin (sub_nat_to_imported nR) -> I.Bool)
    (HQ : forall oR oL, CpOrdRel nR (sub_nat_to_imported nR) oR oL -> CpBoolRel (Q oR) (q oL))
    (dflt : bool) :
  forall kR, Logic.eq (cp_target_family (sub_nat_to_imported nR) q (cp_b2l dflt) (sub_nat_to_imported kR))
                      (cp_b2l (cp_ord_family nR Q dflt kR)).
Proof.
  intro kR. unfold cp_target_family, cp_ord_family.
  have Hlt := cp_nat_lt kR _ nR _ (sub_nat_rel_canonical kR) (sub_nat_rel_canonical nR).
  destruct (I.Nat_decLt (sub_nat_to_imported kR) (sub_nat_to_imported nR)) as [h|h]; cbn.
  - have Hge : Logic.eq (ltn kR nR) false.
    { apply/negbTE/negP. move=> Hsrc.
      exact (match h (prop_to_sprop _ _ Hlt Hsrc) return Logic.False with end). }
    by rewrite (@insubF _ _ _ kR Hge).
  - have Hsrc : is_true (ltn kR nR) := sprop_to_prop _ _ Hlt h.
    rewrite (insubT (fun x => ltn x nR) Hsrc) /=.
    apply: cp_bool_rel_logic. apply: HQ. exact (sub_nat_rel_canonical kR).
Qed.

(* ------------------------------------------------------------------ *)
(** * Searches over [iota] and [List.range'] *)

Definition cp_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).
Definition cp_zero : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0).

Lemma cp_all_iota (fR : nat -> bool) (fL : Lean.Nat -> I.Bool)
    (Hf : forall kR, Logic.eq (fL (sub_nat_to_imported kR)) (cp_b2l (fR kR))) :
  forall nR sR, Logic.eq
    (I.List_all_inst1 Lean.Nat (I.List_range' (sub_nat_to_imported sR) (sub_nat_to_imported nR) cp_one) fL)
    (cp_b2l (all fR (iota sR nR))).
Proof.
  elim => [|n IH] sR; first reflexivity.
  change (Logic.eq (I.Bool_and (fL (sub_nat_to_imported sR))
      (I.List_all_inst1 Lean.Nat (I.List_range' (sub_nat_to_imported (S sR)) (sub_nat_to_imported n) cp_one) fL))
    (cp_b2l (fR sR && all fR (iota (S sR) n)))).
  by rewrite Hf IH cp_b2l_and.
Qed.

Lemma cp_find_iota (fR : nat -> bool) (fL : Lean.Nat -> I.Bool)
    (Hf : forall kR, Logic.eq (fL (sub_nat_to_imported kR)) (cp_b2l (fR kR))) :
  forall nR sR, Logic.eq
    (I.Option_getD_inst1 Lean.Nat
      (I.List_find__q_inst1 Lean.Nat fL (I.List_range' (sub_nat_to_imported sR) (sub_nat_to_imported nR) cp_one))
      cp_zero)
    (sub_nat_to_imported (odflt O (ohead (filter fR (iota sR nR))))).
Proof.
  elim => [|n IH] sR; first reflexivity.
  change (Logic.eq
    (I.Option_getD_inst1 Lean.Nat
      (I.List_find__q_inst1 Lean.Nat fL (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported sR)
        (I.List_range' (sub_nat_to_imported (S sR)) (sub_nat_to_imported n) cp_one)))
      cp_zero)
    (sub_nat_to_imported (odflt O (ohead (filter fR (sR :: iota (S sR) n)))))).
  have E := Hf sR. cbn [filter].
  destruct (fR sR); cbn in E.
  - change (Logic.eq (I.Option_getD_inst1 Lean.Nat
      (match fL (sub_nat_to_imported sR) with
       | I.Bool_true => I.Option_some_inst1 Lean.Nat (sub_nat_to_imported sR)
       | I.Bool_false => I.List_find__q_inst1 Lean.Nat fL
           (I.List_range' (sub_nat_to_imported (S sR)) (sub_nat_to_imported n) cp_one)
       end) cp_zero) (sub_nat_to_imported sR)).
    by rewrite E.
  - change (Logic.eq (I.Option_getD_inst1 Lean.Nat
      (match fL (sub_nat_to_imported sR) with
       | I.Bool_true => I.Option_some_inst1 Lean.Nat (sub_nat_to_imported sR)
       | I.Bool_false => I.List_find__q_inst1 Lean.Nat fL
           (I.List_range' (sub_nat_to_imported (S sR)) (sub_nat_to_imported n) cp_one)
       end) cp_zero) (sub_nat_to_imported (odflt O (ohead (filter fR (iota (S sR) n)))))).
    by rewrite E IH.
Qed.

(* ------------------------------------------------------------------ *)
(** * Source-side rewrites of [pick] and [[forall j, _]] into [iota] searches *)

Lemma cp_forall_ord_iota (nR : nat) (Q : 'I_nR -> bool) :
  Logic.eq [forall j, Q j] (all (cp_ord_family nR Q true) (iota 0 nR)).
Proof.
  apply/idP/idP.
  - move/forallP => H. apply/allP => k. rewrite mem_iota add0n => /andP [_ Hk].
    by rewrite /cp_ord_family insubT.
  - move/allP => H. apply/forallP => j. have := H (nat_of_ord j).
    rewrite mem_iota add0n ltn_ord /= /cp_ord_family valK. by apply.
Qed.

Lemma cp_default0_pick (nR : nat) (Q : 'I_nR -> bool) :
  Logic.eq (default0 (pick Q)) (odflt O (ohead (filter (cp_ord_family nR Q false) (iota 0 nR)))).
Proof.
  have VE : Logic.eq (map (@nat_of_ord nR) (enum 'I_nR)) (iota 0 nR) := val_enum_ord nR.
  have K : forall x : 'I_nR, Logic.eq (insub (nat_of_ord x)) (Some x) := fun x => valK x.
  rewrite -VE.
  have E : forall l : seq 'I_nR,
      Logic.eq (filter (cp_ord_family nR Q false) (map (@nat_of_ord nR) l))
               (map (@nat_of_ord nR) (filter Q l)).
  { elim => [|x l IH] //=. rewrite /cp_ord_family K. by case: (Q x); rewrite /= IH. }
  rewrite E /pick.
  have F : Logic.eq (enum Q) (filter Q (enum 'I_nR)).
  { rewrite enumT /enum_mem. apply: eq_filter => x. by rewrite inE. }
  rewrite F. by case: (filter Q (enum 'I_nR)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Options of ordinals *)

Inductive CpTrue : SProp := cp_true_intro.
Inductive CpFalse : SProp := .

Definition CpOptOrdRel (nR : nat) (nL : Lean.Nat) (xR : option 'I_nR) (xL : I.Option_inst1 (Fin nL)) : SProp :=
  match xR, xL with
  | None, I.Option_none_inst1 => CpTrue
  | Some oR, I.Option_some_inst1 oL => CpOrdRel nR nL oR oL
  | _, _ => CpFalse
  end.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Definition CpOrdPredRel nR nL (PR : 'I_nR -> bool) (PL : Fin nL -> I.Bool) : SProp :=
  forall oR oL, CpOrdRel nR nL oR oL -> CpBoolRel (PR oR) (PL oL).

Definition CpOrdRelRel nR nL (RR : 'I_nR -> 'I_nR -> bool) (RL : Fin nL -> Fin nL -> I.Bool) : SProp :=
  forall oR oL pR pL, CpOrdRel nR nL oR oL -> CpOrdRel nR nL pR pL -> CpBoolRel (RR oR pR) (RL oL pL).

Definition CpNatPredRel (pR : nat -> bool) (pL : Lean.Nat -> I.Bool) : SProp :=
  forall kR kL, SubNatRel kR kL -> CpBoolRel (pR kR) (pL kL).

Theorem default0_correspondence nR nL (Hn : SubNatRel nR nL)
    (xR : option 'I_nR) (xL : I.Option_inst1 (Fin nL)) :
  CpOptOrdRel nR nL xR xL ->
  SubNatRel (@default0 nR xR) (I.Prosa_Classic_Util_Pick_default0 nL xL).
Proof.
  destruct xR as [oR|], xL as [|oL]; cbn; intro H.
  - exact (match H with end).
  - exact H.
  - exact (sub_nat_rel_canonical O).
  - exact (match H with end).
Qed.

Theorem arg_pred_nat_correspondence nR nL (Hn : SubNatRel nR nL) PR PL ordR ordL
    (iR : 'I_nR) (iL : Fin nL) :
  CpOrdPredRel nR nL PR PL -> CpOrdRelRel nR nL ordR ordL -> CpOrdRel nR nL iR iL ->
  CpBoolRel (arg_pred_nat nR PR ordR iR) (I.Prosa_Classic_Util_Pick_arg_pred_nat nL PL ordL iL).
Proof.
  have E := cp_nat_logic _ _ Hn. subst nL. intros HP Hord Hi.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  change (Logic.eq (I.Bool_and (PL iL) (I.List_all_inst1 (Fin (sub_nat_to_imported nR))
      (I.List_finRange (sub_nat_to_imported nR)) (fun j => I.Bool_or (I.Bool_not (PL j)) (ordL iL j))))
    (cp_b2l (PR iR && [forall j, PR j ==> ordR iR j]))).
  rewrite (imported_eq_to_coq_eq _ _
    (I.Prosa_Validation_ClassicPickInterface_finRange_all (sub_nat_to_imported nR)
      (fun j => I.Bool_or (I.Bool_not (PL j)) (ordL iL j)))).
  rewrite cp_forall_ord_iota cp_b2l_and (cp_bool_rel_logic _ _ (HP iR iL Hi)).
  congr (I.Bool_and _ _).
  apply: (cp_all_iota (cp_ord_family nR (fun j => PR j ==> ordR iR j) true)
            (cp_target_family (sub_nat_to_imported nR)
               (fun j => I.Bool_or (I.Bool_not (PL j)) (ordL iL j)) I.Bool_true) _ nR O).
  move=> kR.
  apply: (cp_family_related nR (fun j => PR j ==> ordR iR j)
            (fun j => I.Bool_or (I.Bool_not (PL j)) (ordL iL j)) _ true kR).
  move=> oR oL Ho. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (cp_bool_rel_logic _ _ (HP oR oL Ho)) (cp_bool_rel_logic _ _ (Hord iR iL oR oL Hi Ho)).
  by rewrite /implb; case: (PR oR); case: (ordR iR oR).
Qed.

Theorem pred_min_nat_correspondence nR nL (Hn : SubNatRel nR nL) PR PL :
  CpOrdPredRel nR nL PR PL ->
  CpOrdPredRel nR nL (fun o => pred_min_nat nR PR o) (I.Prosa_Classic_Util_Pick_pred_min_nat nL PL).
Proof.
  intros HP oR oL Ho.
  apply: (arg_pred_nat_correspondence nR nL Hn PR PL _ _ oR oL HP _ Ho).
  move=> aR aL bR bL Ha Hb. exact (cp_decide_le_related _ _ _ _ Ha Hb).
Qed.

Theorem pred_max_nat_correspondence nR nL (Hn : SubNatRel nR nL) PR PL :
  CpOrdPredRel nR nL PR PL ->
  CpOrdPredRel nR nL (fun o => pred_max_nat nR PR o) (I.Prosa_Classic_Util_Pick_pred_max_nat nL PL).
Proof.
  intros HP oR oL Ho.
  apply: (arg_pred_nat_correspondence nR nL Hn PR PL _ _ oR oL HP _ Ho).
  move=> aR aL bR bL Ha Hb. exact (cp_decide_le_related _ _ _ _ Hb Ha).
Qed.

Theorem to_pred_ord_correspondence nR nL pR pL :
  CpNatPredRel pR pL ->
  CpOrdPredRel nR nL (to_pred_ord nR pR) (I.Prosa_Classic_Util_Pick_to_pred_ord nL pL).
Proof. intros Hp oR oL Ho. exact (Hp _ _ Ho). Qed.

(** [default0 (pick Q)] against [default0 (find? q (finRange n))], through the
    exported interface equation [default0_find?]. *)
Lemma cp_pick_correspondence nR nL (Hn : SubNatRel nR nL) (Q : 'I_nR -> bool) (q : Fin nL -> I.Bool) :
  CpOrdPredRel nR nL Q q ->
  SubNatRel (default0 (pick Q))
    (I.Prosa_Classic_Util_Pick_default0 nL (I.List_find__q_inst1 (Fin nL) q (I.List_finRange nL))).
Proof.
  have E := cp_nat_logic _ _ Hn. subst nL. intro HQ.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _
    (I.Prosa_Validation_ClassicPickInterface_default0_find__q (sub_nat_to_imported nR) q)).
  rewrite cp_default0_pick. apply: Logic.eq_sym.
  exact (cp_find_iota (cp_ord_family nR Q false) (cp_target_family (sub_nat_to_imported nR) q I.Bool_false)
           (cp_family_related nR Q q HQ false) nR O).
Qed.

Theorem pick_any_correspondence nR nL (Hn : SubNatRel nR nL) pR pL :
  CpNatPredRel pR pL -> SubNatRel (pick_any nR pR) (I.Prosa_Classic_Util_Pick_pick_any nL pL).
Proof.
  intro Hp. exact (cp_pick_correspondence nR nL Hn _ _ (to_pred_ord_correspondence nR nL pR pL Hp)).
Qed.

Theorem pick_min_correspondence nR nL (Hn : SubNatRel nR nL) pR pL :
  CpNatPredRel pR pL -> SubNatRel (pick_min nR pR) (I.Prosa_Classic_Util_Pick_pick_min nL pL).
Proof.
  intro Hp. exact (cp_pick_correspondence nR nL Hn _ _
    (pred_min_nat_correspondence nR nL Hn _ _ (to_pred_ord_correspondence nR nL pR pL Hp))).
Qed.

Theorem pick_max_correspondence nR nL (Hn : SubNatRel nR nL) pR pL :
  CpNatPredRel pR pL -> SubNatRel (pick_max nR pR) (I.Prosa_Classic_Util_Pick_pick_max nL pL).
Proof.
  intro Hp. exact (cp_pick_correspondence nR nL Hn _ _
    (pred_max_nat_correspondence nR nL Hn _ _ (to_pred_ord_correspondence nR nL pR pL Hp))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statement combinators *)

Lemma cp_imp (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. apply (prop_to_sprop _ _ HQ). exact (H (sprop_to_prop _ _ HP p)).
  - intro H. apply strictly_inhabits. intro p.
    apply (sprop_to_prop _ _ HQ). exact (H (prop_to_sprop _ _ HP p)).
Qed.

Lemma cp_and (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P /\ Q) (And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p q]. exact (And_intro PL QL (prop_to_sprop _ _ HP p) (prop_to_sprop _ _ HQ q)).
  - intros [p q]. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ HP p).
    + exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma cp_exists_nat (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (exists nR, PR nR) (I.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [nR Hn]. exact (I.Exists_intro Lean.Nat PL (sub_nat_to_imported nR)
      (prop_to_sprop _ _ (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) Hn)).
  - intros [nL Hn]. apply strictly_inhabits. exists (sub_nat_to_rocq nL).
    exact (sprop_to_prop _ _ (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL)) Hn).
Qed.

Lemma cp_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b)
    (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a.
    exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma cp_forall_cover_prop (A B : Type) (Rel : A -> B -> Prop) (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b)
    (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a.
    exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma cp_forall_nat (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall nR, PR nR) (forall nL, PL nL).
Proof.
  exact (cp_forall_cover_sprop _ _ SubNatRel sub_nat_to_imported sub_nat_to_rocq
    sub_nat_rel_canonical sub_nat_rel_surjective PR PL).
Qed.

(** Boolean predicates on naturals: pointwise on related arguments. *)
Lemma cp_nat_pred_input (pR : nat -> bool) (pL : Lean.Nat -> I.Bool) :
  CpNatPredRel pR pL -> forall kR, Logic.eq (pL (sub_nat_to_imported kR)) (cp_b2l (pR kR)).
Proof. intros Hp kR. exact (cp_bool_rel_logic _ _ (Hp _ _ (sub_nat_rel_canonical kR))). Qed.

Lemma cp_forall_nat_pred (PR : pred nat -> Prop) (PL : (Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CpNatPredRel pR pL -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  apply (cp_forall_cover_sprop _ _ CpNatPredRel (fun pR kL => cp_b2l (pR (sub_nat_to_rocq kL)))
           (fun pL kR => cp_l2b (pL (sub_nat_to_imported kR)))).
  - intros pR kR kL Hk. have E := cp_nat_logic _ _ Hk. subst kL.
    rewrite sub_nat_rocq_roundtrip. exact (cp_bool_rel_canonical _).
  - intros pL kR kL Hk. have E := cp_nat_logic _ _ Hk. subst kL.
    exact (cp_bool_rel_surjective _).
Qed.

(** Propositional predicates on naturals ([nat -> Prop] against Lean's
    [Nat -> Prop], imported as [Nat -> SProp]): pointwise [PropSPropRel]. *)
Definition CpPropPredRel (PR : nat -> Prop) (PL : Lean.Nat -> SProp) : Prop :=
  forall kR kL, SubNatRel kR kL -> PropSPropRel (PR kR) (PL kL).

Inductive CpBox (Q : SProp) : Prop := cp_box : Q -> CpBox Q.

Lemma cp_box_rel (Q : SProp) : PropSPropRel (CpBox Q) Q.
Proof.
  apply prop_sprop_rel_intro.
  - intros [q]. exact q.
  - intro q. apply strictly_inhabits. exact (cp_box Q q).
Qed.

Lemma cp_strict_rel (P : Prop) : PropSPropRel P (StrictlyInhabited P).
Proof.
  apply prop_sprop_rel_intro.
  - intro p. exact (strictly_inhabits p).
  - intro p. exact p.
Qed.

Lemma cp_forall_prop_pred (PR : (nat -> Prop) -> Prop) (PL : (Lean.Nat -> SProp) -> SProp) :
  (forall PRp PLp, CpPropPredRel PRp PLp -> PropSPropRel (PR PRp) (PL PLp)) ->
  PropSPropRel (forall P, PR P) (forall P, PL P).
Proof.
  apply (cp_forall_cover_prop _ _ CpPropPredRel
           (fun PRp kL => StrictlyInhabited (PRp (sub_nat_to_rocq kL)))
           (fun PLp kR => CpBox (PLp (sub_nat_to_imported kR)))).
  - intros PRp kR kL Hk. have E := cp_nat_logic _ _ Hk. subst kL.
    rewrite sub_nat_rocq_roundtrip. exact (cp_strict_rel _).
  - intros PLp kR kL Hk. have E := cp_nat_logic _ _ Hk. subst kL.
    exact (cp_box_rel _).
Qed.

(** Leaves. *)
Lemma cp_bool_rel_not aR aL : CpBoolRel aR aL -> CpBoolRel (~~ aR) (I.Bool_not aL).
Proof.
  intro H. rewrite (cp_bool_rel_logic _ _ H). apply: coq_eq_to_imported_eq. exact (cp_b2l_not aR).
Qed.

Lemma cp_ex_below nR nL (Hn : SubNatRel nR nL) pR pL : CpNatPredRel pR pL ->
  PropSPropRel (exists x : nat, is_true (ltn x nR) /\ is_true (pR x))
    (I.Exists Lean.Nat (fun x => And (I.LT_lt_inst1 Lean.Nat I.instLTNat x nL) (Lean.eq (pL x) I.Bool_true))).
Proof.
  intro Hp. apply: cp_exists_nat => xR xL Hx.
  exact (cp_and _ _ _ _ (cp_nat_lt _ _ _ _ Hx Hn) (cp_bool_truth _ _ (Hp _ _ Hx))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_pick_any_holds : Prop := ltac:(type_of_term @pick_any_holds).
Definition tgt_pick_any_holds : SProp := ltac:(type_of_term @I.Prosa_Classic_Util_Pick_pick_any_holds).
Theorem pick_any_holds_correspondence : PropSPropRel src_pick_any_holds tgt_pick_any_holds.
Proof.
  unfold src_pick_any_holds, tgt_pick_any_holds.
  apply: cp_forall_nat => nR nL Hn. apply: cp_forall_nat_pred => pR pL Hp.
  apply: cp_forall_prop_pred => PR PL HP.
  apply: cp_imp; first exact (cp_ex_below nR nL Hn pR pL Hp).
  apply: cp_imp.
  - apply: cp_forall_nat => xR xL Hx.
    exact (cp_imp _ _ _ _ (cp_bool_truth _ _ (Hp _ _ Hx)) (HP _ _ Hx)).
  - exact (HP _ _ (pick_any_correspondence nR nL Hn pR pL Hp)).
Qed.

Definition src_pick_min_ltn : Prop := ltac:(type_of_term @pick_min_ltn).
Definition tgt_pick_min_ltn : SProp := ltac:(type_of_term @I.Prosa_Classic_Util_Pick_pick_min_ltn).
Theorem pick_min_ltn_correspondence : PropSPropRel src_pick_min_ltn tgt_pick_min_ltn.
Proof.
  unfold src_pick_min_ltn, tgt_pick_min_ltn.
  apply: cp_forall_nat => nR nL Hn. apply: cp_forall_nat_pred => pR pL Hp.
  apply: cp_imp; first exact (cp_ex_below nR nL Hn pR pL Hp).
  exact (cp_nat_lt _ _ _ _ (pick_min_correspondence nR nL Hn pR pL Hp) Hn).
Qed.

Definition src_pick_min_holds : Prop := ltac:(type_of_term @pick_min_holds).
Definition tgt_pick_min_holds : SProp := ltac:(type_of_term @I.Prosa_Classic_Util_Pick_pick_min_holds).
Theorem pick_min_holds_correspondence : PropSPropRel src_pick_min_holds tgt_pick_min_holds.
Proof.
  unfold src_pick_min_holds, tgt_pick_min_holds.
  apply: cp_forall_nat => nR nL Hn. apply: cp_forall_nat_pred => pR pL Hp.
  apply: cp_forall_prop_pred => PR PL HP.
  apply: cp_imp; first exact (cp_ex_below nR nL Hn pR pL Hp).
  apply: cp_imp.
  - apply: cp_forall_nat => xR xL Hx.
    apply: cp_imp; first exact (cp_nat_lt _ _ _ _ Hx Hn).
    apply: cp_imp; first exact (cp_bool_truth _ _ (Hp _ _ Hx)).
    apply: cp_imp; last exact (HP _ _ Hx).
    apply: cp_forall_nat => yR yL Hy.
    apply: cp_imp; first exact (cp_nat_lt _ _ _ _ Hy Hn).
    exact (cp_imp _ _ _ _ (cp_bool_truth _ _ (Hp _ _ Hy)) (cp_nat_le _ _ _ _ Hx Hy)).
  - exact (HP _ _ (pick_min_correspondence nR nL Hn pR pL Hp)).
Qed.

Definition src_pick_max_ltn : Prop := ltac:(type_of_term @pick_max_ltn).
Definition tgt_pick_max_ltn : SProp := ltac:(type_of_term @I.Prosa_Classic_Util_Pick_pick_max_ltn).
Theorem pick_max_ltn_correspondence : PropSPropRel src_pick_max_ltn tgt_pick_max_ltn.
Proof.
  unfold src_pick_max_ltn, tgt_pick_max_ltn.
  apply: cp_forall_nat => nR nL Hn. apply: cp_forall_nat_pred => pR pL Hp.
  apply: cp_imp; first exact (cp_ex_below nR nL Hn pR pL Hp).
  exact (cp_nat_lt _ _ _ _ (pick_max_correspondence nR nL Hn pR pL Hp) Hn).
Qed.

Definition src_pick_max_holds : Prop := ltac:(type_of_term @pick_max_holds).
Definition tgt_pick_max_holds : SProp := ltac:(type_of_term @I.Prosa_Classic_Util_Pick_pick_max_holds).
Theorem pick_max_holds_correspondence : PropSPropRel src_pick_max_holds tgt_pick_max_holds.
Proof.
  unfold src_pick_max_holds, tgt_pick_max_holds.
  apply: cp_forall_nat => nR nL Hn. apply: cp_forall_nat_pred => pR pL Hp.
  apply: cp_forall_prop_pred => PR PL HP.
  apply: cp_imp; first exact (cp_ex_below nR nL Hn pR pL Hp).
  apply: cp_imp.
  - apply: cp_forall_nat => xR xL Hx.
    apply: cp_imp; first exact (cp_nat_lt _ _ _ _ Hx Hn).
    apply: cp_imp; first exact (cp_bool_truth _ _ (Hp _ _ Hx)).
    apply: cp_imp; last exact (HP _ _ Hx).
    apply: cp_forall_nat => yR yL Hy.
    apply: cp_imp; first exact (cp_nat_lt _ _ _ _ Hy Hn).
    exact (cp_imp _ _ _ _ (cp_bool_truth _ _ (Hp _ _ Hy)) (cp_nat_le _ _ _ _ Hy Hx)).
  - exact (HP _ _ (pick_max_correspondence nR nL Hn pR pL Hp)).
Qed.

Definition src_pick_any_pred : Prop := ltac:(type_of_term @pick_any_pred).
Definition tgt_pick_any_pred : SProp := ltac:(type_of_term @I.Prosa_Classic_Util_Pick_pick_any_pred).
Theorem pick_any_pred_correspondence : PropSPropRel src_pick_any_pred tgt_pick_any_pred.
Proof.
  unfold src_pick_any_pred, tgt_pick_any_pred.
  apply: cp_forall_nat => nR nL Hn. apply: cp_forall_nat_pred => pR pL Hp.
  apply: cp_imp; first exact (cp_ex_below nR nL Hn pR pL Hp).
  exact (cp_bool_truth _ _ (Hp _ _ (pick_any_correspondence nR nL Hn pR pL Hp))).
Qed.

Definition src_pick_min_pred : Prop := ltac:(type_of_term @pick_min_pred).
Definition tgt_pick_min_pred : SProp := ltac:(type_of_term @I.Prosa_Classic_Util_Pick_pick_min_pred).
Theorem pick_min_pred_correspondence : PropSPropRel src_pick_min_pred tgt_pick_min_pred.
Proof.
  unfold src_pick_min_pred, tgt_pick_min_pred.
  apply: cp_forall_nat => nR nL Hn. apply: cp_forall_nat_pred => pR pL Hp.
  apply: cp_imp; first exact (cp_ex_below nR nL Hn pR pL Hp).
  exact (cp_bool_truth _ _ (Hp _ _ (pick_min_correspondence nR nL Hn pR pL Hp))).
Qed.

Definition src_pick_max_pred : Prop := ltac:(type_of_term @pick_max_pred).
Definition tgt_pick_max_pred : SProp := ltac:(type_of_term @I.Prosa_Classic_Util_Pick_pick_max_pred).
Theorem pick_max_pred_correspondence : PropSPropRel src_pick_max_pred tgt_pick_max_pred.
Proof.
  unfold src_pick_max_pred, tgt_pick_max_pred.
  apply: cp_forall_nat => nR nL Hn. apply: cp_forall_nat_pred => pR pL Hp.
  apply: cp_imp; first exact (cp_ex_below nR nL Hn pR pL Hp).
  exact (cp_bool_truth _ _ (Hp _ _ (pick_max_correspondence nR nL Hn pR pL Hp))).
Qed.

Definition src_pick_min_compare : Prop := ltac:(type_of_term @pick_min_compare).
Definition tgt_pick_min_compare : SProp := ltac:(type_of_term @I.Prosa_Classic_Util_Pick_pick_min_compare).
Theorem pick_min_compare_correspondence : PropSPropRel src_pick_min_compare tgt_pick_min_compare.
Proof.
  unfold src_pick_min_compare, tgt_pick_min_compare.
  apply: cp_forall_nat => nR nL Hn.
  apply: cp_forall_nat_pred => p1R p1L Hp1. apply: cp_forall_nat_pred => p2R p2L Hp2.
  apply: cp_imp; first exact (cp_ex_below nR nL Hn p1R p1L Hp1).
  apply: cp_imp; first exact (cp_ex_below nR nL Hn p2R p2L Hp2).
  apply: cp_imp.
  - apply: cp_forall_nat => xR xL Hx. apply: cp_forall_nat => yR yL Hy.
    apply: cp_imp; first exact (cp_nat_lt _ _ _ _ Hx Hn).
    apply: cp_imp; first exact (cp_nat_lt _ _ _ _ Hy Hn).
    apply: cp_imp; first exact (cp_bool_truth _ _ (Hp1 _ _ Hx)).
    apply: cp_imp; first exact (cp_bool_truth _ _ (Hp2 _ _ Hy)).
    exact (cp_imp _ _ _ _ (cp_bool_truth _ _ (cp_bool_rel_not _ _ (Hp1 _ _ Hy))) (cp_nat_le _ _ _ _ Hx Hy)).
  - exact (cp_nat_le _ _ _ _ (pick_min_correspondence nR nL Hn p1R p1L Hp1)
                             (pick_min_correspondence nR nL Hn p2R p2L Hp2)).
Qed.
