From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
From prosa Require Import classic.util.tactics.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicTactics.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence.

Module I := ImportedClassicTactics.

(** Certificates for [classic/util/tactics.v] (ProsaBuddy classic, commit f692cb7).

    Inputs.  Booleans constructor-wise ([CtBoolRel], two-way totals); natural
    numbers by the accepted [SubNatRel]; for an [eqType] [T] the Lean
    [DecidableEq T] instance is the eqType's decision procedure
    ([ct_decidable_eq], as for the accepted v0.6 [util/seqset]) and elements of
    [T] are identified.

    Statements.  The source side is the exact elaborated type of the pinned
    lemma (via [type of]; the source proof is not used); Prop-valued statements
    are related by [PropSPropRel] through structural combinators.  The
    [Type]-valued [reflect] view [vlib__internal_eqP] is related to the Lean
    [BoolReflect] family by a pair of constructor-preserving maps (as for the
    accepted v0.6 [quiet_time_P]); no source or target proof is used.
    Lean's decision procedures are never unfolded: a [decide] is related to a
    Boolean through the propositional correspondence of its proposition. *)

Ltac type_of_term t := let T := type of t in exact T.

(* ------------------------------------------------------------------ *)
(** * Booleans *)

Definition ct_b2l (b : bool) : I.Bool := if b then I.Bool_true else I.Bool_false.
Definition ct_l2b (b : I.Bool) : bool := match b with I.Bool_true => true | I.Bool_false => false end.
Definition CtBoolRel (bR : bool) (bL : I.Bool) : SProp := Lean.eq (ct_b2l bR) bL.

Lemma ct_bool_canonical b : CtBoolRel b (ct_b2l b).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma ct_bool_surjective b : CtBoolRel (ct_l2b b) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma ct_bool_rel_logic bR bL : CtBoolRel bR bL -> Logic.eq bL (ct_b2l bR).
Proof. intro H. exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ H)). Qed.

Definition ct_false_elim (Q : SProp) (H : I.False) : Q := match H return Q with end.
Definition ct_coq_false_to_target (H : Logic.False) : I.False := match H return I.False with end.
Definition ct_target_false_to_strict (H : I.False) : StrictlyInhabited Logic.False := match H with end.

Lemma ct_decide_bool (b : bool) (Q : SProp) (d : I.Decidable Q) :
  PropSPropRel (is_true b) Q -> CtBoolRel b (I.Decidable_decide Q d).
Proof.
  intro Hrel. unfold CtBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (ct_false_elim _ (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (ct_false_elim _ (ct_coq_false_to_target (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Lemma ct_bool_eq aR aL bR bL :
  CtBoolRel aR aL -> CtBoolRel bR bL -> PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. rewrite (ct_bool_rel_logic _ _ Ha) (ct_bool_rel_logic _ _ Hb). clear Ha Hb.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := imported_eq_to_coq_eq _ _ E. clear E.
    move: E'. by case: aR; case: bR.
Qed.

Lemma ct_bool_truth bR bL : CtBoolRel bR bL -> PropSPropRel (is_true bR) (Lean.eq bL I.Bool_true).
Proof. intro H. exact (ct_bool_eq _ _ true I.Bool_true H (@Lean.eq_refl _ _)). Qed.

Lemma ct_bool_false bR bL : CtBoolRel bR bL -> PropSPropRel (Logic.eq bR false) (Lean.eq bL I.Bool_false).
Proof. intro H. exact (ct_bool_eq _ _ false I.Bool_false H (@Lean.eq_refl _ _)). Qed.

Lemma ct_bool_and aR aL bR bL :
  CtBoolRel aR aL -> CtBoolRel bR bL -> CtBoolRel (aR && bR) (I.Bool_and aL bL).
Proof.
  intros Ha Hb. rewrite /CtBoolRel (ct_bool_rel_logic _ _ Ha) (ct_bool_rel_logic _ _ Hb). clear Ha Hb.
  apply: coq_eq_to_imported_eq. by case: aR; case: bR.
Qed.

Lemma ct_bool_or aR aL bR bL :
  CtBoolRel aR aL -> CtBoolRel bR bL -> CtBoolRel (aR || bR) (I.Bool_or aL bL).
Proof.
  intros Ha Hb. rewrite /CtBoolRel (ct_bool_rel_logic _ _ Ha) (ct_bool_rel_logic _ _ Hb). clear Ha Hb.
  apply: coq_eq_to_imported_eq. by case: aR; case: bR.
Qed.

Lemma ct_bool_not aR aL : CtBoolRel aR aL -> CtBoolRel (~~ aR) (I.Bool_not aL).
Proof.
  intro Ha. rewrite /CtBoolRel (ct_bool_rel_logic _ _ Ha). clear Ha. apply: coq_eq_to_imported_eq. by case: aR.
Qed.

(* ------------------------------------------------------------------ *)
(** * Natural numbers *)

Lemma ct_decide_le aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL ->
  CtBoolRel (leq aR bR) (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat aL bL) (I.Nat_decLe aL bL)).
Proof. intros Ha Hb. exact (ct_decide_bool _ _ _ (sub_nat_le_correspondence _ _ _ _ Ha Hb)). Qed.

Lemma ct_decide_lt aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL ->
  CtBoolRel (ltn aR bR) (I.Decidable_decide (I.LT_lt_inst1 Lean.Nat I.instLTNat aL bL) (I.Nat_decLt aL bL)).
Proof. intros Ha Hb. exact (ct_decide_bool _ _ _ (sub_nat_lt_correspondence _ _ _ _ Ha Hb)). Qed.

(* ------------------------------------------------------------------ *)
(** * eqTypes *)

Definition ct_decidable_eq (T : eqType) : I.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => I.Decidable_isTrue (Lean.eq x y) (coq_eq_to_imported_eq x y H)
    | ReflectF H => I.Decidable_isFalse (Lean.eq x y)
        (fun HL => ct_coq_false_to_target (H (imported_eq_to_coq_eq x y HL)))
    end.

Lemma ct_eq_rel (T : Type) (x y : T) : PropSPropRel (Logic.eq x y) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - exact (coq_eq_to_imported_eq x y).
  - intro H. exact (strictly_inhabits (imported_eq_to_coq_eq x y H)).
Qed.

Lemma ct_eqb_rel (T : eqType) (x y : T) : PropSPropRel (is_true (x == y)) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP. exact (coq_eq_to_imported_eq x y).
  - intro H. apply strictly_inhabits. apply/eqP. exact (imported_eq_to_coq_eq x y H).
Qed.

Lemma ct_decide_eq (T : eqType) (x y : T) :
  CtBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (ct_decidable_eq T x y)).
Proof. exact (ct_decide_bool _ _ _ (ct_eqb_rel T x y)). Qed.

(* ------------------------------------------------------------------ *)
(** * Statement combinators *)

Lemma ct_imp (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. apply (prop_to_sprop _ _ HQ). exact (H (sprop_to_prop _ _ HP p)).
  - intro H. apply strictly_inhabits. intro p.
    apply (sprop_to_prop _ _ HQ). exact (H (prop_to_sprop _ _ HP p)).
Qed.

Lemma ct_and (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P /\ Q) (And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p q]. exact (And_intro PL QL (prop_to_sprop _ _ HP p) (prop_to_sprop _ _ HQ q)).
  - intros [p q]. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ HP p).
    + exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma ct_or (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P \/ Q) (Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p|q]; [exact (Or_inl PL QL (prop_to_sprop _ _ HP p)) | exact (Or_inr PL QL (prop_to_sprop _ _ HQ q))].
  - intros [p|q]; apply strictly_inhabits; [left; exact (sprop_to_prop _ _ HP p) | right; exact (sprop_to_prop _ _ HQ q)].
Qed.

Lemma ct_forall_identity (A : Type) (PR : A -> Prop) (PL : A -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) -> PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (H x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x. exact (sprop_to_prop _ _ (H x) (HL x)).
Qed.

Lemma ct_forall_bool (PR : bool -> Prop) (PL : I.Bool -> SProp) :
  (forall bR bL, CtBoolRel bR bL -> PropSPropRel (PR bR) (PL bL)) ->
  PropSPropRel (forall b, PR b) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR bL. exact (prop_to_sprop _ _ (H _ _ (ct_bool_surjective bL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro bR. exact (sprop_to_prop _ _ (H _ _ (ct_bool_canonical bR)) (HL _)).
Qed.

Lemma ct_forall_nat (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall n, PR n) (forall n, PL n).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR nL. exact (prop_to_sprop _ _ (H _ _ (sub_nat_rel_surjective nL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro nR. exact (sprop_to_prop _ _ (H _ _ (sub_nat_rel_canonical nR)) (HL _)).
Qed.

(* ------------------------------------------------------------------ *)
(** * The [reflect] view *)

Definition ct_reflect_forward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    reflect PR bR -> I.Prosa_Classic_Util_Tactics_BoolReflect PL bL.
Proof.
  destruct Hb. intro HR. destruct HR as [Htrue | Hfalse].
  - exact (I.Prosa_Classic_Util_Tactics_BoolReflect_isTrue PL (prop_to_sprop _ _ HP Htrue)).
  - exact (I.Prosa_Classic_Util_Tactics_BoolReflect_isFalse PL
      (fun HL => ct_coq_false_to_target (Hfalse (sprop_to_prop _ _ HP HL)))).
Defined.

Definition ct_reflect_backward_at_bool (PR : Prop) (PL : SProp) (HP : PropSPropRel PR PL) (bL : I.Bool) :
    I.Prosa_Classic_Util_Tactics_BoolReflect PL bL -> reflect PR (ct_l2b bL) :=
  fun HL =>
    match HL in I.Prosa_Classic_Util_Tactics_BoolReflect _ b return reflect PR (ct_l2b b) with
    | I.Prosa_Classic_Util_Tactics_BoolReflect_isTrue Htrue => ReflectT PR (sprop_to_prop _ _ HP Htrue)
    | I.Prosa_Classic_Util_Tactics_BoolReflect_isFalse Hfalse =>
        ReflectF PR (fun HR => interpret_strict Logic.False
          (ct_target_false_to_strict (Hfalse (prop_to_sprop _ _ HP HR))))
    end.

Definition ct_reflect_backward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    I.Prosa_Classic_Util_Tactics_BoolReflect PL bL -> reflect PR bR.
Proof. destruct Hb. destruct bR; cbn; exact (ct_reflect_backward_at_bool PR PL HP _). Defined.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_vlib__internal_eqP (T : eqType) : Type := ltac:(type_of_term (@vlib__internal_eqP T)).
Definition tgt_vlib__internal_eqP (T : eqType) : Type :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Tactics_vlib__internal_eqP T (ct_decidable_eq T))).
Theorem vlib__internal_eqP_correspondence (T : eqType) :
  Datatypes.prod (src_vlib__internal_eqP T -> tgt_vlib__internal_eqP T)
                 (tgt_vlib__internal_eqP T -> src_vlib__internal_eqP T).
Proof.
  split.
  - intros f x y. exact (ct_reflect_forward _ _ _ _ (ct_eq_rel T x y) (ct_decide_eq T x y) (f x y)).
  - intros g x y. exact (ct_reflect_backward _ _ _ _ (ct_eq_rel T x y) (ct_decide_eq T x y) (g x y)).
Defined.

Definition src_beq_refl (T : eqType) : Prop := ltac:(type_of_term (@beq_refl T)).
Definition tgt_beq_refl (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Tactics_beq_refl T (ct_decidable_eq T))).
Theorem beq_refl_correspondence (T : eqType) : PropSPropRel (src_beq_refl T) (tgt_beq_refl T).
Proof.
  unfold src_beq_refl, tgt_beq_refl. apply: ct_forall_identity => x.
  exact (ct_bool_truth _ _ (ct_decide_eq T x x)).
Qed.

Definition src_beq_sym (T : eqType) : Prop := ltac:(type_of_term (@beq_sym T)).
Definition tgt_beq_sym (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Tactics_beq_sym T (ct_decidable_eq T))).
Theorem beq_sym_correspondence (T : eqType) : PropSPropRel (src_beq_sym T) (tgt_beq_sym T).
Proof.
  unfold src_beq_sym, tgt_beq_sym. apply: ct_forall_identity => x. apply: ct_forall_identity => y.
  exact (ct_bool_eq _ _ _ _ (ct_decide_eq T x y) (ct_decide_eq T y x)).
Qed.

Definition src_vlib__negb_rewrite : Prop := ltac:(type_of_term @vlib__negb_rewrite).
Definition tgt_vlib__negb_rewrite : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Tactics_vlib__negb_rewrite).
Theorem vlib__negb_rewrite_correspondence : PropSPropRel src_vlib__negb_rewrite tgt_vlib__negb_rewrite.
Proof.
  unfold src_vlib__negb_rewrite, tgt_vlib__negb_rewrite. apply: ct_forall_bool => bR bL Hb.
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (ct_bool_not _ _ Hb)) (ct_bool_false _ _ Hb)).
Qed.

Definition src_vlib__andb_split : Prop := ltac:(type_of_term @vlib__andb_split).
Definition tgt_vlib__andb_split : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Tactics_vlib__andb_split).
Theorem vlib__andb_split_correspondence : PropSPropRel src_vlib__andb_split tgt_vlib__andb_split.
Proof.
  unfold src_vlib__andb_split, tgt_vlib__andb_split.
  apply: ct_forall_bool => aR aL Ha. apply: ct_forall_bool => bR bL Hb.
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (ct_bool_and _ _ _ _ Ha Hb))
    (ct_and _ _ _ _ (ct_bool_truth _ _ Ha) (ct_bool_truth _ _ Hb))).
Qed.

Definition src_vlib__nandb_split : Prop := ltac:(type_of_term @vlib__nandb_split).
Definition tgt_vlib__nandb_split : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Tactics_vlib__nandb_split).
Theorem vlib__nandb_split_correspondence : PropSPropRel src_vlib__nandb_split tgt_vlib__nandb_split.
Proof.
  unfold src_vlib__nandb_split, tgt_vlib__nandb_split.
  apply: ct_forall_bool => aR aL Ha. apply: ct_forall_bool => bR bL Hb.
  exact (ct_imp _ _ _ _ (ct_bool_false _ _ (ct_bool_and _ _ _ _ Ha Hb))
    (ct_or _ _ _ _ (ct_bool_false _ _ Ha) (ct_bool_false _ _ Hb))).
Qed.

Definition src_vlib__orb_split : Prop := ltac:(type_of_term @vlib__orb_split).
Definition tgt_vlib__orb_split : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Tactics_vlib__orb_split).
Theorem vlib__orb_split_correspondence : PropSPropRel src_vlib__orb_split tgt_vlib__orb_split.
Proof.
  unfold src_vlib__orb_split, tgt_vlib__orb_split.
  apply: ct_forall_bool => aR aL Ha. apply: ct_forall_bool => bR bL Hb.
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (ct_bool_or _ _ _ _ Ha Hb))
    (ct_or _ _ _ _ (ct_bool_truth _ _ Ha) (ct_bool_truth _ _ Hb))).
Qed.

Definition src_vlib__norb_split : Prop := ltac:(type_of_term @vlib__norb_split).
Definition tgt_vlib__norb_split : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Tactics_vlib__norb_split).
Theorem vlib__norb_split_correspondence : PropSPropRel src_vlib__norb_split tgt_vlib__norb_split.
Proof.
  unfold src_vlib__norb_split, tgt_vlib__norb_split.
  apply: ct_forall_bool => aR aL Ha. apply: ct_forall_bool => bR bL Hb.
  exact (ct_imp _ _ _ _ (ct_bool_false _ _ (ct_bool_or _ _ _ _ Ha Hb))
    (ct_and _ _ _ _ (ct_bool_false _ _ Ha) (ct_bool_false _ _ Hb))).
Qed.

Definition src_vlib__eqb_split : Prop := ltac:(type_of_term @vlib__eqb_split).
Definition tgt_vlib__eqb_split : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Tactics_vlib__eqb_split).
Theorem vlib__eqb_split_correspondence : PropSPropRel src_vlib__eqb_split tgt_vlib__eqb_split.
Proof.
  unfold src_vlib__eqb_split, tgt_vlib__eqb_split.
  apply: ct_forall_bool => aR aL Ha. apply: ct_forall_bool => bR bL Hb.
  apply: ct_imp; first exact (ct_imp _ _ _ _ (ct_bool_truth _ _ Ha) (ct_bool_truth _ _ Hb)).
  apply: ct_imp; first exact (ct_imp _ _ _ _ (ct_bool_truth _ _ Hb) (ct_bool_truth _ _ Ha)).
  exact (ct_bool_eq _ _ _ _ Ha Hb).
Qed.

Definition src_vlib__beq_rewrite (T : eqType) : Prop := ltac:(type_of_term (@vlib__beq_rewrite T)).
Definition tgt_vlib__beq_rewrite (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Tactics_vlib__beq_rewrite T (ct_decidable_eq T))).
Theorem vlib__beq_rewrite_correspondence (T : eqType) :
  PropSPropRel (src_vlib__beq_rewrite T) (tgt_vlib__beq_rewrite T).
Proof.
  unfold src_vlib__beq_rewrite, tgt_vlib__beq_rewrite.
  apply: ct_forall_identity => x. apply: ct_forall_identity => y.
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (ct_decide_eq T x y)) (ct_eq_rel T x y)).
Qed.

Definition src_vlib__leq_split : Prop := ltac:(type_of_term @vlib__leq_split).
Definition tgt_vlib__leq_split : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Tactics_vlib__leq_split).
Theorem vlib__leq_split_correspondence : PropSPropRel src_vlib__leq_split tgt_vlib__leq_split.
Proof.
  unfold src_vlib__leq_split, tgt_vlib__leq_split.
  apply: ct_forall_nat => aR aL Ha. apply: ct_forall_nat => bR bL Hb. apply: ct_forall_nat => cR cL Hc.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ha Hb).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Hb Hc).
  exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Ha Hb) (ct_decide_le _ _ _ _ Hb Hc))).
Qed.

Definition src_vlib__ltn_split1 : Prop := ltac:(type_of_term @vlib__ltn_split1).
Definition tgt_vlib__ltn_split1 : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Tactics_vlib__ltn_split1).
Theorem vlib__ltn_split1_correspondence : PropSPropRel src_vlib__ltn_split1 tgt_vlib__ltn_split1.
Proof.
  unfold src_vlib__ltn_split1, tgt_vlib__ltn_split1.
  apply: ct_forall_nat => aR aL Ha. apply: ct_forall_nat => bR bL Hb. apply: ct_forall_nat => cR cL Hc.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ha Hb).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hb Hc).
  exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Ha Hb) (ct_decide_lt _ _ _ _ Hb Hc))).
Qed.

Definition src_vlib__ltn_split2 : Prop := ltac:(type_of_term @vlib__ltn_split2).
Definition tgt_vlib__ltn_split2 : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Tactics_vlib__ltn_split2).
Theorem vlib__ltn_split2_correspondence : PropSPropRel src_vlib__ltn_split2 tgt_vlib__ltn_split2.
Proof.
  unfold src_vlib__ltn_split2, tgt_vlib__ltn_split2.
  apply: ct_forall_nat => aR aL Ha. apply: ct_forall_nat => bR bL Hb. apply: ct_forall_nat => cR cL Hc.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ha Hb).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Hb Hc).
  exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ Ha Hb) (ct_decide_le _ _ _ _ Hb Hc))).
Qed.
