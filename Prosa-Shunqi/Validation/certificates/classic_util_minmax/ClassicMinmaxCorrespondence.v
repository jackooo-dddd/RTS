From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
From prosa Require Import classic.util.minmax.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicMinmax.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicMinmaxBase ClassicMinmaxList.

Module I := ImportedClassicMinmax.
Local Open Scope nat_scope.

(** Certificates for [classic/util/minmax.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: elements of [eqType]s identified (their Lean [DecidableEq] the
    eqTypes' decision procedures); sequences elementwise ([ClListRel]),
    natural-number sequences through [SubNatRel] ([cm_natl], Lean's [Set]-level
    lists); options constructor-wise; natural numbers by [SubNatRel]; Boolean
    relations, predicates and functions pointwise; all with two-way totals.

    Computation: [seq_argmin]/[seq_argmax]/[seq_argmin_k]/[rem] against their
    Lean counterparts by structural induction, one Lean step at a time by
    conversion (stated through the imported matchers); [values_between]
    through the exported equation [ClassicMinmaxInterface.finRange_map_val]
    and MathComp [val_enum_ord].  Lean decisions are never unfolded.

    Statements: the source side is the exact elaborated type of the pinned
    lemma (via [type of]; the source proof is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

Lemma cm_val_eq (T : Type) (aR aL bR bL : T) :
  Logic.eq aR aL -> Logic.eq bR bL -> PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros -> ->. apply prop_sprop_rel_intro.
  - exact (coq_eq_to_imported_eq _ _).
  - intro H. exact (strictly_inhabits (imported_eq_to_coq_eq _ _ H)).
Qed.

Lemma cm_opt_eq {A} (o1 o2 : option A) : PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := f_equal cl_unopt (imported_eq_to_coq_eq _ _ E).
    by rewrite !cl_unopt_opt in E'.
Qed.

Lemma cm_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl_forall_list cid cid (fun _ => Logic.eq_refl _) PR PL). Qed.

Lemma cm_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cm_forall_rel (A : Type) (PR : (A -> A -> bool) -> Prop) (PL : (A -> A -> I.Bool) -> SProp) :
  (forall pR pL, (forall a b, CtBoolRel (pR a b) (pL a b)) -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H (fun a b => ct_l2b (pL a b)) pL (fun a b => ct_bool_surjective _)) (HR _)).
  - intro HL. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ (H pR (fun a b => ct_b2l (pR a b)) (fun a b => ct_bool_canonical _)) (HL _)).
Qed.

Lemma cm_transitive (T : Type) (R : T -> T -> bool) RL (HR : forall a b, CtBoolRel (R a b) (RL a b)) :
  PropSPropRel (transitive R)
    (forall y x z, Lean.eq (RL x y) I.Bool_true -> Lean.eq (RL y z) I.Bool_true -> Lean.eq (RL x z) I.Bool_true).
Proof.
  rewrite /transitive. apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (HR x y)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (HR y z)) (ct_bool_truth _ _ (HR x z))).
Qed.

(** [o != None] against [!decide (o = none)]. *)
Lemma cm_neq_none {A : eqType} (o : option A) (dec : I.Decidable (Lean.eq (cl_opt o) (I.Option_none A))) :
  CtBoolRel (o != None) (I.Bool_not (I.Decidable_decide (Lean.eq (cl_opt o) (I.Option_none A)) dec)).
Proof.
  apply: ct_bool_not. apply: ct_decide_bool. apply prop_sprop_rel_intro.
  - move=> /eqP ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. have E' := f_equal cl_unopt (imported_eq_to_coq_eq _ _ E).
    by rewrite cl_unopt_opt in E'.
Qed.

(* ------------------------------------------------------------------ *)
(** * [seq_argmin] / [seq_argmax] *)

Section Arg.
Variables (T1 : eqType) (T2R : eqType) (T2L : Type) (d2 : I.DecidableEq T2L).
Variables (relR : T2R -> T2R -> bool) (relL : T2L -> T2L -> I.Bool) (FR : T1 -> T2R) (FL : T1 -> T2L).
Hypothesis Hcomp : forall x y, CtBoolRel (relR (FR x) (FR y)) (relL (FL x) (FL y)).
Notation d1 := (ct_decidable_eq T1).

Lemma cm_argmin_step x l :
  Logic.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (I.List_cons T1 x l))
    (I.Prosa_Classic_Util_Minmax_seq_argmin_match_1 T1 (fun _ => I.Option T1)
       (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL l)
       (fun y => I.ite (I.Option T1) (Lean.eq (relL (FL x) (FL y)) I.Bool_true) (I.instDecidableEqBool (relL (FL x) (FL y)) I.Bool_true)
                   (I.Option_some T1 x) (I.Option_some T1 y))
       (fun _ => I.Option_some T1 x)).
Proof. reflexivity. Qed.

Lemma cm_argmax_step x l :
  Logic.eq (I.Prosa_Classic_Util_Minmax_seq_argmax T1 T2L d1 d2 relL FL (I.List_cons T1 x l))
    (I.Prosa_Classic_Util_Minmax_seq_argmin_match_1 T1 (fun _ => I.Option T1)
       (I.Prosa_Classic_Util_Minmax_seq_argmax T1 T2L d1 d2 relL FL l)
       (fun y => I.ite (I.Option T1) (Lean.eq (relL (FL y) (FL x)) I.Bool_true) (I.instDecidableEqBool (relL (FL y) (FL x)) I.Bool_true)
                   (I.Option_some T1 x) (I.Option_some T1 y))
       (fun _ => I.Option_some T1 x)).
Proof. reflexivity. Qed.

Lemma cm_argmin_rel : forall l,
  Logic.eq (cl_opt (seq_argmin relR FR l)) (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (cl_map cid l)).
Proof.
  elim => [|x l IH] //=. rewrite cm_argmin_step -IH.
  case: (seq_argmin relR FR l) => [y|] //=.
  rewrite (ct_bool_rel_logic _ _ (Hcomp x y)). by case: (relR (FR x) (FR y)).
Qed.

Lemma cm_argmax_rel : forall l,
  Logic.eq (cl_opt (seq_argmax relR FR l)) (I.Prosa_Classic_Util_Minmax_seq_argmax T1 T2L d1 d2 relL FL (cl_map cid l)).
Proof.
  elim => [|x l IH] //=. rewrite cm_argmax_step -IH.
  case: (seq_argmax relR FR l) => [y|] //=.
  rewrite (ct_bool_rel_logic _ _ (Hcomp y x)). by case: (relR (FR y) (FR x)).
Qed.

Lemma cm_argmin_eq l L (H : ClListRel cid l L) o :
  PropSPropRel (Logic.eq (seq_argmin relR FR l) o)
    (Lean.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL L) (cl_opt o)).
Proof. destruct H. rewrite -cm_argmin_rel. exact (cm_opt_eq _ _). Qed.

Lemma cm_argmax_eq l L (H : ClListRel cid l L) o :
  PropSPropRel (Logic.eq (seq_argmax relR FR l) o)
    (Lean.eq (I.Prosa_Classic_Util_Minmax_seq_argmax T1 T2L d1 d2 relL FL L) (cl_opt o)).
Proof. destruct H. rewrite -cm_argmax_rel. exact (cm_opt_eq _ _). Qed.

Lemma cm_argmin_neq l L (H : ClListRel cid l L) :
  CtBoolRel (seq_argmin relR FR l != None)
    (I.Bool_not (I.Decidable_decide (Lean.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL L) (I.Option_none T1))
       (I.Option_decidableEqNone T1 (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL L)))).
Proof. destruct H. rewrite -cm_argmin_rel. exact (cm_neq_none _ _). Qed.

Lemma cm_argmax_neq l L (H : ClListRel cid l L) :
  CtBoolRel (seq_argmax relR FR l != None)
    (I.Bool_not (I.Decidable_decide (Lean.eq (I.Prosa_Classic_Util_Minmax_seq_argmax T1 T2L d1 d2 relL FL L) (I.Option_none T1))
       (I.Option_decidableEqNone T1 (I.Prosa_Classic_Util_Minmax_seq_argmax T1 T2L d1 d2 relL FL L)))).
Proof. destruct H. rewrite -cm_argmax_rel. exact (cm_neq_none _ _). Qed.
End Arg.

Theorem seq_argmin_correspondence (T1 T2 : eqType) relR relL (Hrel : forall a b, CtBoolRel (relR a b) (relL a b)) (F : T1 -> T2) l :
  Logic.eq (cl_opt (seq_argmin relR F l))
    (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2) relL F (cl_map cid l)).
Proof. exact (cm_argmin_rel T1 T2 T2 (ct_decidable_eq T2) relR relL F F (fun x y => Hrel _ _) l). Qed.

Theorem seq_argmax_correspondence (T1 T2 : eqType) relR relL (Hrel : forall a b, CtBoolRel (relR a b) (relL a b)) (F : T1 -> T2) l :
  Logic.eq (cl_opt (seq_argmax relR F l))
    (I.Prosa_Classic_Util_Minmax_seq_argmax T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2) relL F (cl_map cid l)).
Proof. exact (cm_argmax_rel T1 T2 T2 (ct_decidable_eq T2) relR relL F F (fun x y => Hrel _ _) l). Qed.

Theorem seq_min_correspondence (T : eqType) relR relL (Hrel : forall a b, CtBoolRel (relR a b) (relL a b)) l :
  Logic.eq (cl_opt (seq_min relR l)) (I.Prosa_Classic_Util_Minmax_seq_min T (ct_decidable_eq T) relL (cl_map cid l)).
Proof. exact (cm_argmin_rel T T T (ct_decidable_eq T) relR relL (@Datatypes.id T) (I.id T) (fun x y => Hrel _ _) l). Qed.

Theorem seq_max_correspondence (T : eqType) relR relL (Hrel : forall a b, CtBoolRel (relR a b) (relL a b)) l :
  Logic.eq (cl_opt (seq_max relR l)) (I.Prosa_Classic_Util_Minmax_seq_max T (ct_decidable_eq T) relL (cl_map cid l)).
Proof. exact (cm_argmax_rel T T T (ct_decidable_eq T) relR relL (@Datatypes.id T) (I.id T) (fun x y => Hrel _ _) l). Qed.

Definition cm_le (a b : Lean.Nat) : I.Bool := I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat a b) (I.Nat_decLe a b).

Lemma cm_le_comp (T : Type) (FR : T -> nat) (FL : T -> Lean.Nat) (HF : forall x, SubNatRel (FR x) (FL x)) x y :
  CtBoolRel (leq (FR x) (FR y)) (cm_le (FL x) (FL y)).
Proof. exact (ct_decide_le _ _ _ _ (HF x) (HF y)). Qed.

Theorem seq_argmin_nat_correspondence (T : eqType) (FR : T -> nat) (FL : T -> Lean.Nat) (HF : forall x, SubNatRel (FR x) (FL x)) l :
  Logic.eq (cl_opt (seq_argmin_nat FR l)) (I.Prosa_Classic_Util_Minmax_seq_argmin_nat T (ct_decidable_eq T) FL (cl_map cid l)).
Proof. exact (cm_argmin_rel T nat Lean.Nat I.instDecidableEqNat leq cm_le FR FL (cm_le_comp T FR FL HF) l). Qed.

Theorem seq_argmax_nat_correspondence (T : eqType) (FR : T -> nat) (FL : T -> Lean.Nat) (HF : forall x, SubNatRel (FR x) (FL x)) l :
  Logic.eq (cl_opt (seq_argmax_nat FR l)) (I.Prosa_Classic_Util_Minmax_seq_argmax_nat T (ct_decidable_eq T) FL (cl_map cid l)).
Proof. exact (cm_argmax_rel T nat Lean.Nat I.instDecidableEqNat leq cm_le FR FL (cm_le_comp T FR FL HF) l). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements: [seq_argmin]/[seq_argmax] *)

Lemma cm_comp (T1 T2 : Type) (relR : T2 -> T2 -> bool) relL (Hrel : forall a b, CtBoolRel (relR a b) (relL a b)) (F : T1 -> T2) x y :
  CtBoolRel (relR (F x) (F y)) (relL (F x) (F y)).
Proof. exact (Hrel _ _). Qed.

Definition src_seq_argmin_exists (T1 T2 : eqType) : Prop := ltac:(type_of_term (@seq_argmin_exists T1 T2)).
Definition tgt_seq_argmin_exists (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_argmin_exists T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem seq_argmin_exists_correspondence (T1 T2 : eqType) : PropSPropRel (src_seq_argmin_exists T1 T2) (tgt_seq_argmin_exists T1 T2).
Proof.
  unfold src_seq_argmin_exists, tgt_seq_argmin_exists.
  apply: cm_forall_rel => relR relL Hrel. apply: ct_forall_identity => F.
  apply: cm_forall_list => l L H. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cm_mem T1 x l L H)
           (ct_bool_truth _ _ (cm_argmin_neq T1 T2 T2 (ct_decidable_eq T2) relR relL F F (cm_comp T1 T2 relR relL Hrel F) l L H))).
Qed.

Definition src_seq_argmax_exists (T1 T2 : eqType) : Prop := ltac:(type_of_term (@seq_argmax_exists T1 T2)).
Definition tgt_seq_argmax_exists (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_argmax_exists T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem seq_argmax_exists_correspondence (T1 T2 : eqType) : PropSPropRel (src_seq_argmax_exists T1 T2) (tgt_seq_argmax_exists T1 T2).
Proof.
  unfold src_seq_argmax_exists, tgt_seq_argmax_exists.
  apply: cm_forall_rel => relR relL Hrel. apply: ct_forall_identity => F.
  apply: cm_forall_list => l L H. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cm_mem T1 x l L H)
           (ct_bool_truth _ _ (cm_argmax_neq T1 T2 T2 (ct_decidable_eq T2) relR relL F F (cm_comp T1 T2 relR relL Hrel F) l L H))).
Qed.

Definition src_seq_argmin_in_seq (T1 T2 : eqType) : Prop := ltac:(type_of_term (@seq_argmin_in_seq T1 T2)).
Definition tgt_seq_argmin_in_seq (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_argmin_in_seq T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem seq_argmin_in_seq_correspondence (T1 T2 : eqType) : PropSPropRel (src_seq_argmin_in_seq T1 T2) (tgt_seq_argmin_in_seq T1 T2).
Proof.
  unfold src_seq_argmin_in_seq, tgt_seq_argmin_in_seq.
  apply: cm_forall_rel => relR relL Hrel. apply: ct_forall_identity => F.
  apply: cm_forall_list => l L H. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cm_argmin_eq T1 T2 T2 (ct_decidable_eq T2) relR relL F F (cm_comp T1 T2 relR relL Hrel F) l L H (Some x)) (cm_mem T1 x l L H)).
Qed.

Definition src_seq_argmax_in_seq (T1 T2 : eqType) : Prop := ltac:(type_of_term (@seq_argmax_in_seq T1 T2)).
Definition tgt_seq_argmax_in_seq (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_argmax_in_seq T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem seq_argmax_in_seq_correspondence (T1 T2 : eqType) : PropSPropRel (src_seq_argmax_in_seq T1 T2) (tgt_seq_argmax_in_seq T1 T2).
Proof.
  unfold src_seq_argmax_in_seq, tgt_seq_argmax_in_seq.
  apply: cm_forall_rel => relR relL Hrel. apply: ct_forall_identity => F.
  apply: cm_forall_list => l L H. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cm_argmax_eq T1 T2 T2 (ct_decidable_eq T2) relR relL F F (cm_comp T1 T2 relR relL Hrel F) l L H (Some x)) (cm_mem T1 x l L H)).
Qed.

Definition src_seq_argmin_computes_min (T1 T2 : eqType) : Prop := ltac:(type_of_term (@seq_argmin_computes_min T1 T2)).
Definition tgt_seq_argmin_computes_min (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_argmin_computes_min T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem seq_argmin_computes_min_correspondence (T1 T2 : eqType) :
  PropSPropRel (src_seq_argmin_computes_min T1 T2) (tgt_seq_argmin_computes_min T1 T2).
Proof.
  unfold src_seq_argmin_computes_min, tgt_seq_argmin_computes_min.
  apply: cm_forall_rel => relR relL Hrel. apply: ct_forall_identity => F.
  apply: ct_imp; first exact (cm_transitive T2 relR relL Hrel).
  apply: cm_forall_list => l L H.
  apply: ct_imp.
  - apply: ct_forall_identity => x. apply: ct_forall_identity => y.
    apply: ct_imp; first exact (cm_mem T1 x l L H).
    exact (ct_imp _ _ _ _ (cm_mem T1 y l L H) (ct_bool_truth _ _ (ct_bool_or _ _ _ _ (Hrel _ _) (Hrel _ _)))).
  - apply: ct_forall_identity => x. apply: ct_forall_identity => y.
    apply: ct_imp; first exact (cm_argmin_eq T1 T2 T2 (ct_decidable_eq T2) relR relL F F (cm_comp T1 T2 relR relL Hrel F) l L H (Some x)).
    exact (ct_imp _ _ _ _ (cm_mem T1 y l L H) (ct_bool_truth _ _ (Hrel _ _))).
Qed.

Definition src_seq_argmax_computes_max (T1 T2 : eqType) : Prop := ltac:(type_of_term (@seq_argmax_computes_max T1 T2)).
Definition tgt_seq_argmax_computes_max (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_argmax_computes_max T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem seq_argmax_computes_max_correspondence (T1 T2 : eqType) :
  PropSPropRel (src_seq_argmax_computes_max T1 T2) (tgt_seq_argmax_computes_max T1 T2).
Proof.
  unfold src_seq_argmax_computes_max, tgt_seq_argmax_computes_max.
  apply: cm_forall_rel => relR relL Hrel. apply: ct_forall_identity => F.
  apply: ct_imp; first exact (cm_transitive T2 relR relL Hrel).
  apply: cm_forall_list => l L H.
  apply: ct_imp.
  - apply: ct_forall_identity => x. apply: ct_forall_identity => y.
    apply: ct_imp; first exact (cm_mem T1 x l L H).
    exact (ct_imp _ _ _ _ (cm_mem T1 y l L H) (ct_bool_truth _ _ (ct_bool_or _ _ _ _ (Hrel _ _) (Hrel _ _)))).
  - apply: ct_forall_identity => x. apply: ct_forall_identity => y.
    apply: ct_imp; first exact (cm_argmax_eq T1 T2 T2 (ct_decidable_eq T2) relR relL F F (cm_comp T1 T2 relR relL Hrel F) l L H (Some x)).
    exact (ct_imp _ _ _ _ (cm_mem T1 y l L H) (ct_bool_truth _ _ (Hrel _ _))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements: [seq_min]/[seq_max] *)

Notation cmid T := (@Datatypes.id T).

Definition src_seq_min_exists (T : eqType) : Prop := ltac:(type_of_term (@seq_min_exists T)).
Definition tgt_seq_min_exists (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_min_exists T (ct_decidable_eq T))).
Theorem seq_min_exists_correspondence (T : eqType) : PropSPropRel (src_seq_min_exists T) (tgt_seq_min_exists T).
Proof.
  unfold src_seq_min_exists, tgt_seq_min_exists.
  apply: cm_forall_rel => relR relL Hrel. apply: cm_forall_list => l L H. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cm_mem T x l L H)
           (ct_bool_truth _ _ (cm_argmin_neq T T T (ct_decidable_eq T) relR relL (cmid T) (I.id T) (fun a b => Hrel _ _) l L H))).
Qed.

Definition src_seq_max_exists (T : eqType) : Prop := ltac:(type_of_term (@seq_max_exists T)).
Definition tgt_seq_max_exists (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_max_exists T (ct_decidable_eq T))).
Theorem seq_max_exists_correspondence (T : eqType) : PropSPropRel (src_seq_max_exists T) (tgt_seq_max_exists T).
Proof.
  unfold src_seq_max_exists, tgt_seq_max_exists.
  apply: cm_forall_rel => relR relL Hrel. apply: cm_forall_list => l L H. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cm_mem T x l L H)
           (ct_bool_truth _ _ (cm_argmax_neq T T T (ct_decidable_eq T) relR relL (cmid T) (I.id T) (fun a b => Hrel _ _) l L H))).
Qed.

Definition src_seq_min_in_seq (T : eqType) : Prop := ltac:(type_of_term (@seq_min_in_seq T)).
Definition tgt_seq_min_in_seq (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_min_in_seq T (ct_decidable_eq T))).
Theorem seq_min_in_seq_correspondence (T : eqType) : PropSPropRel (src_seq_min_in_seq T) (tgt_seq_min_in_seq T).
Proof.
  unfold src_seq_min_in_seq, tgt_seq_min_in_seq.
  apply: cm_forall_rel => relR relL Hrel. apply: cm_forall_list => l L H. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cm_argmin_eq T T T (ct_decidable_eq T) relR relL (cmid T) (I.id T) (fun a b => Hrel _ _) l L H (Some x)) (cm_mem T x l L H)).
Qed.

Definition src_seq_max_in_seq (T : eqType) : Prop := ltac:(type_of_term (@seq_max_in_seq T)).
Definition tgt_seq_max_in_seq (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_max_in_seq T (ct_decidable_eq T))).
Theorem seq_max_in_seq_correspondence (T : eqType) : PropSPropRel (src_seq_max_in_seq T) (tgt_seq_max_in_seq T).
Proof.
  unfold src_seq_max_in_seq, tgt_seq_max_in_seq.
  apply: cm_forall_rel => relR relL Hrel. apply: cm_forall_list => l L H. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cm_argmax_eq T T T (ct_decidable_eq T) relR relL (cmid T) (I.id T) (fun a b => Hrel _ _) l L H (Some x)) (cm_mem T x l L H)).
Qed.

Definition src_seq_min_computes_min (T : eqType) : Prop := ltac:(type_of_term (@seq_min_computes_min T)).
Definition tgt_seq_min_computes_min (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_min_computes_min T (ct_decidable_eq T))).
Theorem seq_min_computes_min_correspondence (T : eqType) : PropSPropRel (src_seq_min_computes_min T) (tgt_seq_min_computes_min T).
Proof.
  unfold src_seq_min_computes_min, tgt_seq_min_computes_min.
  apply: cm_forall_rel => relR relL Hrel.
  apply: ct_imp; first exact (cm_transitive T relR relL Hrel).
  apply: cm_forall_list => l L H.
  apply: ct_imp.
  - apply: ct_forall_identity => x. apply: ct_forall_identity => y.
    apply: ct_imp; first exact (cm_mem T x l L H).
    exact (ct_imp _ _ _ _ (cm_mem T y l L H) (ct_bool_truth _ _ (ct_bool_or _ _ _ _ (Hrel _ _) (Hrel _ _)))).
  - apply: ct_forall_identity => x. apply: ct_forall_identity => y.
    apply: ct_imp; first exact (cm_argmin_eq T T T (ct_decidable_eq T) relR relL (cmid T) (I.id T) (fun a b => Hrel _ _) l L H (Some x)).
    exact (ct_imp _ _ _ _ (cm_mem T y l L H) (ct_bool_truth _ _ (Hrel _ _))).
Qed.

Definition src_seq_max_computes_max (T : eqType) : Prop := ltac:(type_of_term (@seq_max_computes_max T)).
Definition tgt_seq_max_computes_max (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_max_computes_max T (ct_decidable_eq T))).
Theorem seq_max_computes_max_correspondence (T : eqType) : PropSPropRel (src_seq_max_computes_max T) (tgt_seq_max_computes_max T).
Proof.
  unfold src_seq_max_computes_max, tgt_seq_max_computes_max.
  apply: cm_forall_rel => relR relL Hrel.
  apply: ct_imp; first exact (cm_transitive T relR relL Hrel).
  apply: cm_forall_list => l L H.
  apply: ct_imp.
  - apply: ct_forall_identity => x. apply: ct_forall_identity => y.
    apply: ct_imp; first exact (cm_mem T x l L H).
    exact (ct_imp _ _ _ _ (cm_mem T y l L H) (ct_bool_truth _ _ (ct_bool_or _ _ _ _ (Hrel _ _) (Hrel _ _)))).
  - apply: ct_forall_identity => x. apply: ct_forall_identity => y.
    apply: ct_imp; first exact (cm_argmax_eq T T T (ct_decidable_eq T) relR relL (cmid T) (I.id T) (fun a b => Hrel _ _) l L H (Some x)).
    exact (ct_imp _ _ _ _ (cm_mem T y l L H) (ct_bool_truth _ _ (Hrel _ _))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements: [seq_argmin_nat]/[seq_argmax_nat] *)

Lemma cm_forall_natfun (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall FR FL, (forall x, SubNatRel (FR x) (FL x)) -> PropSPropRel (PR FR) (PL FL)) ->
  PropSPropRel (forall F, PR F) (forall F, PL F).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR FL. exact (prop_to_sprop _ _ (H (fun x => sub_nat_to_rocq (FL x)) FL (fun x => sub_nat_rel_surjective _)) (HR _)).
  - intro HL. apply strictly_inhabits. intro FR.
    exact (sprop_to_prop _ _ (H FR (fun x => sub_nat_to_imported (FR x)) (fun x => sub_nat_rel_canonical _)) (HL _)).
Qed.

Definition src_seq_argmin_nat_exists (T : eqType) : Prop := ltac:(type_of_term (@seq_argmin_nat_exists T)).
Definition tgt_seq_argmin_nat_exists (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_argmin_nat_exists T (ct_decidable_eq T))).
Theorem seq_argmin_nat_exists_correspondence (T : eqType) : PropSPropRel (src_seq_argmin_nat_exists T) (tgt_seq_argmin_nat_exists T).
Proof.
  unfold src_seq_argmin_nat_exists, tgt_seq_argmin_nat_exists.
  apply: cm_forall_natfun => FR FL HF. apply: cm_forall_list => l L H. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cm_mem T x l L H)
           (ct_bool_truth _ _ (cm_argmin_neq T nat Lean.Nat I.instDecidableEqNat leq cm_le FR FL (cm_le_comp T FR FL HF) l L H))).
Qed.

Definition src_seq_argmax_nat_exists (T : eqType) : Prop := ltac:(type_of_term (@seq_argmax_nat_exists T)).
Definition tgt_seq_argmax_nat_exists (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_argmax_nat_exists T (ct_decidable_eq T))).
Theorem seq_argmax_nat_exists_correspondence (T : eqType) : PropSPropRel (src_seq_argmax_nat_exists T) (tgt_seq_argmax_nat_exists T).
Proof.
  unfold src_seq_argmax_nat_exists, tgt_seq_argmax_nat_exists.
  apply: cm_forall_natfun => FR FL HF. apply: cm_forall_list => l L H. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cm_mem T x l L H)
           (ct_bool_truth _ _ (cm_argmax_neq T nat Lean.Nat I.instDecidableEqNat leq cm_le FR FL (cm_le_comp T FR FL HF) l L H))).
Qed.

Definition src_seq_argmin_nat_in_seq (T : eqType) : Prop := ltac:(type_of_term (@seq_argmin_nat_in_seq T)).
Definition tgt_seq_argmin_nat_in_seq (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_argmin_nat_in_seq T (ct_decidable_eq T))).
Theorem seq_argmin_nat_in_seq_correspondence (T : eqType) : PropSPropRel (src_seq_argmin_nat_in_seq T) (tgt_seq_argmin_nat_in_seq T).
Proof.
  unfold src_seq_argmin_nat_in_seq, tgt_seq_argmin_nat_in_seq.
  apply: cm_forall_natfun => FR FL HF. apply: cm_forall_list => l L H. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cm_argmin_eq T nat Lean.Nat I.instDecidableEqNat leq cm_le FR FL (cm_le_comp T FR FL HF) l L H (Some x))
           (cm_mem T x l L H)).
Qed.

Definition src_seq_argmax_nat_in_seq (T : eqType) : Prop := ltac:(type_of_term (@seq_argmax_nat_in_seq T)).
Definition tgt_seq_argmax_nat_in_seq (T : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_argmax_nat_in_seq T (ct_decidable_eq T))).
Theorem seq_argmax_nat_in_seq_correspondence (T : eqType) : PropSPropRel (src_seq_argmax_nat_in_seq T) (tgt_seq_argmax_nat_in_seq T).
Proof.
  unfold src_seq_argmax_nat_in_seq, tgt_seq_argmax_nat_in_seq.
  apply: cm_forall_natfun => FR FL HF. apply: cm_forall_list => l L H. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cm_argmax_eq T nat Lean.Nat I.instDecidableEqNat leq cm_le FR FL (cm_le_comp T FR FL HF) l L H (Some x))
           (cm_mem T x l L H)).
Qed.

Definition src_seq_argmin_nat_computes_min (T : eqType) : Prop := ltac:(type_of_term (@seq_argmin_nat_computes_min T)).
Definition tgt_seq_argmin_nat_computes_min (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_argmin_nat_computes_min T (ct_decidable_eq T))).
Theorem seq_argmin_nat_computes_min_correspondence (T : eqType) :
  PropSPropRel (src_seq_argmin_nat_computes_min T) (tgt_seq_argmin_nat_computes_min T).
Proof.
  unfold src_seq_argmin_nat_computes_min, tgt_seq_argmin_nat_computes_min.
  apply: cm_forall_natfun => FR FL HF. apply: cm_forall_list => l L H.
  apply: ct_forall_identity => x. apply: ct_forall_identity => y.
  apply: ct_imp; first exact (cm_argmin_eq T nat Lean.Nat I.instDecidableEqNat leq cm_le FR FL (cm_le_comp T FR FL HF) l L H (Some x)).
  exact (ct_imp _ _ _ _ (cm_mem T y l L H) (sub_nat_le_correspondence _ _ _ _ (HF x) (HF y))).
Qed.

Definition src_seq_argmax_nat_computes_max (T : eqType) : Prop := ltac:(type_of_term (@seq_argmax_nat_computes_max T)).
Definition tgt_seq_argmax_nat_computes_max (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_argmax_nat_computes_max T (ct_decidable_eq T))).
Theorem seq_argmax_nat_computes_max_correspondence (T : eqType) :
  PropSPropRel (src_seq_argmax_nat_computes_max T) (tgt_seq_argmax_nat_computes_max T).
Proof.
  unfold src_seq_argmax_nat_computes_max, tgt_seq_argmax_nat_computes_max.
  apply: cm_forall_natfun => FR FL HF. apply: cm_forall_list => l L H.
  apply: ct_forall_identity => x. apply: ct_forall_identity => y.
  apply: ct_imp; first exact (cm_argmax_eq T nat Lean.Nat I.instDecidableEqNat leq cm_le FR FL (cm_le_comp T FR FL HF) l L H (Some x)).
  exact (ct_imp _ _ _ _ (cm_mem T y l L H) (sub_nat_le_correspondence _ _ _ _ (HF y) (HF x))).
Qed.

(* ------------------------------------------------------------------ *)
(** * [seq_argmin_k] and [rem] *)

Lemma cm_erase_step (T : eqType) a as' b :
  Logic.eq (I.List_erase T (I.instBEqOfDecidableEq T (ct_decidable_eq T)) (I.List_cons T a as') b)
    (I.List_filter_match_1 (fun _ => I.List T) (I.Decidable_decide (Lean.eq a b) (ct_decidable_eq T a b))
       (fun _ => as') (fun _ => I.List_cons T a (I.List_erase T (I.instBEqOfDecidableEq T (ct_decidable_eq T)) as' b))).
Proof. reflexivity. Qed.

Lemma cm_rem (T : eqType) (x : T) : forall l,
  Logic.eq (cl_map cid (rem x l)) (I.List_erase T (I.instBEqOfDecidableEq T (ct_decidable_eq T)) (cl_map cid l) x).
Proof.
  elim => [|y l IH] //=. rewrite cm_erase_step (ct_bool_rel_logic _ _ (ct_decide_eq T y x)).
  case: (y == x) => //=. by rewrite IH.
Qed.

Section ArgK.
Variables (T1 T2 : eqType) (relR : T2 -> T2 -> bool) (relL : T2 -> T2 -> I.Bool) (F : T1 -> T2).
Hypothesis Hrel : forall a b, CtBoolRel (relR a b) (relL a b).
Notation d1 := (ct_decidable_eq T1).
Notation d2 := (ct_decidable_eq T2).

Lemma cm_argmin_k_step l k :
  Logic.eq (I.Prosa_Classic_Util_Minmax_seq_argmin_k T1 T2 d1 d2 relL F l (Lean.Nat_succ k))
    (I.Prosa_Classic_Util_Minmax_seq_argmin_match_1 T1 (fun _ => I.List T1)
       (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2 d1 d2 relL F l)
       (fun m => I.List_cons T1 m (I.Prosa_Classic_Util_Minmax_seq_argmin_k T1 T2 d1 d2 relL F
                   (I.List_erase T1 (I.instBEqOfDecidableEq T1 d1) l m) k))
       (fun _ => I.List_nil T1)).
Proof. reflexivity. Qed.

Theorem seq_argmin_k_correspondence : forall k l,
  Logic.eq (cl_map cid (seq_argmin_k relR F l k))
    (I.Prosa_Classic_Util_Minmax_seq_argmin_k T1 T2 d1 d2 relL F (cl_map cid l) (sub_nat_to_imported k)).
Proof.
  elim => [|k IH] l //=. rewrite cm_argmin_k_step -(seq_argmin_correspondence T1 T2 relR relL Hrel F l).
  case: (seq_argmin relR F l) => [m|] //=. by rewrite -cm_rem -IH.
Qed.
End ArgK.

Lemma cm_neq_nil (T : eqType) s L (H : ClListRel cid s L) :
  CtBoolRel (s != [::]) (I.Bool_not (I.Decidable_decide (Lean.eq L (I.List_nil T)) (I.List_instDecidableEqNil T L))).
Proof.
  destruct H. apply: ct_bool_not. apply: ct_decide_bool. apply prop_sprop_rel_intro.
  - move=> /eqP ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. have E' := imported_eq_to_coq_eq _ _ E. clear E. move: E'.
    by case: s.
Qed.

Definition src_seq_argmin_k_exists (T1 T2 : eqType) : Prop := ltac:(type_of_term (@seq_argmin_k_exists T1 T2)).
Definition tgt_seq_argmin_k_exists (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Minmax_seq_argmin_k_exists T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem seq_argmin_k_exists_correspondence (T1 T2 : eqType) :
  PropSPropRel (src_seq_argmin_k_exists T1 T2) (tgt_seq_argmin_k_exists T1 T2).
Proof.
  unfold src_seq_argmin_k_exists, tgt_seq_argmin_k_exists.
  apply: cm_forall_rel => relR relL Hrel. apply: ct_forall_identity => F.
  apply: ct_forall_nat => k kL Hk. apply: cm_forall_list => l L H. apply: ct_forall_identity => x.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical 1) Hk).
  apply: ct_imp; first exact (cm_mem T1 x l L H).
  apply: ct_bool_truth. apply: cm_neq_nil. destruct H. rewrite -(imported_eq_to_coq_eq _ _ Hk).
  apply: coq_eq_to_imported_eq. exact (seq_argmin_k_correspondence T1 T2 relR relL F Hrel k l).
Qed.

(* ------------------------------------------------------------------ *)
(** * Natural-number sequences (Lean's [Set]-level lists) *)

Fixpoint cm_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cm_natl s') end.
Fixpoint cm_unnatl (l : I.List_inst1 Lean.Nat) : seq nat :=
  match l with I.List_nil_inst1 => [::] | I.List_cons_inst1 x l' => sub_nat_to_rocq x :: cm_unnatl l' end.
Lemma cm_natl_unnatl l : Logic.eq (cm_natl (cm_unnatl l)) l.
Proof. induction l as [|x l IH]; first reflexivity. cbn. by rewrite sub_nat_imported_roundtrip IH. Qed.
Lemma cm_unnatl_natl s : Logic.eq (cm_unnatl (cm_natl s)) s.
Proof. elim: s => [|x s IH] //=. by rewrite sub_nat_rocq_roundtrip IH. Qed.

Definition cm_opt1 (o : option nat) : I.Option_inst1 Lean.Nat :=
  if o is Some x then I.Option_some_inst1 _ (sub_nat_to_imported x) else I.Option_none_inst1 _.
Definition cm_unopt1 (o : I.Option_inst1 Lean.Nat) : option nat :=
  match o with I.Option_some_inst1 x => Some (sub_nat_to_rocq x) | I.Option_none_inst1 => None end.
Lemma cm_unopt1_opt1 o : Logic.eq (cm_unopt1 (cm_opt1 o)) o. Proof. case: o => //= x. by rewrite sub_nat_rocq_roundtrip. Qed.

Lemma cm_opt1_eq (o1 o2 : option nat) : PropSPropRel (Logic.eq o1 o2) (Lean.eq (cm_opt1 o1) (cm_opt1 o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := f_equal cm_unopt1 (imported_eq_to_coq_eq _ _ E).
    by rewrite !cm_unopt1_opt1 in E'.
Qed.

Lemma cm_forall_natl (PR : seq nat -> Prop) (PL : I.List_inst1 Lean.Nat -> SProp) :
  (forall s, PropSPropRel (PR s) (PL (cm_natl s))) -> PropSPropRel (forall s, PR s) (forall l, PL l).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR l. have S := prop_to_sprop _ _ (H (cm_unnatl l)) (HR _). rewrite cm_natl_unnatl in S. exact S.
  - intro HL. apply strictly_inhabits. intro s. exact (sprop_to_prop _ _ (H s) (HL _)).
Qed.

Fixpoint cm_natl_mem_forward (x : nat) (s : seq nat) {struct s} : x \in s -> I.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x) (cm_natl s) :=
  match s as s0 return x \in s0 -> I.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x) (cm_natl s0) with
  | [::] => fun H => cl_false_elim_s _ H
  | y :: s' =>
      match @eqP _ x y in reflect _ b return (b || (x \in s')) -> I.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x) (I.List_cons_inst1 _ (sub_nat_to_imported y) (cm_natl s')) with
      | ReflectT E => fun _ =>
          match E in Logic.eq _ z return I.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x) (I.List_cons_inst1 _ (sub_nat_to_imported z) (cm_natl s')) with
          | Logic.eq_refl => I.List_Mem_head_inst1 Lean.Nat (sub_nat_to_imported x) _
          end
      | ReflectF _ => fun H => I.List_Mem_tail_inst1 Lean.Nat (sub_nat_to_imported x) (sub_nat_to_imported y) _ (cm_natl_mem_forward x s' H)
      end
  end.

Fixpoint cm_natl_mem_backward (a : Lean.Nat) (l : I.List_inst1 Lean.Nat) (H : I.List_Mem_inst1 Lean.Nat a l) :
    StrictlyInhabited (sub_nat_to_rocq a \in cm_unnatl l) :=
  match H with
  | I.List_Mem_head_inst1 l' => strictly_inhabits (mem_head (sub_nat_to_rocq a) (cm_unnatl l'))
  | I.List_Mem_tail_inst1 y l' Ht =>
      match cm_natl_mem_backward a l' Ht with
      | strictly_inhabits Hm => strictly_inhabits (introT orP (or_intror Hm) : sub_nat_to_rocq a \in sub_nat_to_rocq y :: cm_unnatl l')
      end
  end.

Lemma cm_natl_mem (x : nat) (s : seq nat) xL : SubNatRel x xL ->
  PropSPropRel (x \in s) (I.Membership_mem_inst3 Lean.Nat (I.List_inst1 Lean.Nat) (I.List_instMembership_inst1 Lean.Nat) (cm_natl s) xL).
Proof.
  intro Hx. rewrite -(imported_eq_to_coq_eq _ _ Hx). apply prop_sprop_rel_intro; first exact (cm_natl_mem_forward x s).
  intro H. have S := cm_natl_mem_backward _ _ H. rewrite sub_nat_rocq_roundtrip cm_unnatl_natl in S. exact S.
Qed.

Definition cm_lefun : Lean.Nat -> Lean.Nat -> I.Bool := fun x y => I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat x y) (I.Nat_decLe x y).

Lemma cm_argmin1_step x l :
  Logic.eq (I.Prosa_Classic_Util_Minmax_seq_argmin_inst3 Lean.Nat Lean.Nat I.instDecidableEqNat I.instDecidableEqNat cm_lefun (I.id Lean.Nat)
              (I.List_cons_inst1 Lean.Nat x l))
    (I.Prosa_Classic_Util_Minmax_seq_argmin_match_1_inst1 Lean.Nat (fun _ => I.Option_inst1 Lean.Nat)
       (I.Prosa_Classic_Util_Minmax_seq_argmin_inst3 Lean.Nat Lean.Nat I.instDecidableEqNat I.instDecidableEqNat cm_lefun (I.id Lean.Nat) l)
       (fun y => I.ite (I.Option_inst1 Lean.Nat) (Lean.eq (cm_lefun x y) I.Bool_true) (I.instDecidableEqBool (cm_lefun x y) I.Bool_true)
                   (I.Option_some_inst1 Lean.Nat x) (I.Option_some_inst1 Lean.Nat y))
       (fun _ => I.Option_some_inst1 Lean.Nat x)).
Proof. reflexivity. Qed.

Lemma cm_argmax1_step x l :
  Logic.eq (I.Prosa_Classic_Util_Minmax_seq_argmax_inst3 Lean.Nat Lean.Nat I.instDecidableEqNat I.instDecidableEqNat cm_lefun (I.id Lean.Nat)
              (I.List_cons_inst1 Lean.Nat x l))
    (I.Prosa_Classic_Util_Minmax_seq_argmin_match_1_inst1 Lean.Nat (fun _ => I.Option_inst1 Lean.Nat)
       (I.Prosa_Classic_Util_Minmax_seq_argmax_inst3 Lean.Nat Lean.Nat I.instDecidableEqNat I.instDecidableEqNat cm_lefun (I.id Lean.Nat) l)
       (fun y => I.ite (I.Option_inst1 Lean.Nat) (Lean.eq (cm_lefun y x) I.Bool_true) (I.instDecidableEqBool (cm_lefun y x) I.Bool_true)
                   (I.Option_some_inst1 Lean.Nat x) (I.Option_some_inst1 Lean.Nat y))
       (fun _ => I.Option_some_inst1 Lean.Nat x)).
Proof. reflexivity. Qed.

Lemma cm_lefun_rel a b : CtBoolRel (a <= b) (cm_lefun (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof. exact (ct_decide_le _ _ _ _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b)). Qed.

Theorem seq_min_nat_correspondence : forall l,
  Logic.eq (cm_opt1 (seq_min_nat l)) (I.Prosa_Classic_Util_Minmax_seq_min_nat (cm_natl l)).
Proof.
  rewrite /seq_min_nat. elim => [|x l IH] //.
  change (Logic.eq (cm_opt1 (seq_argmin leq (@Datatypes.id nat) (x :: l)))
    (I.Prosa_Classic_Util_Minmax_seq_argmin_inst3 Lean.Nat Lean.Nat I.instDecidableEqNat I.instDecidableEqNat cm_lefun (I.id Lean.Nat)
       (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported x) (cm_natl l)))).
  rewrite cm_argmin1_step. change (I.Prosa_Classic_Util_Minmax_seq_argmin_inst3 Lean.Nat Lean.Nat I.instDecidableEqNat I.instDecidableEqNat cm_lefun (I.id Lean.Nat) (cm_natl l))
    with (I.Prosa_Classic_Util_Minmax_seq_min_nat (cm_natl l)). rewrite -IH /=.
  case: (seq_argmin leq (@Datatypes.id nat) l) => [y|] //=.
  rewrite (ct_bool_rel_logic _ _ (cm_lefun_rel x y)). by case: (x <= y).
Qed.

Theorem seq_max_nat_correspondence : forall l,
  Logic.eq (cm_opt1 (seq_max_nat l)) (I.Prosa_Classic_Util_Minmax_seq_max_nat (cm_natl l)).
Proof.
  rewrite /seq_max_nat. elim => [|x l IH] //.
  change (Logic.eq (cm_opt1 (seq_argmax leq (@Datatypes.id nat) (x :: l)))
    (I.Prosa_Classic_Util_Minmax_seq_argmax_inst3 Lean.Nat Lean.Nat I.instDecidableEqNat I.instDecidableEqNat cm_lefun (I.id Lean.Nat)
       (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported x) (cm_natl l)))).
  rewrite cm_argmax1_step. change (I.Prosa_Classic_Util_Minmax_seq_argmax_inst3 Lean.Nat Lean.Nat I.instDecidableEqNat I.instDecidableEqNat cm_lefun (I.id Lean.Nat) (cm_natl l))
    with (I.Prosa_Classic_Util_Minmax_seq_max_nat (cm_natl l)). rewrite -IH /=.
  case: (seq_argmax leq (@Datatypes.id nat) l) => [y|] //=.
  rewrite (ct_bool_rel_logic _ _ (cm_lefun_rel y x)). by case: (y <= x).
Qed.

Lemma cm_opt1_eq_rel (o : option nat) oL x : Logic.eq oL (cm_opt1 o) ->
  PropSPropRel (Logic.eq o (Some x)) (Lean.eq oL (I.Option_some_inst1 Lean.Nat (sub_nat_to_imported x))).
Proof. intros ->. exact (cm_opt1_eq o (Some x)). Qed.

Lemma cm_neq_none1 (o : option nat) oL (Ho : Logic.eq oL (cm_opt1 o)) dec :
  CtBoolRel (o != None) (I.Bool_not (I.Decidable_decide (Lean.eq oL (I.Option_none_inst1 Lean.Nat)) dec)).
Proof.
  subst oL. apply: ct_bool_not. apply: ct_decide_bool. apply prop_sprop_rel_intro.
  - move=> /eqP ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. have E' := f_equal cm_unopt1 (imported_eq_to_coq_eq _ _ E).
    by rewrite cm_unopt1_opt1 in E'.
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements: [seq_min_nat]/[seq_max_nat] *)

Definition src_seq_min_nat_exists : Prop := ltac:(type_of_term seq_min_nat_exists).
Definition tgt_seq_min_nat_exists : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Minmax_seq_min_nat_exists).
Theorem seq_min_nat_exists_correspondence : PropSPropRel src_seq_min_nat_exists tgt_seq_min_nat_exists.
Proof.
  unfold src_seq_min_nat_exists, tgt_seq_min_nat_exists.
  apply: cm_forall_natl => l. apply: ct_forall_nat => x xL Hx.
  apply: ct_imp; first exact (cm_natl_mem x l xL Hx).
  exact (ct_bool_truth _ _ (cm_neq_none1 _ _ (Logic.eq_sym (seq_min_nat_correspondence l)) _)).
Qed.

Definition src_seq_max_nat_exists : Prop := ltac:(type_of_term seq_max_nat_exists).
Definition tgt_seq_max_nat_exists : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Minmax_seq_max_nat_exists).
Theorem seq_max_nat_exists_correspondence : PropSPropRel src_seq_max_nat_exists tgt_seq_max_nat_exists.
Proof.
  unfold src_seq_max_nat_exists, tgt_seq_max_nat_exists.
  apply: cm_forall_natl => l. apply: ct_forall_nat => x xL Hx.
  apply: ct_imp; first exact (cm_natl_mem x l xL Hx).
  exact (ct_bool_truth _ _ (cm_neq_none1 _ _ (Logic.eq_sym (seq_max_nat_correspondence l)) _)).
Qed.

Definition src_seq_min_nat_in_seq : Prop := ltac:(type_of_term seq_min_nat_in_seq).
Definition tgt_seq_min_nat_in_seq : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Minmax_seq_min_nat_in_seq).
Theorem seq_min_nat_in_seq_correspondence : PropSPropRel src_seq_min_nat_in_seq tgt_seq_min_nat_in_seq.
Proof.
  unfold src_seq_min_nat_in_seq, tgt_seq_min_nat_in_seq.
  apply: cm_forall_natl => l. apply: ct_forall_nat => x xL Hx. rewrite -(imported_eq_to_coq_eq _ _ Hx).
  exact (ct_imp _ _ _ _ (cm_opt1_eq_rel _ _ x (Logic.eq_sym (seq_min_nat_correspondence l)))
           (cm_natl_mem x l _ (sub_nat_rel_canonical x))).
Qed.

Definition src_seq_max_nat_in_seq : Prop := ltac:(type_of_term seq_max_nat_in_seq).
Definition tgt_seq_max_nat_in_seq : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Minmax_seq_max_nat_in_seq).
Theorem seq_max_nat_in_seq_correspondence : PropSPropRel src_seq_max_nat_in_seq tgt_seq_max_nat_in_seq.
Proof.
  unfold src_seq_max_nat_in_seq, tgt_seq_max_nat_in_seq.
  apply: cm_forall_natl => l. apply: ct_forall_nat => x xL Hx. rewrite -(imported_eq_to_coq_eq _ _ Hx).
  exact (ct_imp _ _ _ _ (cm_opt1_eq_rel _ _ x (Logic.eq_sym (seq_max_nat_correspondence l)))
           (cm_natl_mem x l _ (sub_nat_rel_canonical x))).
Qed.

Definition src_seq_min_nat_computes_min : Prop := ltac:(type_of_term seq_min_nat_computes_min).
Definition tgt_seq_min_nat_computes_min : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Minmax_seq_min_nat_computes_min).
Theorem seq_min_nat_computes_min_correspondence : PropSPropRel src_seq_min_nat_computes_min tgt_seq_min_nat_computes_min.
Proof.
  unfold src_seq_min_nat_computes_min, tgt_seq_min_nat_computes_min.
  apply: cm_forall_natl => l. apply: ct_forall_nat => x xL Hx. apply: ct_forall_nat => y yL Hy.
  apply: ct_imp.
  - rewrite -(imported_eq_to_coq_eq _ _ Hx). exact (cm_opt1_eq_rel _ _ x (Logic.eq_sym (seq_min_nat_correspondence l))).
  - exact (ct_imp _ _ _ _ (cm_natl_mem y l yL Hy) (sub_nat_le_correspondence _ _ _ _ Hx Hy)).
Qed.

Definition src_seq_max_nat_computes_max : Prop := ltac:(type_of_term seq_max_nat_computes_max).
Definition tgt_seq_max_nat_computes_max : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Minmax_seq_max_nat_computes_max).
Theorem seq_max_nat_computes_max_correspondence : PropSPropRel src_seq_max_nat_computes_max tgt_seq_max_nat_computes_max.
Proof.
  unfold src_seq_max_nat_computes_max, tgt_seq_max_nat_computes_max.
  apply: cm_forall_natl => l. apply: ct_forall_nat => x xL Hx. apply: ct_forall_nat => y yL Hy.
  apply: ct_imp.
  - rewrite -(imported_eq_to_coq_eq _ _ Hx). exact (cm_opt1_eq_rel _ _ x (Logic.eq_sym (seq_max_nat_correspondence l))).
  - exact (ct_imp _ _ _ _ (cm_natl_mem y l yL Hy) (sub_nat_le_correspondence _ _ _ _ Hy Hx)).
Qed.

(* ------------------------------------------------------------------ *)
(** * [values_between], [min_nat_cond], [max_nat_cond] *)

Definition cm_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cm_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cm_one) (cm_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cm_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cm_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cm_filter1 (pR : nat -> bool) (pL : Lean.Nat -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL (sub_nat_to_imported x))) : forall s,
  Logic.eq (cm_natl (filter pR s)) (I.List_filter_inst1 Lean.Nat pL (cm_natl s)).
Proof.
  elim => [|x s IH] //=.
  have -> : Logic.eq (I.List_filter_inst1 Lean.Nat pL (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported x) (cm_natl s)))
      (match pL (sub_nat_to_imported x) with
       | I.Bool_true => I.List_cons_inst1 Lean.Nat (sub_nat_to_imported x) (I.List_filter_inst1 Lean.Nat pL (cm_natl s))
       | I.Bool_false => I.List_filter_inst1 Lean.Nat pL (cm_natl s) end).
  { cbn. destruct (pL (sub_nat_to_imported x)); reflexivity. }
  rewrite (ct_bool_rel_logic _ _ (Hp x)) -IH. by case: (pR x).
Qed.

Lemma cm_enum_vals b : Logic.eq (map (@nat_of_ord b) (enum 'I_b)) (iota 0 b).
Proof. exact (val_enum_ord b). Qed.

Theorem values_between_correspondence a b :
  Logic.eq (cm_natl (values_between a b)) (I.Prosa_Classic_Util_Minmax_values_between (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  change (Logic.eq (cm_natl (values_between a b))
    (I.List_filter_inst1 Lean.Nat (fun x => cm_lefun (sub_nat_to_imported a) x)
       (I.List_map_inst3 (Fin (sub_nat_to_imported b)) Lean.Nat (I.Fin_val (sub_nat_to_imported b)) (I.List_finRange (sub_nat_to_imported b))))).
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicMinmaxInterface_finRange_map_val (sub_nat_to_imported b))).
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cm_iota_range b 0) /values_between cm_enum_vals.
  apply: cm_filter1 => x. exact (cm_lefun_rel a x).
Qed.

Lemma cm_vb_rel a aL b bL : SubNatRel a aL -> SubNatRel b bL ->
  Logic.eq (I.Prosa_Classic_Util_Minmax_values_between aL bL) (cm_natl (values_between a b)).
Proof.
  intros Ha Hb. rewrite -(imported_eq_to_coq_eq _ _ Ha) -(imported_eq_to_coq_eq _ _ Hb).
  exact (Logic.eq_sym (values_between_correspondence a b)).
Qed.

Definition CmNatPredRel (pR : nat -> bool) (pL : Lean.Nat -> I.Bool) : SProp :=
  forall kR kL, SubNatRel kR kL -> CtBoolRel (pR kR) (pL kL).

Lemma cl_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma cm_forall_nat_pred (PR : pred nat -> Prop) (PL : (Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CmNatPredRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  apply (cl_forall_cover_sprop _ _ CmNatPredRel (fun pR kL => ct_b2l (pR (sub_nat_to_rocq kL)))
           (fun pL kR => ct_l2b (pL (sub_nat_to_imported kR)))).
  - intros pR kR kL Hk. rewrite (cl_nat_input _ _ Hk). exact (ct_bool_canonical _).
  - intros pL kR kL Hk. rewrite (cl_nat_logic _ _ Hk). exact (ct_bool_surjective _).
Qed.

Lemma cm_forall_natfun1 (PR : (nat -> bool) -> Prop) (PL : (Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CmNatPredRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (cm_forall_nat_pred PR PL). Qed.

Theorem min_nat_cond_correspondence pR pL (Hp : CmNatPredRel pR pL) a b :
  Logic.eq (cm_opt1 (min_nat_cond pR a b)) (I.Prosa_Classic_Util_Minmax_min_nat_cond pL (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  rewrite /min_nat_cond seq_min_nat_correspondence.
  change (Logic.eq (I.Prosa_Classic_Util_Minmax_seq_min_nat (cm_natl (filter pR (values_between a b))))
    (I.Prosa_Classic_Util_Minmax_seq_min_nat (I.List_filter_inst1 Lean.Nat pL
       (I.Prosa_Classic_Util_Minmax_values_between (sub_nat_to_imported a) (sub_nat_to_imported b))))).
  rewrite -values_between_correspondence (cm_filter1 pR pL (fun x => Hp _ _ (sub_nat_rel_canonical x))).
  reflexivity.
Qed.

Theorem max_nat_cond_correspondence pR pL (Hp : CmNatPredRel pR pL) a b :
  Logic.eq (cm_opt1 (max_nat_cond pR a b)) (I.Prosa_Classic_Util_Minmax_max_nat_cond pL (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  rewrite /max_nat_cond seq_max_nat_correspondence.
  change (Logic.eq (I.Prosa_Classic_Util_Minmax_seq_max_nat (cm_natl (filter pR (values_between a b))))
    (I.Prosa_Classic_Util_Minmax_seq_max_nat (I.List_filter_inst1 Lean.Nat pL
       (I.Prosa_Classic_Util_Minmax_values_between (sub_nat_to_imported a) (sub_nat_to_imported b))))).
  rewrite -values_between_correspondence (cm_filter1 pR pL (fun x => Hp _ _ (sub_nat_rel_canonical x))).
  reflexivity.
Qed.

Lemma cm_cond_rel (min : bool) pR pL (Hp : CmNatPredRel pR pL) a aL b bL : SubNatRel a aL -> SubNatRel b bL ->
  Logic.eq (if min then I.Prosa_Classic_Util_Minmax_min_nat_cond pL aL bL else I.Prosa_Classic_Util_Minmax_max_nat_cond pL aL bL)
           (cm_opt1 (if min then min_nat_cond pR a b else max_nat_cond pR a b)).
Proof.
  intros Ha Hb. rewrite -(imported_eq_to_coq_eq _ _ Ha) -(imported_eq_to_coq_eq _ _ Hb).
  case: min; [exact (Logic.eq_sym (min_nat_cond_correspondence pR pL Hp a b)) | exact (Logic.eq_sym (max_nat_cond_correspondence pR pL Hp a b))].
Qed.

Lemma cm_range_rel a aL x xL b bL : SubNatRel a aL -> SubNatRel x xL -> SubNatRel b bL ->
  CtBoolRel (a <= x < b) (I.Bool_and (cm_lefun aL xL) (I.Decidable_decide (I.LT_lt_inst1 Lean.Nat I.instLTNat xL bL) (I.Nat_decLt xL bL))).
Proof. intros Ha Hx Hb. exact (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Ha Hx) (ct_decide_lt _ _ _ _ Hx Hb)). Qed.

Definition src_mem_values_between : Prop := ltac:(type_of_term mem_values_between).
Definition tgt_mem_values_between : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Minmax_mem_values_between).
Theorem mem_values_between_correspondence : PropSPropRel src_mem_values_between tgt_mem_values_between.
Proof.
  unfold src_mem_values_between, tgt_mem_values_between.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => b bL Hb. apply: ct_forall_nat => x xL Hx.
  apply: ct_bool_eq; last exact (cm_range_rel _ _ _ _ _ _ Ha Hx Hb).
  apply: ct_decide_bool. rewrite (cm_vb_rel _ _ _ _ Ha Hb). exact (cm_natl_mem x _ xL Hx).
Qed.

Definition src_min_nat_cond_exists : Prop := ltac:(type_of_term min_nat_cond_exists).
Definition tgt_min_nat_cond_exists : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Minmax_min_nat_cond_exists).
Theorem min_nat_cond_exists_correspondence : PropSPropRel src_min_nat_cond_exists tgt_min_nat_cond_exists.
Proof.
  unfold src_min_nat_cond_exists, tgt_min_nat_cond_exists.
  apply: cm_forall_natfun1 => pR pL Hp.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => b bL Hb. apply: ct_forall_nat => x xL Hx.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cm_range_rel _ _ _ _ _ _ Ha Hx Hb)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hp _ _ Hx)).
  exact (ct_bool_truth _ _ (cm_neq_none1 _ _ (cm_cond_rel true pR pL Hp _ _ _ _ Ha Hb) _)).
Qed.

Definition src_max_nat_cond_exists : Prop := ltac:(type_of_term max_nat_cond_exists).
Definition tgt_max_nat_cond_exists : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Minmax_max_nat_cond_exists).
Theorem max_nat_cond_exists_correspondence : PropSPropRel src_max_nat_cond_exists tgt_max_nat_cond_exists.
Proof.
  unfold src_max_nat_cond_exists, tgt_max_nat_cond_exists.
  apply: cm_forall_natfun1 => pR pL Hp.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => b bL Hb. apply: ct_forall_nat => x xL Hx.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cm_range_rel _ _ _ _ _ _ Ha Hx Hb)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hp _ _ Hx)).
  exact (ct_bool_truth _ _ (cm_neq_none1 _ _ (cm_cond_rel false pR pL Hp _ _ _ _ Ha Hb) _)).
Qed.

Definition src_min_nat_cond_in_seq : Prop := ltac:(type_of_term min_nat_cond_in_seq).
Definition tgt_min_nat_cond_in_seq : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Minmax_min_nat_cond_in_seq).
Theorem min_nat_cond_in_seq_correspondence : PropSPropRel src_min_nat_cond_in_seq tgt_min_nat_cond_in_seq.
Proof.
  unfold src_min_nat_cond_in_seq, tgt_min_nat_cond_in_seq.
  apply: cm_forall_nat_pred => pR pL Hp.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => b bL Hb. apply: ct_forall_nat => x xL Hx.
  apply: ct_imp.
  - rewrite -(imported_eq_to_coq_eq _ _ Hx). exact (cm_opt1_eq_rel _ _ x (cm_cond_rel true pR pL Hp _ _ _ _ Ha Hb)).
  - exact (ct_and _ _ _ _ (ct_bool_truth _ _ (cm_range_rel _ _ _ _ _ _ Ha Hx Hb)) (ct_bool_truth _ _ (Hp _ _ Hx))).
Qed.

Definition src_max_nat_cond_in_seq : Prop := ltac:(type_of_term max_nat_cond_in_seq).
Definition tgt_max_nat_cond_in_seq : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Minmax_max_nat_cond_in_seq).
Theorem max_nat_cond_in_seq_correspondence : PropSPropRel src_max_nat_cond_in_seq tgt_max_nat_cond_in_seq.
Proof.
  unfold src_max_nat_cond_in_seq, tgt_max_nat_cond_in_seq.
  apply: cm_forall_nat_pred => pR pL Hp.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => b bL Hb. apply: ct_forall_nat => x xL Hx.
  apply: ct_imp.
  - rewrite -(imported_eq_to_coq_eq _ _ Hx). exact (cm_opt1_eq_rel _ _ x (cm_cond_rel false pR pL Hp _ _ _ _ Ha Hb)).
  - exact (ct_and _ _ _ _ (ct_bool_truth _ _ (cm_range_rel _ _ _ _ _ _ Ha Hx Hb)) (ct_bool_truth _ _ (Hp _ _ Hx))).
Qed.

Definition src_min_nat_cond_computes_min : Prop := ltac:(type_of_term min_nat_cond_computes_min).
Definition tgt_min_nat_cond_computes_min : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Minmax_min_nat_cond_computes_min).
Theorem min_nat_cond_computes_min_correspondence : PropSPropRel src_min_nat_cond_computes_min tgt_min_nat_cond_computes_min.
Proof.
  unfold src_min_nat_cond_computes_min, tgt_min_nat_cond_computes_min.
  apply: cm_forall_nat_pred => pR pL Hp.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => b bL Hb. apply: ct_forall_nat => x xL Hx.
  apply: ct_imp.
  - rewrite -(imported_eq_to_coq_eq _ _ Hx). exact (cm_opt1_eq_rel _ _ x (cm_cond_rel true pR pL Hp _ _ _ _ Ha Hb)).
  - apply: ct_forall_nat => y yL Hy.
    apply: ct_imp; first exact (ct_bool_truth _ _ (cm_range_rel _ _ _ _ _ _ Ha Hy Hb)).
    exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (Hp _ _ Hy)) (sub_nat_le_correspondence _ _ _ _ Hx Hy)).
Qed.

Definition src_max_nat_cond_computes_max : Prop := ltac:(type_of_term max_nat_cond_computes_max).
Definition tgt_max_nat_cond_computes_max : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Minmax_max_nat_cond_computes_max).
Theorem max_nat_cond_computes_max_correspondence : PropSPropRel src_max_nat_cond_computes_max tgt_max_nat_cond_computes_max.
Proof.
  unfold src_max_nat_cond_computes_max, tgt_max_nat_cond_computes_max.
  apply: cm_forall_nat_pred => pR pL Hp.
  apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => b bL Hb. apply: ct_forall_nat => x xL Hx.
  apply: ct_imp.
  - rewrite -(imported_eq_to_coq_eq _ _ Hx). exact (cm_opt1_eq_rel _ _ x (cm_cond_rel false pR pL Hp _ _ _ _ Ha Hb)).
  - apply: ct_forall_nat => y yL Hy.
    apply: ct_imp; first exact (ct_bool_truth _ _ (cm_range_rel _ _ _ _ _ _ Ha Hy Hb)).
    exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (Hp _ _ Hy)) (sub_nat_le_correspondence _ _ _ _ Hy Hx)).
Qed.
