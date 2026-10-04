From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
From prosa Require Import classic.util.fixedpoint.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicFixedpoint.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicFixedpointBase.

Module I := ImportedClassicFixedpoint.
Local Open Scope nat_scope.

(** Certificates for [classic/util/fixedpoint.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: type parameters and elements identified (for an [eqType], the Lean
    [DecidableEq] is the eqType's decision procedure); natural numbers by
    [SubNatRel]; Booleans, Boolean relations and options constructor-wise /
    pointwise; functions [nat -> nat] pointwise on related arguments; type
    families [P : T -> Type] identified; all with two-way totals.

    Computation: MathComp's [iter] against the Lean helper [iter] and
    [iter_fixpoint] against its Lean counterpart, by structural induction (the
    Lean side unfolded one step at a time by conversion; the Lean decision
    [decide (x = f x)] is related through [ct_decide_eq]).

    Statements: the source side is the exact elaborated type of the pinned
    lemma (via [type of]; the source proof is not used); the [Type]-valued
    [iter_fixpoint_ind] by a pair of maps. *)

Ltac type_of_term t := let T := type of t in exact T.

Lemma cf_nat_logic nR nL : SubNatRel nR nL -> Logic.eq nL (sub_nat_to_imported nR).
Proof. intro H. exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ H)). Qed.

Lemma cf_nat_input nR nL : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof. intro H. rewrite (cf_nat_logic _ _ H). exact (sub_nat_rocq_roundtrip nR). Qed.

Lemma cf_val_eq (T : Type) (aR aL bR bL : T) :
  Logic.eq aR aL -> Logic.eq bR bL -> PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros -> ->. apply prop_sprop_rel_intro.
  - exact (coq_eq_to_imported_eq _ _).
  - intro H. exact (strictly_inhabits (imported_eq_to_coq_eq _ _ H)).
Qed.

Lemma cf_succ nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                    (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro H. have := sub_add_correspondence _ _ 1 _ H (sub_nat_rel_canonical 1). by rewrite addn1. Qed.

(* ------------------------------------------------------------------ *)
(** * [iter] *)

Lemma cf_iter (T : Type) (f : T -> T) (x : T) : forall n,
  Logic.eq (iter n f x) (I.Prosa_Classic_Util_Fixedpoint_iter T (sub_nat_to_imported n) f x).
Proof.
  elim => [|n IH] //=.
  change (Logic.eq (f (iter n f x)) (f (I.Prosa_Classic_Util_Fixedpoint_iter T (sub_nat_to_imported n) f x))).
  by rewrite IH.
Qed.

Lemma cf_iter_rel (T : Type) (f : T -> T) (x : T) nR nL : SubNatRel nR nL ->
  Logic.eq (iter nR f x) (I.Prosa_Classic_Util_Fixedpoint_iter T nL f x).
Proof. intro H. rewrite (cf_nat_logic _ _ H). exact (cf_iter T f x nR). Qed.

Definition CfNatFunRel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) : SProp :=
  forall a aL, SubNatRel a aL -> SubNatRel (fR a) (fL aL).

Lemma cf_iter_nat fR fL (Hf : CfNatFunRel fR fL) : forall n x xL, SubNatRel x xL ->
  SubNatRel (iter n fR x) (I.Prosa_Classic_Util_Fixedpoint_iter_inst1 Lean.Nat (sub_nat_to_imported n) fL xL).
Proof.
  intro n. induction n as [|n IH]; intros x xL Hx; first exact Hx.
  change (SubNatRel (fR (iter n fR x)) (fL (I.Prosa_Classic_Util_Fixedpoint_iter_inst1 Lean.Nat (sub_nat_to_imported n) fL xL))).
  exact (Hf _ _ (IH x xL Hx)).
Qed.

Lemma cf_iter_nat_rel fR fL (Hf : CfNatFunRel fR fL) nR nL x xL : SubNatRel nR nL -> SubNatRel x xL ->
  SubNatRel (iter nR fR x) (I.Prosa_Classic_Util_Fixedpoint_iter_inst1 Lean.Nat nL fL xL).
Proof. intros Hn Hx. rewrite (cf_nat_logic _ _ Hn). exact (cf_iter_nat fR fL Hf nR x xL Hx). Qed.

Lemma cf_natfun_target_total fL : CfNatFunRel (fun a => sub_nat_to_rocq (fL (sub_nat_to_imported a))) fL.
Proof. intros a aL Ha. rewrite (cf_nat_logic _ _ Ha). exact (sub_nat_rel_surjective _). Qed.

Lemma cf_natfun_source_total fR : CfNatFunRel fR (fun aL => sub_nat_to_imported (fR (sub_nat_to_rocq aL))).
Proof. intros a aL Ha. rewrite (cf_nat_input _ _ Ha). exact (sub_nat_rel_canonical _). Qed.

Lemma cf_forall_natfun (PR : (nat -> nat) -> Prop) (PL : (Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, CfNatFunRel fR fL -> PropSPropRel (PR fR) (PL fL)) -> PropSPropRel (forall f, PR f) (forall f, PL f).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR fL. exact (prop_to_sprop _ _ (H _ _ (cf_natfun_target_total fL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro fR. exact (sprop_to_prop _ _ (H _ _ (cf_natfun_source_total fR)) (HL _)).
Qed.

Lemma cf_forall_rel (A : Type) (PR : (A -> A -> bool) -> Prop) (PL : (A -> A -> I.Bool) -> SProp) :
  (forall pR pL, (forall a b, CtBoolRel (pR a b) (pL a b)) -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H (fun a b => ct_l2b (pL a b)) pL (fun a b => ct_bool_surjective _)) (HR _)).
  - intro HL. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ (H pR (fun a b => ct_b2l (pR a b)) (fun a b => ct_bool_canonical _)) (HL _)).
Qed.

Lemma cf_reflexive (T : Type) (R : T -> T -> bool) RL (HR : forall a b, CtBoolRel (R a b) (RL a b)) :
  PropSPropRel (reflexive R) (forall x, Lean.eq (RL x x) I.Bool_true).
Proof. rewrite /reflexive. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (HR x x)). Qed.

Lemma cf_transitive (T : Type) (R : T -> T -> bool) RL (HR : forall a b, CtBoolRel (R a b) (RL a b)) :
  PropSPropRel (transitive R)
    (forall y x z, Lean.eq (RL x y) I.Bool_true -> Lean.eq (RL y z) I.Bool_true -> Lean.eq (RL x z) I.Bool_true).
Proof.
  rewrite /transitive. apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (HR x y)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (HR y z)) (ct_bool_truth _ _ (HR x z))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem monotone_correspondence (T : Type) (f : T -> T) (R : T -> T -> bool) RL
    (HR : forall a b, CtBoolRel (R a b) (RL a b)) :
  PropSPropRel (fixedpoint.monotone f R) (I.Prosa_Classic_Util_Fixedpoint_monotone T f RL).
Proof.
  apply: ct_forall_identity => x. apply: ct_forall_identity => y.
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (HR x y)) (ct_bool_truth _ _ (HR (f x) (f y)))).
Qed.

Definition cf_opt {A : Type} (o : option A) : I.Option A :=
  if o is Some x then I.Option_some A x else I.Option_none A.

Definition cf_unopt {A : Type} (o : I.Option A) : option A :=
  match o with I.Option_some x => Some x | I.Option_none => None end.
Lemma cf_unopt_opt {A} (o : option A) : Logic.eq (cf_unopt (cf_opt o)) o. Proof. by case: o. Qed.

Lemma cf_opt_eq {A} (o1 o2 : option A) : PropSPropRel (Logic.eq o1 o2) (Lean.eq (cf_opt o1) (cf_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := f_equal cf_unopt (imported_eq_to_coq_eq _ _ E).
    by rewrite !cf_unopt_opt in E'.
Qed.

Theorem iter_fixpoint_correspondence (T : eqType) (f : T -> T) : forall n x,
  Logic.eq (cf_opt (iter_fixpoint f n x))
    (I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint T (ct_decidable_eq T) f (sub_nat_to_imported n) x).
Proof.
  elim => [|n IH] x //.
  have -> : Logic.eq (I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint T (ct_decidable_eq T) f (sub_nat_to_imported n.+1) x)
      (match I.Decidable_decide (Lean.eq x (f x)) (ct_decidable_eq T x (f x)) with
       | I.Bool_true => I.Option_some T x
       | I.Bool_false => I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint T (ct_decidable_eq T) f (sub_nat_to_imported n) (f x) end).
  { cbn. destruct (ct_decidable_eq T x (f x)); reflexivity. }
  rewrite (ct_bool_rel_logic _ _ (ct_decide_eq T x (f x))) -IH /=. by case: (x == f x).
Qed.

Lemma cf_ifp_eq (T : eqType) (f : T -> T) nR nL x (o : option T) : SubNatRel nR nL ->
  PropSPropRel (Logic.eq (iter_fixpoint f nR x) o)
    (Lean.eq (I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint T (ct_decidable_eq T) f nL x) (cf_opt o)).
Proof. intro Hn. rewrite (cf_nat_logic _ _ Hn) -iter_fixpoint_correspondence. exact (cf_opt_eq _ _). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_iter_fix : Prop := ltac:(type_of_term @iter_fix).
Definition tgt_iter_fix : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Fixedpoint_iter_fix).
Theorem iter_fix_correspondence : PropSPropRel src_iter_fix tgt_iter_fix.
Proof.
  unfold src_iter_fix, tgt_iter_fix.
  apply: ct_forall_identity => T. apply: ct_forall_identity => F. apply: ct_forall_identity => x.
  apply: ct_forall_nat => k kL Hk. apply: ct_forall_nat => n nL Hn.
  apply: ct_imp; first exact (cf_val_eq T _ _ _ _ (cf_iter_rel T F x _ _ Hk) (cf_iter_rel T F x _ _ (cf_succ _ _ Hk))).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Hk Hn).
  exact (cf_val_eq T _ _ _ _ (cf_iter_rel T F x _ _ Hn) (cf_iter_rel T F x _ _ (cf_succ _ _ Hn))).
Qed.

Definition src_fun_mon_iter_mon : Prop := ltac:(type_of_term @fun_mon_iter_mon).
Definition tgt_fun_mon_iter_mon : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Fixedpoint_fun_mon_iter_mon).
Theorem fun_mon_iter_mon_correspondence : PropSPropRel src_fun_mon_iter_mon tgt_fun_mon_iter_mon.
Proof.
  unfold src_fun_mon_iter_mon, tgt_fun_mon_iter_mon.
  apply: cf_forall_natfun => fR fL Hf.
  apply: ct_forall_nat => x0 x0L H0. apply: ct_forall_nat => x1 x1L H1. apply: ct_forall_nat => x2 x2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 H2).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H0 (Hf _ _ H0)).
  apply: ct_imp.
  - apply: ct_forall_nat => a aL Ha. apply: ct_forall_nat => b bL Hb.
    exact (ct_imp _ _ _ _ (sub_nat_le_correspondence _ _ _ _ Ha Hb) (sub_nat_le_correspondence _ _ _ _ (Hf _ _ Ha) (Hf _ _ Hb))).
  - exact (sub_nat_le_correspondence _ _ _ _ (cf_iter_nat_rel fR fL Hf _ _ _ _ H1 H0) (cf_iter_nat_rel fR fL Hf _ _ _ _ H2 H0)).
Qed.

Definition src_fun_mon_iter_mon_helper : Prop := ltac:(type_of_term @fun_mon_iter_mon_helper).
Definition tgt_fun_mon_iter_mon_helper : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Fixedpoint_fun_mon_iter_mon_helper).
Theorem fun_mon_iter_mon_helper_correspondence : PropSPropRel src_fun_mon_iter_mon_helper tgt_fun_mon_iter_mon_helper.
Proof.
  unfold src_fun_mon_iter_mon_helper, tgt_fun_mon_iter_mon_helper.
  apply: ct_forall_identity => T. apply: ct_forall_identity => f. apply: cf_forall_rel => le leL Hle.
  apply: ct_forall_identity => x0. apply: ct_forall_nat => x1 x1L H1.
  apply: ct_imp; first exact (cf_reflexive T _ _ Hle).
  apply: ct_imp; first exact (cf_transitive T _ _ Hle).
  apply: ct_imp.
  - apply: ct_forall_nat => x2 x2L H2. rewrite (cf_iter_rel T f x0 _ _ H2). exact (ct_bool_truth _ _ (Hle _ _)).
  - apply: ct_imp.
    + apply: ct_forall_identity => a. apply: ct_forall_identity => b.
      apply: ct_imp; first exact (ct_bool_truth _ _ (Hle _ _)).
      exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (Hle _ _)) (ct_bool_truth _ _ (Hle _ _))).
    + rewrite (cf_iter_rel T f x0 _ _ H1) (cf_iter_rel T f x0 _ _ (cf_succ _ _ H1)). exact (ct_bool_truth _ _ (Hle _ _)).
Qed.

Definition src_fun_mon_iter_mon_generic : Prop := ltac:(type_of_term @fun_mon_iter_mon_generic).
Definition tgt_fun_mon_iter_mon_generic : SProp := ltac:(type_of_term I.Prosa_Classic_Util_Fixedpoint_fun_mon_iter_mon_generic).
Theorem fun_mon_iter_mon_generic_correspondence : PropSPropRel src_fun_mon_iter_mon_generic tgt_fun_mon_iter_mon_generic.
Proof.
  unfold src_fun_mon_iter_mon_generic, tgt_fun_mon_iter_mon_generic.
  apply: ct_forall_identity => T. apply: ct_forall_identity => f. apply: cf_forall_rel => le leL Hle.
  apply: ct_forall_identity => x0. apply: ct_forall_nat => x1 x1L H1. apply: ct_forall_nat => x2 x2L H2.
  apply: ct_imp; first exact (cf_reflexive T _ _ Hle).
  apply: ct_imp; first exact (cf_transitive T _ _ Hle).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 H2).
  apply: ct_imp.
  - apply: ct_forall_identity => a. apply: ct_forall_identity => b.
    apply: ct_imp; first exact (ct_bool_truth _ _ (Hle _ _)).
    exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (Hle _ _)) (ct_bool_truth _ _ (Hle _ _))).
  - apply: ct_imp.
    + apply: ct_forall_nat => x3 x3L H3. rewrite (cf_iter_rel T f x0 _ _ H3). exact (ct_bool_truth _ _ (Hle _ _)).
    + rewrite (cf_iter_rel T f x0 _ _ H1) (cf_iter_rel T f x0 _ _ H2). exact (ct_bool_truth _ _ (Hle _ _)).
Qed.

Definition src_iter_fixpoint_cases (T : eqType) : Prop := ltac:(type_of_term (@iter_fixpoint_cases T)).
Definition tgt_iter_fixpoint_cases (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint_cases T (ct_decidable_eq T))).
Theorem iter_fixpoint_cases_correspondence (T : eqType) : PropSPropRel (src_iter_fixpoint_cases T) (tgt_iter_fixpoint_cases T).
Proof.
  unfold src_iter_fixpoint_cases, tgt_iter_fixpoint_cases.
  apply: ct_forall_identity => f. apply: ct_forall_nat => m mL Hm. apply: ct_forall_identity => x0.
  apply: ct_or; first exact (cf_ifp_eq T f _ _ x0 None Hm).
  apply: ct_exists_identity => y.
  exact (ct_and _ _ _ _ (cf_ifp_eq T f _ _ x0 (Some y) Hm) (ct_eq_rel T y (f y))).
Qed.

Definition src_iter_fixpoint_ind (T : eqType) : Type := ltac:(type_of_term (@iter_fixpoint_ind T)).
Definition tgt_iter_fixpoint_ind (T : eqType) : Type :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint_ind T (ct_decidable_eq T))).
Theorem iter_fixpoint_ind_correspondence (T : eqType) :
  Datatypes.prod (src_iter_fixpoint_ind T -> tgt_iter_fixpoint_ind T) (tgt_iter_fixpoint_ind T -> src_iter_fixpoint_ind T).
Proof.
  split.
  - intros g f mL x0 x HL P P0 ALL.
    have HR := sprop_to_prop _ _ (cf_ifp_eq T f _ _ x0 (Some x) (sub_nat_rel_surjective mL)) HL.
    exact (g f _ x0 x HR P P0 ALL).
  - intros h f m x0 x HR P P0 ALL.
    have HL := prop_to_sprop _ _ (cf_ifp_eq T f _ _ x0 (Some x) (sub_nat_rel_canonical m)) HR.
    exact (h f _ x0 x HL P P0 ALL).
Defined.

Definition src_iter_fixpoint_ge_min (T : eqType) : Prop := ltac:(type_of_term (@iter_fixpoint_ge_min T)).
Definition tgt_iter_fixpoint_ge_min (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint_ge_min T (ct_decidable_eq T))).
Theorem iter_fixpoint_ge_min_correspondence (T : eqType) : PropSPropRel (src_iter_fixpoint_ge_min T) (tgt_iter_fixpoint_ge_min T).
Proof.
  unfold src_iter_fixpoint_ge_min, tgt_iter_fixpoint_ge_min.
  apply: ct_forall_identity => f. apply: cf_forall_rel => R RL HR.
  apply: ct_imp; first exact (cf_transitive T _ _ HR).
  apply: ct_imp; first exact (monotone_correspondence T f R RL HR).
  apply: ct_forall_nat => m mL Hm. apply: ct_forall_identity => x0. apply: ct_forall_identity => x1. apply: ct_forall_identity => x.
  apply: ct_imp; first exact (cf_ifp_eq T f _ _ x1 (Some x) Hm).
  apply: ct_imp; first exact (ct_bool_truth _ _ (HR _ _)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (HR _ _)) (ct_bool_truth _ _ (HR _ _))).
Qed.

Definition src_iter_fixpoint_ge_bottom (T : eqType) : Prop := ltac:(type_of_term (@iter_fixpoint_ge_bottom T)).
Definition tgt_iter_fixpoint_ge_bottom (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint_ge_bottom T (ct_decidable_eq T))).
Theorem iter_fixpoint_ge_bottom_correspondence (T : eqType) :
  PropSPropRel (src_iter_fixpoint_ge_bottom T) (tgt_iter_fixpoint_ge_bottom T).
Proof.
  unfold src_iter_fixpoint_ge_bottom, tgt_iter_fixpoint_ge_bottom.
  apply: ct_forall_identity => f. apply: cf_forall_rel => R RL HR.
  apply: ct_imp; first exact (cf_reflexive T _ _ HR).
  apply: ct_imp; first exact (cf_transitive T _ _ HR).
  apply: ct_imp; first exact (monotone_correspondence T f R RL HR).
  apply: ct_forall_nat => m mL Hm. apply: ct_forall_identity => x0. apply: ct_forall_identity => x.
  apply: ct_imp; first exact (cf_ifp_eq T f _ _ x0 (Some x) Hm).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (HR _ _)) (ct_bool_truth _ _ (HR _ _))).
Qed.
