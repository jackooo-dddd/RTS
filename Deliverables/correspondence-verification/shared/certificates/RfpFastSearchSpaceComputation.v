(* Re-bound copy of the accepted certificates/implementation_refinements_fast_search_space_computation/RefFastSearchSpaceComputationCorrespondence.v: modules renamed (ImportedRefFastSearchSpaceComputation=ImportedRefFPFastSearchSpace,RfsBase=RfpBase,RfsArrivalBound=RfpArrivalBound,RfsTask=RfpTask,RfsArrivalCurve=RfpArrivalCurve,RfsArrivalCurvePrefix=RfpArrivalCurvePrefix), its statement
   correspondences dropped (their statement-only targets are not part of this export), and the commands that mention
   constants absent from this export dropped (the file's report lists them).  Every kept command is unchanged. *)
(** Correspondences for [implementation/refinements/fast_search_space_computation.v].

    The source is the official file, compiled on its official proof closure with CoqEAL 2.1.2 (the module with the
    recorded rewrite-order flag).  The base maps, definition correspondences and statement combinators are those of
    the accepted refinements.v, arrival_bound.v, task.v, arrival_curve.v and arrival_curve_prefix.v certificates,
    re-bound in [RfpBase], [RfpArrivalBound], [RfpTask], [RfpArrivalCurve] and [RfpArrivalCurvePrefix].  Here:
    - the two search-space definitions are related for related inputs (tasks by [TaskRel], numbers by the canonical
      map);
    - the six statements are related by [PropSPropRel], composed from combinators for implication, universal and
      existential quantification, conjunction and disjunction, and from the component relations (order, equality,
      divisibility and inequality of numbers, membership, the accepted definition correspondences).
    No certificate uses its own source or target theorem: statements are taken with [type of], never applied. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div bigop path.
From CoqEAL Require Import hrel param refinements binnat.
From prosa Require Import implementation.refinements.fast_search_space_computation.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefFPFastSearchSpace ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence RfpBase
  RfpArrivalBound RfpTask RfpArrivalCurve RfpArrivalCurvePrefix.
Import Refinements.Op.

Set Warnings "-notation-for-abbreviation,-deprecated".

Module I := ImportedRefFPFastSearchSpace.
Module Rfsc := prosa.implementation.refinements.fast_search_space_computation.
Module Rac := prosa.implementation.refinements.arrival_curve.
Module Rt := prosa.implementation.refinements.task.
Module Dt := prosa.implementation.definitions.task.
Module EAC := prosa.implementation.definitions.extrapolated_arrival_curve.

Abbreviation ISSh := I.Prosa_Implementation_Refinements_FastSearchSpaceComputation_search_space_arrival_curve_prefix_FP_h.
Abbreviation ISS := I.Prosa_Implementation_Refinements_FastSearchSpaceComputation_search_space_arrival_curve_prefix_FP.

(** ** The two definitions *)
Lemma rf_ssh_ex t l r : Lean.eq (lex ne (Rfsc.search_space_arrival_curve_prefix_FP_h t l r)) (ISSh (task_ex t) (ne l) (ne r)).
Proof.
  unfold Rfsc.search_space_arrival_curve_prefix_FP_h. cbv zeta.
  refine (rf_trans _ _ _ (rf_map_ex ne ne predn I.Nat_pred rf_pred_ex _) _).
  refine (rf_congr (I.List_map_inst3 LN LN I.Nat_pred) _ _ _).
  refine (rf_trans _ _ _ (repeat_steps_with_offset_correspondence t _ _ _ (rf_refl _) (rf_refl _)) _).
  refine (rf_congr (IAC_repeat_steps_with_offset (task_ex t)) _ _ _).
  pose hL := IAC_get_horizon_of_task (task_ex t).
  refine (rf_trans _ _ _ (rf_map_ex ne ne (muln (Rac.get_horizon_of_task t)) (fun x => rf_mul hL x)
    (fun a => rf_trans _ _ _ (rf_mul_ex _ a) (rf_congr (fun z => rf_mul z (ne a)) _ _ (rf_ghot_ex t))) _) _).
  exact (rf_congr (I.List_map_inst3 LN LN (fun x => rf_mul hL x)) _ _ (rf_iota_ex l r)).
Qed.

Lemma search_space_arrival_curve_prefix_FP_h_correspondence tR tL lR lL rR rL :
  TaskRel tR tL -> Lean.eq (ne lR) lL -> Lean.eq (ne rR) rL ->
  Lean.eq (lex ne (Rfsc.search_space_arrival_curve_prefix_FP_h tR lR rR)) (ISSh tL lL rL).
Proof. intros Ht Hl Hr. destruct Ht. destruct Hl. destruct Hr. exact (rf_ssh_ex tR lR rR). Qed.

Lemma rf_bound_ex t L :
  Lean.eq (ne (L %/ Rac.get_horizon_of_task t).+1)
    (rf_add (rf_div (ne L) (IAC_get_horizon_of_task (task_ex t))) (ne (S O))).
Proof.
  rewrite -addn1.
  refine (rf_trans _ _ _ (rf_add_ex _ _) (rf_congr (fun z => rf_add z (ne (S O))) _ _ _)).
  exact (rf_trans _ _ _ (rf_div_ex _ _) (rf_congr (rf_div (ne L)) _ _ (rf_ghot_ex t))).
Qed.

Lemma rf_ss_ex t L : Lean.eq (lex ne (Rfsc.search_space_arrival_curve_prefix_FP t L)) (ISS (task_ex t) (ne L)).
Proof.
  unfold Rfsc.search_space_arrival_curve_prefix_FP. cbv zeta.
  exact (rf_trans _ _ _ (rf_ssh_ex t O _) (rf_congr (ISSh (task_ex t) (ne O)) _ _ (rf_bound_ex t L))).
Qed.

Lemma search_space_arrival_curve_prefix_FP_correspondence tR tL LR LL :
  TaskRel tR tL -> Lean.eq (ne LR) LL ->
  Lean.eq (lex ne (Rfsc.search_space_arrival_curve_prefix_FP tR LR)) (ISS tL LL).
Proof. intros Ht HL. destruct Ht. destruct HL. exact (rf_ss_ex tR LR). Qed.

(** ** More statement combinators *)
Lemma rf_and_rel (A B : Prop) (A' B' : SProp) :
  PropSPropRel A A' -> PropSPropRel B B' -> PropSPropRel (A /\ B) (Lean.And A' B').
Proof.
  intros RA RB. apply prop_sprop_rel_intro.
  - intros [a b]. exact (Lean.And_intro _ _ (prop_to_sprop _ _ RA a) (prop_to_sprop _ _ RB b)).
  - intros [a b]. apply strictly_inhabits. exact (conj (sprop_to_prop _ _ RA a) (sprop_to_prop _ _ RB b)).
Qed.

Lemma rf_or_rel (A B : Prop) (A' B' : SProp) :
  PropSPropRel A A' -> PropSPropRel B B' -> PropSPropRel (A \/ B) (Lean.Or A' B').
Proof.
  intros RA RB. apply prop_sprop_rel_intro.
  - intros [a|b]; [exact (Lean.Or_inl _ _ (prop_to_sprop _ _ RA a)) | exact (Lean.Or_inr _ _ (prop_to_sprop _ _ RB b))].
  - intros [a|b]; apply strictly_inhabits; [left; exact (sprop_to_prop _ _ RA a) | right; exact (sprop_to_prop _ _ RB b)].
Qed.

Lemma rf_exists_nat_rel (P : nat -> Prop) (Q : LN -> SProp) :
  (forall a, PropSPropRel (P a) (Q (ne a))) -> PropSPropRel (exists a, P a) (I.Exists LN Q).
Proof.
  intro R. apply prop_sprop_rel_intro.
  - intros [a h]. exact (I.Exists_intro _ _ (ne a) (prop_to_sprop _ _ (R a) h)).
  - intros [c h]. apply strictly_inhabits. exists (ni c).
    exact (sprop_to_prop _ _ (R (ni c)) (rf_tr1S Q (rf_sym _ _ (rf_ne_ni c)) h)).
Qed.

(** Numbers: equality and the canonical images of sums and products. *)
Lemma rf_eqn_canon a b aL bL : Lean.eq (ne a) aL -> Lean.eq (ne b) bL -> PropSPropRel (Logic.eq a b) (Lean.eq aL bL).
Proof. intros Ha Hb. exact (rf_eq_rel a aL b bL Ha Hb). Qed.

Lemma rf_succ_ex A : Lean.eq (ne (A + 1)) (rf_add (ne A) (ne (S O))).
Proof. exact (rf_add_ex A (S O)). Qed.

(** [a != b] against [decide (a ≠ b) = true]. *)
Lemma rf_neq_rel a b aL bL : Lean.eq (ne a) aL -> Lean.eq (ne b) bL ->
  PropSPropRel (is_true (a != b))
    (Lean.eq (I.Decidable_decide (I.Not (Lean.eq aL bL)) (I.instDecidableNot (Lean.eq aL bL) (I.instDecidableEqNat aL bL)))
       I.Bool_true).
Proof.
  intros Ha Hb.
  have R := rf_eq_rel a aL b bL Ha Hb.
  apply rf_true_rel. apply rf_decide_ex.
  apply prop_sprop_rel_intro.
  - intros hne e. have h := sprop_to_prop _ _ R e. rewrite h eqxx in hne. exact (match Bool.diff_false_true hne with end).
  - intro hn. destruct (a == b) eqn:E.
    + exact (rf_false_elim _ (hn (prop_to_sprop _ _ R (elimT eqP E)))).
    + apply strictly_inhabits. exact Logic.eq_refl.
Qed.

(** Membership in a list given by a definition correspondence. *)
Lemma rf_mem_via (x : nat) xs xsL : Lean.eq (lex ne xs) xsL -> PropSPropRel (is_true (x \in xs)) (IMem LN (ne x) xsL).
Proof.
  intro E. have R := rf_mem_rel ne ni rf_ni_ne x xs.
  apply prop_sprop_rel_intro.
  - intro h. exact (rf_tr1S (fun l => IMem LN (ne x) l) E (prop_to_sprop _ _ R h)).
  - intro h. apply strictly_inhabits.
    exact (sprop_to_prop _ _ R (rf_tr1S (fun l => IMem LN (ne x) l) (rf_sym _ _ E) h)).
Qed.

(** [last0] against the accepted [last0] ([getLastD _ 0]). *)
Lemma rf_last_ex x xs :
  Lean.eq (ne (last x xs)) (I.Prosa_Util_List_last0 (Icons LN (ne x) (lex ne xs))).
Proof.
  revert x; induction xs as [|y ys IH]; intro x.
  - exact (rf_refl _).
  - exact (IH y).
Qed.

Lemma rf_last0_ex xs : Lean.eq (ne (last0 xs)) (I.Prosa_Util_List_last0 (lex ne xs)).
Proof. destruct xs as [|x xs]; [exact (rf_refl _) | exact (rf_last_ex x xs)]. Qed.

(** ** Statement correspondences *)
Ltac rfs_head ts tsk :=
  apply rf_forall_tasks; intro ts;
  apply rf_imp_rel; first exact (task_set_with_valid_arrivals_correspondence _ _ (rf_refl _));
  apply rf_forall_task; intro tsk;
  apply rf_imp_rel; first exact (rf_lt_canon _ _);
  apply rf_imp_rel; first exact (rf_mem_rel task_ex task_im rf_task_rt _ _).

Lemma rf_steps_lt_rel tsk :
  PropSPropRel (forall s : nat, is_true (s \in Rac.get_time_steps_of_task tsk) -> is_true (ltn s (Rac.get_horizon_of_task tsk)))
    (forall sL : LN, IMem LN sL (IAC_get_time_steps_of_task (task_ex tsk)) ->
       rf_lt sL (IAC_get_horizon_of_task (task_ex tsk))).
Proof.
  apply rf_forall_nat. intro s.
  apply rf_imp_rel; first exact (rf_mem_via s _ _ (rf_gtst_ex tsk)).
  exact (rf_lt_rel _ _ _ _ (sub_nat_rel_canonical s) (rf_ghot_ex tsk)).
Qed.

Lemma rf_rbf_neq_rel tsk A :
  PropSPropRel (is_true (Rac.task_rbf tsk A != Rac.task_rbf tsk (A + 1)))
    (Lean.eq (I.Decidable_decide
       (I.Not (Lean.eq (IAC_task_rbf (task_ex tsk) (ne A)) (IAC_task_rbf (task_ex tsk) (rf_add (ne A) (ne (S O))))))
       (I.instDecidableNot _ (I.instDecidableEqNat (IAC_task_rbf (task_ex tsk) (ne A))
          (IAC_task_rbf (task_ex tsk) (rf_add (ne A) (ne (S O)))))))
     I.Bool_true).
Proof.
  apply rf_neq_rel.
  - exact (task_rbf_correspondence tsk _ A _ (rf_refl _) (rf_refl _)).
  - exact (task_rbf_correspondence tsk _ (A + 1) _ (rf_refl _) (rf_succ_ex A)).
Qed.

Lemma rf_bound_rel tsk L i :
  PropSPropRel (is_true (ltn i (L %/ Rac.get_horizon_of_task tsk).+1))
    (rf_lt (ne i) (rf_add (rf_div (ne L) (IAC_get_horizon_of_task (task_ex tsk))) (ne (S O)))).
Proof. exact (rf_lt_rel _ _ _ _ (sub_nat_rel_canonical i) (rf_bound_ex tsk L)). Qed.

Lemma rf_sum_rel tsk A i t :
  PropSPropRel (Logic.eq (A + 1) (i * Rac.get_horizon_of_task tsk + t))
    (Lean.eq (rf_add (ne A) (ne (S O))) (rf_add (rf_mul (ne i) (IAC_get_horizon_of_task (task_ex tsk))) (ne t))).
Proof.
  apply rf_eqn_canon; first exact (rf_succ_ex A).
  refine (rf_trans _ _ _ (rf_add_ex _ _) (rf_congr (fun z => rf_add z (ne t)) _ _ _)).
  exact (rf_trans _ _ _ (rf_mul_ex _ _) (rf_congr (rf_mul (ne i)) _ _ (rf_ghot_ex tsk))).
Qed.

Lemma rf_mul_rel tsk A i :
  PropSPropRel (Logic.eq (A + 1) (i * Rac.get_horizon_of_task tsk))
    (Lean.eq (rf_add (ne A) (ne (S O))) (rf_mul (ne i) (IAC_get_horizon_of_task (task_ex tsk)))).
Proof.
  apply rf_eqn_canon; first exact (rf_succ_ex A).
  exact (rf_trans _ _ _ (rf_mul_ex _ _) (rf_congr (rf_mul (ne i)) _ _ (rf_ghot_ex tsk))).
Qed.