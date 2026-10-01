(** Correspondences for [implementation/refinements/arrival_curve_prefix.v].

    The source is the official file, compiled on its official proof closure with CoqEAL 2.1.2 (the module with the
    recorded rewrite-order flag).  The base maps and definition correspondences are those of the accepted
    refinements.v, arrival_bound.v, task.v and arrival_curve.v certificates, re-bound in [RacpBase],
    [RacpArrivalBound], [RacpTask] and [RacpArrivalCurve].  Here the four statements are related by [PropSPropRel],
    built from generic combinators: universal quantification over tasks, task lists, numbers and number lists (covered
    in both directions by the canonical maps and their roundtrips), and implication.
    No certificate uses its own source or target theorem: statements are taken with [type of], never applied. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div bigop path.
From CoqEAL Require Import hrel param refinements binnat.
From prosa Require Import implementation.refinements.arrival_curve_prefix.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefArrivalCurvePrefix ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence RacpBase
  RacpArrivalBound RacpTask RacpArrivalCurve.
Import Refinements.Op.

Set Warnings "-notation-for-abbreviation,-deprecated".

Module I := ImportedRefArrivalCurvePrefix.
Module Racp := prosa.implementation.refinements.arrival_curve_prefix.
Module Rac := prosa.implementation.refinements.arrival_curve.
Module Rt := prosa.implementation.refinements.task.
Module Dt := prosa.implementation.definitions.task.
Module EAC := prosa.implementation.definitions.extrapolated_arrival_curve.

(** ** Generic combinators *)
Definition rf_tr1S {A : Type} (P : A -> SProp) {x y : A} (H : Lean.eq x y) (p : P x) : P y :=
  match H in Lean.eq _ z return P z with Lean.eq_refl => p end.

Lemma rf_imp_rel (A B : Prop) (A' B' : SProp) :
  PropSPropRel A A' -> PropSPropRel B B' -> PropSPropRel (A -> B) (A' -> B').
Proof.
  intros RA RB. apply prop_sprop_rel_intro.
  - intros h a'. exact (prop_to_sprop _ _ RB (h (sprop_to_prop _ _ RA a'))).
  - intro h. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ RB (h (prop_to_sprop _ _ RA a))).
Qed.

Lemma rf_forall_rel {A C : Type} (e : A -> C) (i : C -> A) (H : forall c, Lean.eq (e (i c)) c)
    (P : A -> Prop) (Q : C -> SProp) :
  (forall a, PropSPropRel (P a) (Q (e a))) -> PropSPropRel (forall a, P a) (forall c, Q c).
Proof.
  intro R. apply prop_sprop_rel_intro.
  - intros h c. exact (rf_tr1S Q (H c) (prop_to_sprop _ _ (R (i c)) (h (i c)))).
  - intro h. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (R a) (h (e a))).
Qed.

Abbreviation ITask := I.Prosa_Implementation_Refinements_Task_Task.

Definition rf_forall_task := @rf_forall_rel Rt.Task ITask task_ex task_im rf_task_rtL.
Definition rf_forall_tasks := @rf_forall_rel (seq Rt.Task) (IList ITask) (lex task_ex) (lim task_im)
  (rf_lex_lim task_ex task_im rf_task_rtL).
Definition rf_forall_nat := @rf_forall_rel nat LN ne ni rf_ne_ni.
Definition rf_forall_nats := @rf_forall_rel (seq nat) (IList LN) (lex ne) (lim ni) (rf_lex_lim ne ni rf_ne_ni).

(** ** Components *)
Lemma rf_lt_canon a b : PropSPropRel (is_true (ltn a b)) (rf_lt (ne a) (ne b)).
Proof. exact (rf_lt_rel a _ b _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b)). Qed.

Lemma rf_head_ex t :
  Lean.eq (ne (head (O, O) (EAC.steps_of (Dt.get_arrival_curve_prefix t))).1)
    (I.Prod_fst_inst3 LN LN (I.List_headD_inst1 (IProd LN LN) (IEsteps (IGACP (task_ex t))) (pre ne ne (O, O)))).
Proof.
  have h := rf_gacp_ex t. destruct (Dt.get_arrival_curve_prefix t) as [hh st].
  refine (rf_trans _ _ _ _ (rf_congr (fun p => I.Prod_fst_inst3 LN LN
    (I.List_headD_inst1 (IProd LN LN) (IEsteps p) (pre ne ne (O, O)))) _ _ h)).
  destruct st as [|[a b] st]; exact (rf_refl _).
Qed.

Lemma rf_sorted_ltn_ex xs :
  Lean.eq (be (sorted ltn xs))
    (IEsortedBool LN (fun a b => I.Decidable_decide (rf_lt a b) (I.Nat_decLt a b)) (lex ne xs)).
Proof. exact (rf_sorted_ex ne ltn _ (fun a b => rf_lt_decide_ex a b) xs). Qed.

(** ** Statement correspondences *)
Definition rf_src_has_valid_arrival_curve_prefix_tsk := ltac:(src_ty Racp.has_valid_arrival_curve_prefix_tsk).
Definition rf_tgt_has_valid_arrival_curve_prefix_tsk :=
  ltac:(src_ty I.Prosa_Implementation_Refinements_ArrivalCurvePrefix_has_valid_arrival_curve_prefix_tsk).
Lemma has_valid_arrival_curve_prefix_tsk_correspondence :
  PropSPropRel rf_src_has_valid_arrival_curve_prefix_tsk rf_tgt_has_valid_arrival_curve_prefix_tsk.
Proof.
  apply rf_forall_tasks. intro ts.
  apply rf_imp_rel; first exact (task_set_with_valid_arrivals_correspondence ts _ (rf_refl _)).
  apply rf_forall_task. intro tsk.
  apply rf_imp_rel; first exact (rf_mem_rel task_ex task_im rf_task_rt tsk ts).
  exact (has_valid_arrival_curve_prefix_correspondence tsk _ (rf_refl _)).
Qed.

Definition rf_src_steps_are_positive_if_first_step_is_positive :=
  ltac:(src_ty Racp.steps_are_positive_if_first_step_is_positive).
Definition rf_tgt_steps_are_positive_if_first_step_is_positive :=
  ltac:(src_ty I.Prosa_Implementation_Refinements_ArrivalCurvePrefix_steps_are_positive_if_first_step_is_positive).
Lemma steps_are_positive_if_first_step_is_positive_correspondence :
  PropSPropRel rf_src_steps_are_positive_if_first_step_is_positive
    rf_tgt_steps_are_positive_if_first_step_is_positive.
Proof.
  apply rf_forall_tasks. intro ts.
  apply rf_imp_rel; first exact (task_set_with_valid_arrivals_correspondence ts _ (rf_refl _)).
  apply rf_forall_task. intro tsk.
  apply rf_imp_rel; first exact (rf_lt_canon O (Dt.task_cost tsk)).
  apply rf_imp_rel; first exact (rf_mem_rel task_ex task_im rf_task_rt tsk ts).
  apply rf_imp_rel; first exact (rf_lt_rel _ _ _ _ (sub_nat_rel_canonical O) (rf_head_ex tsk)).
  apply rf_forall_nat. intro st.
  apply rf_imp_rel.
  - have R := rf_mem_rel ne ni rf_ni_ne st (Rac.get_time_steps_of_task tsk).
    apply prop_sprop_rel_intro.
    + intro h. exact (rf_tr1S (fun l => IMem LN (ne st) l) (rf_gtst_ex tsk) (prop_to_sprop _ _ R h)).
    + intro h. apply strictly_inhabits.
      exact (sprop_to_prop _ _ R (rf_tr1S (fun l => IMem LN (ne st) l) (rf_sym _ _ (rf_gtst_ex tsk)) h)).
  - exact (rf_lt_canon O st).
Qed.

Definition rf_src_nonshifted_offsets_are_positive := ltac:(src_ty Racp.nonshifted_offsets_are_positive).
Definition rf_tgt_nonshifted_offsets_are_positive :=
  ltac:(src_ty I.Prosa_Implementation_Refinements_ArrivalCurvePrefix_nonshifted_offsets_are_positive).
Lemma nonshifted_offsets_are_positive_correspondence :
  PropSPropRel rf_src_nonshifted_offsets_are_positive rf_tgt_nonshifted_offsets_are_positive.
Proof.
  apply rf_forall_tasks. intro ts.
  apply rf_imp_rel; first exact (task_set_with_valid_arrivals_correspondence ts _ (rf_refl _)).
  apply rf_forall_task. intro tsk.
  apply rf_imp_rel; first exact (rf_lt_canon O (Dt.task_cost tsk)).
  apply rf_imp_rel; first exact (rf_mem_rel task_ex task_im rf_task_rt tsk ts).
  apply rf_imp_rel; first exact (rf_lt_rel _ _ _ _ (sub_nat_rel_canonical O) (rf_head_ex tsk)).
  apply rf_forall_nat. intro A.
  apply rf_forall_nats. intro offs.
  apply rf_imp_rel.
  - have R := rf_mem_rel ne ni rf_ni_ne A (Rac.repeat_steps_with_offset tsk offs).
    have E := repeat_steps_with_offset_correspondence tsk _ offs _ (rf_refl _) (rf_refl _).
    apply prop_sprop_rel_intro.
    + intro h. exact (rf_tr1S (fun l => IMem LN (ne A) l) E (prop_to_sprop _ _ R h)).
    + intro h. apply strictly_inhabits.
      exact (sprop_to_prop _ _ R (rf_tr1S (fun l => IMem LN (ne A) l) (rf_sym _ _ E) h)).
  - exact (rf_lt_canon O A).
Qed.

Definition rf_src_time_steps_sorted := ltac:(src_ty Racp.time_steps_sorted).
Definition rf_tgt_time_steps_sorted := ltac:(src_ty I.Prosa_Implementation_Refinements_ArrivalCurvePrefix_time_steps_sorted).
Lemma time_steps_sorted_correspondence : PropSPropRel rf_src_time_steps_sorted rf_tgt_time_steps_sorted.
Proof.
  apply rf_forall_tasks. intro ts.
  apply rf_imp_rel; first exact (task_set_with_valid_arrivals_correspondence ts _ (rf_refl _)).
  apply rf_forall_task. intro tsk.
  apply rf_imp_rel; first exact (rf_mem_rel task_ex task_im rf_task_rt tsk ts).
  exact (rf_true_rel _ _ (rf_trans _ _ _ (rf_sorted_ltn_ex _)
    (rf_congr (IEsortedBool LN (fun a b => I.Decidable_decide (rf_lt a b) (I.Nat_decLt a b))) _ _ (rf_gtst_ex tsk)))).
Qed.
