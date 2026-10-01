(* Re-bound copy of the accepted certificates/implementation_refinements_arrival_curve_prefix/RefArrivalCurvePrefixCorrespondence.v: modules renamed (ImportedRefArrivalCurvePrefix=ImportedRefEDFRefinements,RacpBase=RqBase,RacpArrivalBound=RqArrivalBound,RacpTask=RqTask,RacpArrivalCurve=RqArrivalCurve), its statement
   correspondences dropped (their statement-only targets are not part of this export), and the commands that mention
   constants absent from this export dropped (the file's report lists them).  Every kept command is unchanged. *)
(** Correspondences for [implementation/refinements/arrival_curve_prefix.v].

    The source is the official file, compiled on its official proof closure with CoqEAL 2.1.2 (the module with the
    recorded rewrite-order flag).  The base maps and definition correspondences are those of the accepted
    refinements.v, arrival_bound.v, task.v and arrival_curve.v certificates, re-bound in [RqBase],
    [RqArrivalBound], [RqTask] and [RqArrivalCurve].  Here the four statements are related by [PropSPropRel],
    built from generic combinators: universal quantification over tasks, task lists, numbers and number lists (covered
    in both directions by the canonical maps and their roundtrips), and implication.
    No certificate uses its own source or target theorem: statements are taken with [type of], never applied. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div bigop path.
From CoqEAL Require Import hrel param refinements binnat.
From prosa Require Import implementation.refinements.arrival_curve_prefix.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefEDFRefinements ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence RqBase
  RqArrivalBound RqTask RqArrivalCurve.
Import Refinements.Op.

Set Warnings "-notation-for-abbreviation,-deprecated".

Module I := ImportedRefEDFRefinements.
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

Lemma rf_sorted_ltn_ex xs :
  Lean.eq (be (sorted ltn xs))
    (IEsortedBool LN (fun a b => I.Decidable_decide (rf_lt a b) (I.Nat_decLt a b)) (lex ne xs)).
Proof. exact (rf_sorted_ex ne ltn _ (fun a b => rf_lt_decide_ex a b) xs). Qed.