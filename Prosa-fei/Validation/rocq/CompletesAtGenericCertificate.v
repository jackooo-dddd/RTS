From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From prosa Require Import behavior.service.
From LeanImport Require Import Lean.
Require Import ImportedCompletesAt93 PropSPropFoundation.

(** This certificate isolates exactly the still-open semantic dependency:
    pointwise correspondence of [completed_by].  It does not assume the
    desired [completes_at] correspondence. *)

Fixpoint completes_nat_to_imported (n : Datatypes.nat) : Nat :=
  match n with
  | Datatypes.O => Nat_zero
  | Datatypes.S n' => Nat_succ (completes_nat_to_imported n')
  end.

Definition SourceCompletedByRel
    (completedR : Datatypes.nat -> bool)
    (completedL : Nat -> SProp) : Prop :=
  forall t,
    PropSPropRel (is_true (completedR t))
      (completedL (completes_nat_to_imported t)).

Definition source_completes_at_formula
    (completed : Datatypes.nat -> bool) (t : Datatypes.nat) : bool :=
  (~~ completed t.-1 || (t == Datatypes.O)) && completed t.

Definition coq_false_to_imported_false (H : Logic.False) : False :=
  match H return False with end.

Definition imported_false_to_strict_false (H : False) :
    StrictlyInhabited Logic.False :=
  match H return StrictlyInhabited Logic.False with end.

Lemma source_completes_at_zero_now
    (completed : Datatypes.nat -> bool) :
  is_true (source_completes_at_formula completed Datatypes.O) ->
  is_true (completed Datatypes.O).
Proof.
  rewrite /source_completes_at_formula.
  by move=> /andP [_ Hnow].
Qed.

Lemma source_completes_at_successor_parts
    (completed : Datatypes.nat -> bool) (n : Datatypes.nat) :
  is_true (source_completes_at_formula completed (Datatypes.S n)) ->
  is_true (~~ completed n) /\ is_true (completed (Datatypes.S n)).
Proof.
  rewrite /source_completes_at_formula /=.
  destruct (completed n) eqn:Hprev;
    destruct (completed (Datatypes.S n)) eqn:Hnow;
    cbn; intros H; try discriminate H; split; reflexivity.
Qed.

Lemma successor_not_imported_zero (n : Datatypes.nat) :
  Not (eq (completes_nat_to_imported (Datatypes.S n)) Nat_zero).
Proof.
  intro H.
  pose proof (imported_eq_to_coq_eq _ _ H) as Hcoq.
  discriminate Hcoq.
Qed.

Theorem completes_at_formula_conditional_certificate
    (completedR : Datatypes.nat -> bool)
    (completedL : Nat -> SProp)
    (Hcompleted : SourceCompletedByRel completedR completedL)
    (t : Datatypes.nat) :
  PropSPropRel
    (is_true (source_completes_at_formula completedR t))
    (Prosa_Validation_CompletesAt_completes_at_formula
      completedL (completes_nat_to_imported t)).
Proof.
  apply prop_sprop_rel_intro.
  - destruct t as [|n].
    + cbn. intro Hsource.
      exact (And_intro _ _ (Or_inr _ _ (eq_refl Nat_zero))
        (prop_to_sprop _ _ (Hcompleted Datatypes.O)
          (source_completes_at_zero_now completedR Hsource))).
    + cbn. intro Hsource.
      pose proof (source_completes_at_successor_parts completedR n Hsource)
        as Hparts.
      apply And_intro.
      * apply Or_inl. intro HprevL.
        apply coq_false_to_imported_false.
        have HprevR := sprop_to_prop _ _ (Hcompleted n) HprevL.
        by move: (proj1 Hparts); rewrite HprevR.
      * exact (prop_to_sprop _ _ (Hcompleted n.+1) (proj2 Hparts)).
  - destruct t as [|n].
    + cbn. intro Htarget. destruct Htarget as [Hzero Hnow].
      apply strictly_inhabits. rewrite /source_completes_at_formula.
      apply/andP; split.
      * by rewrite eqxx orbT.
      * exact (sprop_to_prop _ _ (Hcompleted Datatypes.O) Hnow).
    + cbn. intro Htarget. destruct Htarget as [Hbefore Hnow].
      destruct Hbefore as [Hnot | Hzero].
      * apply strictly_inhabits. rewrite /source_completes_at_formula /=.
        apply/andP; split.
        -- destruct (completedR n) eqn:Hvalue.
           ++ exfalso.
              apply (interpret_strict Logic.False).
              apply imported_false_to_strict_false.
              apply Hnot.
              apply (prop_to_sprop _ _ (Hcompleted n)).
              by rewrite Hvalue.
           ++ done.
        -- exact (sprop_to_prop _ _ (Hcompleted n.+1) Hnow).
      * exact (match successor_not_imported_zero n Hzero with end).
Qed.

(** The same compositional result stated directly over the pinned official
    Prosa 0.6 declaration.  Unfolding [completes_at] is definitional; the only
    semantic premise is pointwise [completed_by] correspondence. *)
Theorem official_completes_at_conditional_certificate
    (Job : eqType)
    (PState : prosa.behavior.schedule.ProcessorState Job)
    (sched : prosa.behavior.schedule.schedule PState)
    (job_cost : prosa.behavior.job.JobCost Job)
    (j : Job)
    (completedL : Nat -> SProp)
    (Hcompleted : SourceCompletedByRel
      (fun u => @prosa.behavior.service.completed_by
        Job PState sched job_cost j u)
      completedL)
    (t : Datatypes.nat) :
  PropSPropRel
    (@prosa.behavior.service.completes_at
      Job PState sched job_cost j t)
    (Prosa_Validation_CompletesAt_completes_at_formula
      completedL (completes_nat_to_imported t)).
Proof.
  change (PropSPropRel
    (is_true (source_completes_at_formula
      (fun u => @prosa.behavior.service.completed_by
        Job PState sched job_cost j u) t))
    (Prosa_Validation_CompletesAt_completes_at_formula
      completedL (completes_nat_to_imported t))).
  exact (completes_at_formula_conditional_certificate _ _ Hcompleted t).
Qed.

Print Assumptions completes_at_formula_conditional_certificate.
Print Assumptions official_completes_at_conditional_certificate.
