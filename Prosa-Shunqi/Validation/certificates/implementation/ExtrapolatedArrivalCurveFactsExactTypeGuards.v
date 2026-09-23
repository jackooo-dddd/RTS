From LeanImport Require Import Lean.
From FoundationCertificates Require Import PropSPropFoundation.
From FoundationImported Require Import ImportedExtrapolatedArrivalCurveFactsCombined.
From ImplementationCertificates Require Import ExtrapolatedArrivalCurveFactsCorrespondence.
Require Import OfficialExtrapolatedArrivalCurveFacts.

(** These guards are separate from the semantic certificates.  The source
    guard checks convertibility to the pinned official elaborated signature.
    The target guard checks convertibility to the actual imported compiled
    Lean theorem type; it deliberately refers to the statement-only target
    constant, whereas the semantic certificate never does. *)
Module OF := OfficialExtrapolatedArrivalCurveFacts.OfficialExtrapolatedArrivalCurveFacts.
Module IF := ImportedExtrapolatedArrivalCurveFactsCombined.

Definition facts_source_of_relation {P : Prop} {Q : SProp}
    (_ : PropSPropRel P Q) : Prop := P.
Definition facts_target_of_relation {P : Prop} {Q : SProp}
    (_ : PropSPropRel P Q) : SProp := Q.

Definition source_guard_ltn_steps_is_transitive :
    Logic.eq (facts_source_of_relation facts_ltn_steps_is_transitive_certificate)
      OF.statement_ltn_steps_is_transitive := Logic.eq_refl _.
Definition target_guard_ltn_steps_is_transitive :
    facts_target_of_relation facts_ltn_steps_is_transitive_certificate :=
  IF.Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_ltn_steps_is_transitive.

Definition source_guard_leq_steps_is_reflexive :
    Logic.eq (facts_source_of_relation facts_leq_steps_is_reflexive_certificate)
      OF.statement_leq_steps_is_reflexive := Logic.eq_refl _.
Definition target_guard_leq_steps_is_reflexive :
    facts_target_of_relation facts_leq_steps_is_reflexive_certificate :=
  IF.Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_leq_steps_is_reflexive.

Definition source_guard_leq_steps_is_transitive :
    Logic.eq (facts_source_of_relation facts_leq_steps_is_transitive_certificate)
      OF.statement_leq_steps_is_transitive := Logic.eq_refl _.
Definition target_guard_leq_steps_is_transitive :
    facts_target_of_relation facts_leq_steps_is_transitive_certificate :=
  IF.Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_leq_steps_is_transitive.

Definition source_guard_value_at_monotone :
    Logic.eq (facts_source_of_relation facts_value_at_monotone_certificate)
      OF.statement_value_at_monotone := Logic.eq_refl _.
Definition target_guard_value_at_monotone :
    facts_target_of_relation facts_value_at_monotone_certificate :=
  IF.Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_value_at_monotone.

Definition source_guard_value_at_change_is_in_steps_of :
    Logic.eq (facts_source_of_relation facts_value_at_change_is_in_steps_of_certificate)
      OF.statement_value_at_change_is_in_steps_of := Logic.eq_refl _.
Definition target_guard_value_at_change_is_in_steps_of :
    facts_target_of_relation facts_value_at_change_is_in_steps_of_certificate :=
  IF.Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_value_at_change_is_in_steps_of.

Definition source_guard_sorted_ltn_steps_imply_sorted_leq_steps_steps :
    Logic.eq (facts_source_of_relation facts_sorted_ltn_implies_sorted_leq_certificate)
      OF.statement_sorted_ltn_steps_imply_sorted_leq_steps_steps := Logic.eq_refl _.
Definition target_guard_sorted_ltn_steps_imply_sorted_leq_steps_steps :
    facts_target_of_relation facts_sorted_ltn_implies_sorted_leq_certificate :=
  IF.Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_sorted_ltn_steps_imply_sorted_leq_steps_steps.

Definition source_guard_step_at_0_is_00 :
    Logic.eq (facts_source_of_relation facts_step_at_zero_certificate)
      OF.statement_step_at_0_is_00 := Logic.eq_refl _.
Definition target_guard_step_at_0_is_00 :
    facts_target_of_relation facts_step_at_zero_certificate :=
  IF.Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_step_at_0_is_00.

Definition source_guard_step_at_agrees_with_steps_of :
    Logic.eq (facts_source_of_relation facts_step_at_agrees_with_steps_of_certificate)
      OF.statement_step_at_agrees_with_steps_of := Logic.eq_refl _.
Definition target_guard_step_at_agrees_with_steps_of :
    facts_target_of_relation facts_step_at_agrees_with_steps_of_certificate :=
  IF.Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_step_at_agrees_with_steps_of.

Definition source_guard_extrapolated_arrival_curve_is_monotone :
    Logic.eq (facts_source_of_relation facts_extrapolated_arrival_curve_is_monotone_certificate)
      OF.statement_extrapolated_arrival_curve_is_monotone := Logic.eq_refl _.
Definition target_guard_extrapolated_arrival_curve_is_monotone :
    facts_target_of_relation facts_extrapolated_arrival_curve_is_monotone_certificate :=
  IF.Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_extrapolated_arrival_curve_is_monotone.

Definition source_guard_extrapolated_arrival_curve_change :
    Logic.eq (facts_source_of_relation facts_extrapolated_arrival_curve_change_certificate)
      OF.statement_extrapolated_arrival_curve_change := Logic.eq_refl _.
Definition target_guard_extrapolated_arrival_curve_change :
    facts_target_of_relation facts_extrapolated_arrival_curve_change_certificate :=
  IF.Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_extrapolated_arrival_curve_change.
