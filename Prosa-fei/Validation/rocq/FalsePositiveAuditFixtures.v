Require Import PropSPropFoundation ImportedFiniteNatSumNormalized93.

(** Negative A: the desired semantic relation is merely an input premise.
    This is legal Rocq, but an audit must classify it CONDITIONAL. *)
Section PremiseFixture.
  Variable P : Prop.
  Variable Q : SProp.
  Hypothesis semantic_correspondence : PropSPropRel P Q.

  Theorem premise_certificate : PropSPropRel P Q.
  Proof. exact semantic_correspondence. Qed.
End PremiseFixture.

(** Negative B: a validation-local fake axiom must never be allowlisted. *)
Axiom fake_semantic_axiom : Logic.True.

Theorem fake_axiom_certificate : Logic.True.
Proof. exact fake_semantic_axiom. Qed.

(** Negative C: directly using the imported target theorem is circular. *)
Definition circular_target_certificate :=
  Prosa_Util_Sum_big_nat_eq0.

Goal Logic.True. idtac "AUDIT_BEGIN semantic_premise". exact Logic.I. Qed.
Print premise_certificate.
Print Assumptions premise_certificate.
Goal Logic.True. idtac "AUDIT_END semantic_premise". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN fake_axiom". exact Logic.I. Qed.
Print fake_axiom_certificate.
Print Assumptions fake_axiom_certificate.
Goal Logic.True. idtac "AUDIT_END fake_axiom". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN circular_target". exact Logic.I. Qed.
Print circular_target_certificate.
Print Assumptions circular_target_certificate.
Goal Logic.True. idtac "AUDIT_END circular_target". exact Logic.I. Qed.
