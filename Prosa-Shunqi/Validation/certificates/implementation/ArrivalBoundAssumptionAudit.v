From ImplementationCertificates Require Import ArrivalBoundCorrespondence.
From FoundationImported Require ImportedArrivalBound.
Require OfficialArrivalBound.
Set Printing All.

Check OfficialArrivalBound.OfficialArrivalBound.statement_eqn_task_arrivals_bound : Type.
Check ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_eqn_task_arrivals_bound :
  forall x y : ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound,
    ImportedArrivalBound.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect
      (Lean.eq x y)
      (ImportedArrivalBound.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_eqdef x y).

Goal True. idtac "AUDIT_BEGIN task_arrivals_bound_source_roundtrip". exact I. Qed.
Print Assumptions ab_source_roundtrip.
Goal True. idtac "AUDIT_END task_arrivals_bound_source_roundtrip". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN task_arrivals_bound_target_roundtrip". exact I. Qed.
Print Assumptions ab_target_roundtrip.
Goal True. idtac "AUDIT_END task_arrivals_bound_target_roundtrip". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN task_arrivals_bound_periodic". exact I. Qed.
Print Assumptions ab_source_constructor_periodic.
Goal True. idtac "AUDIT_END task_arrivals_bound_periodic". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN task_arrivals_bound_sporadic". exact I. Qed.
Print Assumptions ab_source_constructor_sporadic.
Goal True. idtac "AUDIT_END task_arrivals_bound_sporadic". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN task_arrivals_bound_prefix". exact I. Qed.
Print Assumptions ab_source_constructor_prefix.
Goal True. idtac "AUDIT_END task_arrivals_bound_prefix". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN task_arrivals_bound_eqdef". exact I. Qed.
Print Assumptions ab_eqdef_bool_correspondence.
Goal True. idtac "AUDIT_END task_arrivals_bound_eqdef". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN eqn_task_arrivals_bound". exact I. Qed.
Print Assumptions ab_eqn_task_arrivals_bound_statement_correspondence.
Goal True. idtac "AUDIT_END eqn_task_arrivals_bound". exact I. Qed.
