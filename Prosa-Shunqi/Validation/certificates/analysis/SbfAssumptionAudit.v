From AnalysisCertificates Require Import SbfCorrespondence.
From FoundationImported Require ImportedSbf.
Require OfficialSbf.
Set Printing All.

Check OfficialSbf.OfficialSbf.SupplyBoundFunction : Type.
Check ImportedSbf.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction : Type.
Check ImportedSbf.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_mk :
  (Lean.Nat -> Lean.Nat) ->
  ImportedSbf.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction.
Check ImportedSbf.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function :
  ImportedSbf.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction ->
  Lean.Nat -> Lean.Nat.

Goal True. idtac "AUDIT_BEGIN export_field". exact I. Qed.
Print Assumptions sbf_export_preserves_field.
Goal True. idtac "AUDIT_END export_field". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN import_field". exact I. Qed.
Print Assumptions sbf_import_preserves_field.
Goal True. idtac "AUDIT_END import_field". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN source_roundtrip". exact I. Qed.
Print Assumptions sbf_source_roundtrip.
Goal True. idtac "AUDIT_END source_roundtrip". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN target_roundtrip". exact I. Qed.
Print Assumptions sbf_target_roundtrip.
Goal True. idtac "AUDIT_END target_roundtrip". exact I. Qed.
