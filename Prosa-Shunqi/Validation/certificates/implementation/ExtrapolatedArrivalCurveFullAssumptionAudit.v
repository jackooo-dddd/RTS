From ImplementationCertificates Require Import ExtrapolatedArrivalCurveFullCorrespondence.
From FoundationImported Require ImportedExtrapolatedArrivalCurve.
Require OfficialExtrapolatedArrivalCurve.
Set Printing All.

Check OfficialExtrapolatedArrivalCurve.OfficialExtrapolatedArrivalCurve.statement_large_horizon_P : Type.
Check OfficialExtrapolatedArrivalCurve.OfficialExtrapolatedArrivalCurve.statement_valid_arrival_curve_prefix_P : Type.
Check ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon_P :
  forall pL,
    ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon pL)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon_dec pL).
Check ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix_P :
  forall pL,
    ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix pL)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix_dec pL).

Goal True. idtac "AUDIT_BEGIN ArrivalCurvePrefix_source_roundtrip". exact I. Qed.
Print Assumptions eac_prefix_rocq_roundtrip.
Goal True. idtac "AUDIT_END ArrivalCurvePrefix_source_roundtrip". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN ArrivalCurvePrefix_target_roundtrip". exact I. Qed.
Print Assumptions eac_prefix_imported_roundtrip.
Goal True. idtac "AUDIT_END ArrivalCurvePrefix_target_roundtrip". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN inter_arrival_to_prefix". exact I. Qed.
Print Assumptions eac_inter_arrival_to_prefix_correspondence.
Goal True. idtac "AUDIT_END inter_arrival_to_prefix". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN horizon_of". exact I. Qed.
Print Assumptions eac_horizon_of_correspondence.
Goal True. idtac "AUDIT_END horizon_of". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN steps_of". exact I. Qed.
Print Assumptions eac_steps_of_correspondence.
Goal True. idtac "AUDIT_END steps_of". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN time_steps_of". exact I. Qed.
Print Assumptions eac_time_steps_of_correspondence.
Goal True. idtac "AUDIT_END time_steps_of". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN step_at". exact I. Qed.
Print Assumptions eac_step_at_correspondence.
Goal True. idtac "AUDIT_END step_at". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN value_at". exact I. Qed.
Print Assumptions eac_value_at_correspondence.
Goal True. idtac "AUDIT_END value_at". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN extrapolated_arrival_curve". exact I. Qed.
Print Assumptions eac_extrapolated_arrival_curve_correspondence.
Goal True. idtac "AUDIT_END extrapolated_arrival_curve". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN positive_horizon". exact I. Qed.
Print Assumptions eac_positive_horizon_correspondence.
Goal True. idtac "AUDIT_END positive_horizon". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN no_inf_arrivals". exact I. Qed.
Print Assumptions eac_no_inf_arrivals_correspondence.
Goal True. idtac "AUDIT_END no_inf_arrivals". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN specified_bursts". exact I. Qed.
Print Assumptions eac_specified_bursts_correspondence.
Goal True. idtac "AUDIT_END specified_bursts". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN ltn_steps". exact I. Qed.
Print Assumptions eac_ltn_steps_correspondence.
Goal True. idtac "AUDIT_END ltn_steps". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN leq_steps". exact I. Qed.
Print Assumptions eac_leq_steps_correspondence.
Goal True. idtac "AUDIT_END leq_steps". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN large_horizon_dec". exact I. Qed.
Print Assumptions eac_large_horizon_dec_correspondence.
Goal True. idtac "AUDIT_END large_horizon_dec". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN large_horizon". exact I. Qed.
Print Assumptions eac_large_horizon_correspondence.
Goal True. idtac "AUDIT_END large_horizon". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN valid_arrival_curve_prefix". exact I. Qed.
Print Assumptions eac_valid_arrival_curve_prefix_correspondence.
Goal True. idtac "AUDIT_END valid_arrival_curve_prefix". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN valid_arrival_curve_prefix_dec". exact I. Qed.
Print Assumptions eac_valid_arrival_curve_prefix_dec_correspondence.
Goal True. idtac "AUDIT_END valid_arrival_curve_prefix_dec". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN large_horizon_P". exact I. Qed.
Print Assumptions eac_large_horizon_P_statement_correspondence.
Goal True. idtac "AUDIT_END large_horizon_P". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN valid_arrival_curve_prefix_P". exact I. Qed.
Print Assumptions eac_valid_arrival_curve_prefix_P_statement_correspondence.
Goal True. idtac "AUDIT_END valid_arrival_curve_prefix_P". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN sorted_ltn_steps". exact I. Qed.
Print Assumptions eac_sorted_ltn_steps_correspondence.
Goal True. idtac "AUDIT_END sorted_ltn_steps". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN sorted_leq_steps". exact I. Qed.
Print Assumptions eac_sorted_leq_steps_correspondence.
Goal True. idtac "AUDIT_END sorted_leq_steps". exact I. Qed.
