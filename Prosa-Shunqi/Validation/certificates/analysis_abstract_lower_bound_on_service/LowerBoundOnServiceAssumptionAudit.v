From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence WorkloadCorrespondence AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations AbstractDefinitionsBusyIntervalHelpers LowerBoundOnServiceCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN interference_is_complement_to_schedule_correspondence". exact Logic.I. Qed.
Print Assumptions interference_is_complement_to_schedule_correspondence.
Goal Logic.True. idtac "AUDIT_END interference_is_complement_to_schedule_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN service_and_interference_bounded_correspondence". exact Logic.I. Qed.
Print Assumptions service_and_interference_bounded_correspondence.
Goal Logic.True. idtac "AUDIT_END service_and_interference_bounded_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN j_receives_enough_service_correspondence". exact Logic.I. Qed.
Print Assumptions j_receives_enough_service_correspondence.
Goal Logic.True. idtac "AUDIT_END j_receives_enough_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN lbs_add_related". exact Logic.I. Qed.
Print Assumptions lbs_add_related.
Goal Logic.True. idtac "AUDIT_END lbs_add_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN lbs_cost_positive_related". exact Logic.I. Qed.
Print Assumptions lbs_cost_positive_related.
Goal Logic.True. idtac "AUDIT_END lbs_cost_positive_related". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN lbs_unit_service_rel". exact Logic.I. Qed.
Print Assumptions lbs_unit_service_rel.
Goal Logic.True. idtac "AUDIT_END lbs_unit_service_rel". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN lbs_arr_ad". exact Logic.I. Qed.
Print Assumptions lbs_arr_ad.
Goal Logic.True. idtac "AUDIT_END lbs_arr_ad". exact Logic.I. Qed.
