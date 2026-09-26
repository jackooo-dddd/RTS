From FoundationCertificates Require Import
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence RequestBoundFunctionCorrespondence DemandBoundFunctionCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN task_demand_bound_function_correspondence". exact Logic.I. Qed.
Print Assumptions task_demand_bound_function_correspondence.
Goal Logic.True. idtac "AUDIT_END task_demand_bound_function_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN total_demand_bound_function_correspondence". exact Logic.I. Qed.
Print Assumptions total_demand_bound_function_correspondence.
Goal Logic.True. idtac "AUDIT_END total_demand_bound_function_correspondence". exact Logic.I. Qed.
