From FoundationCertificates Require Import ClassicPartitionedSchedulabilityCorrespondence.
Set Printing Width 1000.

Goal Logic.True. idtac "AUDIT_BEGIN PartitionSchedulability_same_per_processor_service_correspondence". exact Logic.I. Qed.
Print Assumptions PartitionSchedulability_same_per_processor_service_correspondence.
Goal Logic.True. idtac "AUDIT_END PartitionSchedulability_same_per_processor_service_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN PartitionSchedulability_schedulable_at_system_level_correspondence". exact Logic.I. Qed.
Print Assumptions PartitionSchedulability_schedulable_at_system_level_correspondence.
Goal Logic.True. idtac "AUDIT_END PartitionSchedulability_schedulable_at_system_level_correspondence". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cpg_forall_ncpus_sched". exact Logic.I. Qed.
Print Assumptions cpg_forall_ncpus_sched.
Goal Logic.True. idtac "AUDIT_END cpg_forall_ncpus_sched". exact Logic.I. Qed.

Goal Logic.True. idtac "AUDIT_BEGIN cpp_forall_assign". exact Logic.I. Qed.
Print Assumptions cpp_forall_assign.
Goal Logic.True. idtac "AUDIT_END cpp_forall_assign". exact Logic.I. Qed.
