From FoundationCertificates Require Import FixpointBaseCorrespondence
  FixpointTheoremCorrespondence FixpointMaxOperations
  FixpointMaxTheoremCorrespondence.

Goal True. idtac "AUDIT_BEGIN find_fixpoint_from". exact I. Qed.
Print Assumptions fixpoint_from_correspondence.
Goal True. idtac "AUDIT_END find_fixpoint_from". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN find_fixpoint". exact I. Qed.
Print Assumptions fixpoint_correspondence.
Goal True. idtac "AUDIT_END find_fixpoint". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN ffpf_finds_fixpoint". exact I. Qed.
Print Assumptions fixpoint_ffpf_statement_certificate.
Goal True. idtac "AUDIT_END ffpf_finds_fixpoint". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN ffp_finds_fixpoint". exact I. Qed.
Print Assumptions fixpoint_ffp_statement_certificate.
Goal True. idtac "AUDIT_END ffp_finds_fixpoint". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN no_fixpoint_skipped". exact I. Qed.
Print Assumptions fixpoint_no_skipped_statement_certificate.
Goal True. idtac "AUDIT_END no_fixpoint_skipped". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN ffpf_finds_least_fixpoint". exact I. Qed.
Print Assumptions fixpoint_ffpf_least_statement_certificate.
Goal True. idtac "AUDIT_END ffpf_finds_least_fixpoint". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN ffp_finds_least_fixpoint". exact I. Qed.
Print Assumptions fixpoint_ffp_least_statement_certificate.
Goal True. idtac "AUDIT_END ffp_finds_least_fixpoint". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN ffpf_finds_positive_fixpoint". exact I. Qed.
Print Assumptions fixpoint_ffpf_positive_statement_certificate.
Goal True. idtac "AUDIT_END ffpf_finds_positive_fixpoint". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN ffp_finds_positive_fixpoint". exact I. Qed.
Print Assumptions fixpoint_ffp_positive_statement_certificate.
Goal True. idtac "AUDIT_END ffp_finds_positive_fixpoint". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN ffpf_finds_none". exact I. Qed.
Print Assumptions fixpoint_ffpf_none_statement_certificate.
Goal True. idtac "AUDIT_END ffpf_finds_none". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN ffp_finds_none". exact I. Qed.
Print Assumptions fixpoint_ffp_none_statement_certificate.
Goal True. idtac "AUDIT_END ffp_finds_none". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN find_max_fixpoint_of_seq". exact I. Qed.
Print Assumptions fixpoint_max_of_seq_correspondence.
Goal True. idtac "AUDIT_END find_max_fixpoint_of_seq". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN fmfs_finds_fixpoint". exact I. Qed.
Print Assumptions fixpoint_fmfs_finds_statement_certificate.
Goal True. idtac "AUDIT_END fmfs_finds_fixpoint". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN fmfs_is_maximum". exact I. Qed.
Print Assumptions fixpoint_fmfs_maximum_statement_certificate.
Goal True. idtac "AUDIT_END fmfs_is_maximum". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN find_max_fixpoint". exact I. Qed.
Print Assumptions fixpoint_max_wrapper_correspondence.
Goal True. idtac "AUDIT_END find_max_fixpoint". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN fmf_finds_fixpoint". exact I. Qed.
Print Assumptions fixpoint_fmf_finds_statement_certificate.
Goal True. idtac "AUDIT_END fmf_finds_fixpoint". exact I. Qed.
Goal True. idtac "AUDIT_BEGIN fmf_is_maximum". exact I. Qed.
Print Assumptions fixpoint_fmf_maximum_statement_certificate.
Goal True. idtac "AUDIT_END fmf_is_maximum". exact I. Qed.
