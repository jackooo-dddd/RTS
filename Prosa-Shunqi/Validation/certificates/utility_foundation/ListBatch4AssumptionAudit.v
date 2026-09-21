From FoundationCertificates Require Import ListBatch4Certificate.

Goal True. idtac "AUDIT_BEGIN filter_last_mem". exact I. Qed.
Print Assumptions filter_last_mem_statement_certificate.
Goal True. idtac "AUDIT_END filter_last_mem". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN range". exact I. Qed.
Print Assumptions range_definition_certificate.
Goal True. idtac "AUDIT_END range". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN iotaD_impl". exact I. Qed.
Print Assumptions iotaD_impl_statement_certificate.
Goal True. idtac "AUDIT_END iotaD_impl". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN index_iota_lt_step". exact I. Qed.
Print Assumptions index_iota_lt_step_statement_certificate.
Goal True. idtac "AUDIT_END index_iota_lt_step". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN index_iota_cat". exact I. Qed.
Print Assumptions index_iota_cat_statement_certificate.
Goal True. idtac "AUDIT_END index_iota_cat". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN range_filter_2cons". exact I. Qed.
Print Assumptions range_filter_2cons_statement_certificate.
Goal True. idtac "AUDIT_END range_filter_2cons". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN index_iota_filter_eqx". exact I. Qed.
Print Assumptions index_iota_filter_eqx_statement_certificate.
Goal True. idtac "AUDIT_END index_iota_filter_eqx". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN index_iota_filter_singl". exact I. Qed.
Print Assumptions index_iota_filter_singl_statement_certificate.
Goal True. idtac "AUDIT_END index_iota_filter_singl". exact I. Qed.

Goal True. idtac "AUDIT_BEGIN index_iota_filter_inxs". exact I. Qed.
Print Assumptions index_iota_filter_inxs_statement_certificate.
Goal True. idtac "AUDIT_END index_iota_filter_inxs". exact I. Qed.
