From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import analysis.definitions.sbf.plain.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPlain.
From FoundationCertificates Require Import PlainCorrespondence.

Check @plain_supply_bound_function_respected_correspondence.
Check @plain_valid_supply_bound_function_correspondence.
Check @plain_sbf_respected_simplified_statement_correspondence.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN plain_true". exact I. Qed.
Print Assumptions plain_true_predicate_relation.
Goal Logic.True. Proof. idtac "AUDIT_END plain_true". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN supply_bound_function_respected". exact I. Qed.
Print Assumptions plain_supply_bound_function_respected_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END supply_bound_function_respected". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN valid_supply_bound_function". exact I. Qed.
Print Assumptions plain_valid_supply_bound_function_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END valid_supply_bound_function". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN sbf_respected_simplified". exact I. Qed.
Print Assumptions plain_sbf_respected_simplified_statement_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END sbf_respected_simplified". exact I. Qed.
