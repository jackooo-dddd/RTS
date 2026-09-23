From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import analysis.definitions.sbf.pred.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPred.
From FoundationCertificates Require Import PredCorrespondence.

Check @pred_sbf_is_monotone_correspondence.
Check @pred_unit_supply_bound_function_correspondence.
Check @pred_sbf_respected_correspondence.
Check @pred_valid_pred_sbf_correspondence.
Check @pred_sbf_bounded_by_duration_statement_correspondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN sbf_is_monotone". exact I. Qed.
Print Assumptions pred_sbf_is_monotone_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END sbf_is_monotone". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN unit_supply_bound_function". exact I. Qed.
Print Assumptions pred_unit_supply_bound_function_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END unit_supply_bound_function". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN pred_interval". exact I. Qed.
Print Assumptions pred_interval_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END pred_interval". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN pred_sbf_respected". exact I. Qed.
Print Assumptions pred_sbf_respected_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END pred_sbf_respected". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN valid_pred_sbf". exact I. Qed.
Print Assumptions pred_valid_pred_sbf_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END valid_pred_sbf". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN sbf_bounded_by_duration". exact I. Qed.
Print Assumptions pred_sbf_bounded_by_duration_statement_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END sbf_bounded_by_duration". exact I. Qed.
