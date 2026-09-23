From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import analysis.definitions.finish_time.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFinishTime.
From FoundationCertificates Require Import FinishTimeMinBridge
  FinishTimeCorrespondence.

Check @minimum_value_correspondence.
Check @finish_time_correspondence.
Check @finished_at_finish_time_statement_correspondence.
Check @earliest_finish_time_statement_correspondence.
Check @completes_at_finish_time_statement_correspondence.
Check @response_time_correspondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN minimum_value". exact I. Qed.
Print Assumptions minimum_value_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END minimum_value". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN finish_time". exact I. Qed.
Print Assumptions finish_time_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END finish_time". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN finished_at_finish_time". exact I. Qed.
Print Assumptions finished_at_finish_time_statement_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END finished_at_finish_time". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN earliest_finish_time". exact I. Qed.
Print Assumptions earliest_finish_time_statement_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END earliest_finish_time". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN completes_at_finish_time". exact I. Qed.
Print Assumptions completes_at_finish_time_statement_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END completes_at_finish_time". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN response_time". exact I. Qed.
Print Assumptions response_time_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END response_time". exact I. Qed.
