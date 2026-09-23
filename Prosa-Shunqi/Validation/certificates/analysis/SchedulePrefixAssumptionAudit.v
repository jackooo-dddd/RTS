From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import analysis.definitions.schedule_prefix.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSchedulePrefix.
From FoundationCertificates Require Import SchedulePrefixOperations.

Check @identical_prefix_correspondence.
Check @identical_prefix_scheduled_at_statement_correspondence.
Check @identical_prefix_inclusion_statement_correspondence.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN identical_prefix". exact I. Qed.
Print Assumptions identical_prefix_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END identical_prefix". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN scheduled_in_dependency". exact I. Qed.
Print Assumptions prefix_scheduled_in_related.
Goal Logic.True. Proof. idtac "AUDIT_END scheduled_in_dependency". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN scheduled_at_dependency". exact I. Qed.
Print Assumptions prefix_scheduled_at_related.
Goal Logic.True. Proof. idtac "AUDIT_END scheduled_at_dependency". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN identical_prefix_scheduled_at". exact I. Qed.
Print Assumptions identical_prefix_scheduled_at_statement_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END identical_prefix_scheduled_at". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN identical_prefix_inclusion". exact I. Qed.
Print Assumptions identical_prefix_inclusion_statement_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END identical_prefix_inclusion". exact I. Qed.
