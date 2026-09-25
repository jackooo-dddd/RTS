From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From prosa Require Import model.readiness.jitter.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJitterPublic.
From FoundationCertificates Require Import JitterBaseAdapter
  JitterCorrespondence JitterHelperCorrespondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN JobJitter". exact I. Qed.
Print Assumptions ji_jitter_class_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END JobJitter". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN is_released". exact I. Qed.
Print Assumptions ji_is_released_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END is_released". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN jitter_ready_instance_field". exact I. Qed.
Print Assumptions ji_helper_ready_field_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END jitter_ready_instance_field". exact I. Qed.
