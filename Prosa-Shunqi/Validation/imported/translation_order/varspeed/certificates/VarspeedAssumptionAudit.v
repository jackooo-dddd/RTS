From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.varspeed.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedVarspeedFull.
From FoundationCertificates Require Import
  VarspeedBaseAdapter VarspeedCorrespondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN processor_state". exact I. Qed.
Print Assumptions vs_state_type_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END processor_state". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN varspeed_scheduled_on". exact I. Qed.
Print Assumptions vs_scheduled_on_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END varspeed_scheduled_on". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN varspeed_supply_on". exact I. Qed.
Print Assumptions vs_supply_on_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END varspeed_supply_on". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN varspeed_service_on". exact I. Qed.
Print Assumptions vs_service_on_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END varspeed_service_on". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN pstate_instance". exact I. Qed.
Print Assumptions vs_processor_state_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END pstate_instance". exact I. Qed.
