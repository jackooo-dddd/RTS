From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From prosa Require Import analysis.definitions.sbf.periodic.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPeriodic.
From FoundationCertificates Require Import PeriodicCorrespondence.

Check @prosa.analysis.definitions.sbf.periodic.periodic_resource_model.
Check @prosa.analysis.definitions.sbf.periodic.prm_sbf.
Check ImportedPeriodic.Prosa_Analysis_Definitions_Sbf_Periodic_periodic_resource_model.
Check ImportedPeriodic.Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf.
Check @periodic_resource_model_correspondence.
Check @prm_sbf_correspondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN periodic_bound". exact I. Qed.
Print Assumptions periodic_bound_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END periodic_bound". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN periodic_resource_model". exact I. Qed.
Print Assumptions periodic_resource_model_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END periodic_resource_model". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN prm_sbf". exact I. Qed.
Print Assumptions prm_sbf_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END prm_sbf". exact I. Qed.
