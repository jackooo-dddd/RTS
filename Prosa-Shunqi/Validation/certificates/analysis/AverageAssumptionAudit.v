From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From prosa Require Import analysis.definitions.sbf.average.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedAverage.
From FoundationCertificates Require Import AverageCorrespondence.

Check @prosa.analysis.definitions.sbf.average.average_resource_model.
Check @prosa.analysis.definitions.sbf.average.arm_sbf.
Check ImportedAverage.Prosa_Analysis_Definitions_Sbf_Average_average_resource_model.
Check ImportedAverage.Prosa_Analysis_Definitions_Sbf_Average_arm_sbf.
Check @average_resource_model_correspondence.
Check @arm_sbf_correspondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN average_bound". exact I. Qed.
Print Assumptions average_bound_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END average_bound". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN arm_sbf". exact I. Qed.
Print Assumptions arm_sbf_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END arm_sbf". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN average_resource_model". exact I. Qed.
Print Assumptions average_resource_model_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END average_resource_model". exact I. Qed.
