From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import analysis.definitions.service.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedAnalysisService.
From FoundationCertificates Require Import AnalysisServiceCorrespondence.

Check @prosa.analysis.definitions.service.served_jobs_at.
Check @prosa.analysis.definitions.service.served_job_at.
Check ImportedAnalysisService.Prosa_Analysis_Definitions_Service_served_jobs_at.
Check ImportedAnalysisService.Prosa_Analysis_Definitions_Service_served_job_at.
Check @served_jobs_at_correspondence.
Check @served_job_at_correspondence.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN as_ohead". exact I. Qed.
Print Assumptions as_ohead_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END as_ohead". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN served_jobs_at". exact I. Qed.
Print Assumptions served_jobs_at_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END served_jobs_at". exact I. Qed.

Goal Logic.True. Proof. idtac "AUDIT_BEGIN served_job_at". exact I. Qed.
Print Assumptions served_job_at_correspondence.
Goal Logic.True. Proof. idtac "AUDIT_END served_job_at". exact I. Qed.
