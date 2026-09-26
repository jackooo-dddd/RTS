(* Re-bound copy of accepted certificates/model_readiness_jitter/JitterSvcJobOperations.v for the analysis/facts/behavior/arrivals
   artifact; only the imported module name differs. *)
(* Re-bound copy of the accepted readiness/basic JitterSvcJobOperations.v for the
   jitter projection artifact; only module names differ. *)
(** GENERATED ARTIFACT-LOCAL INSTANTIATION.
    source: Validation/certificates/behavior_service/ServiceJobOperations.v
    source-sha256: 1b226a5aa8353e17511151540b0353e56ec77c11910443222b40c1a37eb14d13
    imported-artifact-sha256: e34025aae0f77959dc58e20663acf5f7abdd5af7df286b3f30e38debcd065838 *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From prosa Require Import behavior.arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReadinessSequential ImportedSubadditivity.
From FoundationCertificates Require Import LogicalRelation
  SubadditivityNatCorrespondence JitterSvcBaseAdapter
  JitterSvcNatBoolOperations.

(** Full one-field class correspondence for the Job observations used by
Service.  The explicit equality instance is part of every imported class
boundary, as required by the v0.6 representation policy. *)

Definition SvcJobCostRel (T : eqType)
    (costR : prosa.behavior.job.JobCost T)
    (costL : ImportedReadinessSequential.Prosa_Behavior_Job_JobCost T
      (svc_decidable_eq T)) : SProp :=
  forall j : T,
    SubNatRel (@prosa.behavior.job.job_cost T costR j)
      (ImportedReadinessSequential.Prosa_Behavior_Job_JobCost_job_cost T
        (svc_decidable_eq T) costL j).

Definition svc_import_job_cost (T : eqType)
    (costR : prosa.behavior.job.JobCost T) :
    ImportedReadinessSequential.Prosa_Behavior_Job_JobCost T
      (svc_decidable_eq T) :=
  ImportedReadinessSequential.Prosa_Behavior_Job_JobCost_mk T
    (svc_decidable_eq T)
    (fun j => sub_nat_to_imported
      (@prosa.behavior.job.job_cost T costR j)).

Definition svc_export_job_cost (T : eqType)
    (costL : ImportedReadinessSequential.Prosa_Behavior_Job_JobCost T
      (svc_decidable_eq T)) : prosa.behavior.job.JobCost T :=
  fun j => sub_nat_to_rocq
    (ImportedReadinessSequential.Prosa_Behavior_Job_JobCost_job_cost T
      (svc_decidable_eq T) costL j).

Lemma svc_job_cost_import (T : eqType)
    (costR : prosa.behavior.job.JobCost T) :
  SvcJobCostRel T costR (svc_import_job_cost T costR).
Proof. intro j. exact (sub_nat_rel_canonical _). Qed.

Lemma svc_job_cost_export (T : eqType)
    (costL : ImportedReadinessSequential.Prosa_Behavior_Job_JobCost T
      (svc_decidable_eq T)) :
  SvcJobCostRel T (svc_export_job_cost T costL) costL.
Proof. intro j. exact (sub_nat_rel_surjective _). Qed.

Lemma svc_job_cost_source_roundtrip (T : eqType)
    (costR : prosa.behavior.job.JobCost T) (j : T) :
  Logic.eq
    (@prosa.behavior.job.job_cost T
      (svc_export_job_cost T (svc_import_job_cost T costR)) j)
    (@prosa.behavior.job.job_cost T costR j).
Proof. exact (sub_nat_rocq_roundtrip _). Qed.

Lemma svc_job_cost_target_roundtrip (T : eqType)
    (costL : ImportedReadinessSequential.Prosa_Behavior_Job_JobCost T
      (svc_decidable_eq T)) (j : T) :
  Lean.eq
    (ImportedReadinessSequential.Prosa_Behavior_Job_JobCost_job_cost T
      (svc_decidable_eq T)
      (svc_import_job_cost T (svc_export_job_cost T costL)) j)
    (ImportedReadinessSequential.Prosa_Behavior_Job_JobCost_job_cost T
      (svc_decidable_eq T) costL j).
Proof. exact (sub_nat_imported_roundtrip _). Qed.

Definition SvcJobArrivalRel (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T)
    (arrivalL : ImportedReadinessSequential.Prosa_Behavior_Job_JobArrival T
      (svc_decidable_eq T)) : SProp :=
  forall j : T,
    SubNatRel (@prosa.behavior.job.job_arrival T arrivalR j)
      (ImportedReadinessSequential.Prosa_Behavior_Job_JobArrival_job_arrival T
        (svc_decidable_eq T) arrivalL j).

Definition svc_import_job_arrival (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T) :
    ImportedReadinessSequential.Prosa_Behavior_Job_JobArrival T
      (svc_decidable_eq T) :=
  ImportedReadinessSequential.Prosa_Behavior_Job_JobArrival_mk T
    (svc_decidable_eq T)
    (fun j => sub_nat_to_imported
      (@prosa.behavior.job.job_arrival T arrivalR j)).

Definition svc_export_job_arrival (T : eqType)
    (arrivalL : ImportedReadinessSequential.Prosa_Behavior_Job_JobArrival T
      (svc_decidable_eq T)) : prosa.behavior.job.JobArrival T :=
  fun j => sub_nat_to_rocq
    (ImportedReadinessSequential.Prosa_Behavior_Job_JobArrival_job_arrival T
      (svc_decidable_eq T) arrivalL j).

Lemma svc_job_arrival_import (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T) :
  SvcJobArrivalRel T arrivalR (svc_import_job_arrival T arrivalR).
Proof. intro j. exact (sub_nat_rel_canonical _). Qed.

Lemma svc_job_arrival_export (T : eqType)
    (arrivalL : ImportedReadinessSequential.Prosa_Behavior_Job_JobArrival T
      (svc_decidable_eq T)) :
  SvcJobArrivalRel T (svc_export_job_arrival T arrivalL) arrivalL.
Proof. intro j. exact (sub_nat_rel_surjective _). Qed.

Lemma svc_job_arrival_source_roundtrip (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T) (j : T) :
  Logic.eq
    (@prosa.behavior.job.job_arrival T
      (svc_export_job_arrival T (svc_import_job_arrival T arrivalR)) j)
    (@prosa.behavior.job.job_arrival T arrivalR j).
Proof. exact (sub_nat_rocq_roundtrip _). Qed.

Lemma svc_job_arrival_target_roundtrip (T : eqType)
    (arrivalL : ImportedReadinessSequential.Prosa_Behavior_Job_JobArrival T
      (svc_decidable_eq T)) (j : T) :
  Lean.eq
    (ImportedReadinessSequential.Prosa_Behavior_Job_JobArrival_job_arrival T
      (svc_decidable_eq T)
      (svc_import_job_arrival T (svc_export_job_arrival T arrivalL)) j)
    (ImportedReadinessSequential.Prosa_Behavior_Job_JobArrival_job_arrival T
      (svc_decidable_eq T) arrivalL j).
Proof. exact (sub_nat_imported_roundtrip _). Qed.

Lemma svc_has_arrived_related (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T)
    (arrivalL : ImportedReadinessSequential.Prosa_Behavior_Job_JobArrival T
      (svc_decidable_eq T)) (j : T) :
  SvcJobArrivalRel T arrivalR arrivalL ->
  forall tR tL, SubNatRel tR tL ->
  SvcBoolRel
    (@prosa.behavior.arrival_sequence.has_arrived T arrivalR j tR)
    (ImportedReadinessSequential.Prosa_Behavior_Arrival_sequence_has_arrived T
      (svc_decidable_eq T) arrivalL j tL).
Proof.
  intros Harrival tR tL Ht. cbn.
  exact (svc_decide_le_related _ _ _ _ (Harrival j) Ht).
Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN svc_job_operations". exact I. Qed.
Print Assumptions svc_job_cost_import.
Print Assumptions svc_job_cost_export.
Print Assumptions svc_job_arrival_import.
Print Assumptions svc_job_arrival_export.
Print Assumptions svc_has_arrived_related.
Goal Logic.True.
Proof. idtac "AUDIT_END svc_job_operations". exact I. Qed.
