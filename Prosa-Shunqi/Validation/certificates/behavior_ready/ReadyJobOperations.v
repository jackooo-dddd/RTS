(** GENERATED ARTIFACT-LOCAL INSTANTIATION.
    source: /Users/shunqiwang/CityuHK/Research/Lean/TranslationProof/Prosa-Shunqi/Validation/certificates/behavior_service/ServiceJobOperations.v
    source-sha256: 1b226a5aa8353e17511151540b0353e56ec77c11910443222b40c1a37eb14d13
    imported-artifact-sha256: 83ce15ec777b3ecaf9444952d0e3f31ed4f667f5b9fb4b93736302a524a7b210 *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From prosa Require Import behavior.arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReady ImportedSubadditivity.
From FoundationCertificates Require Import LogicalRelation
  SubadditivityNatCorrespondence ReadyBaseAdapter
  ReadyNatBoolOperations.

(** Full one-field class correspondence for the Job observations used by
Service.  The explicit equality instance is part of every imported class
boundary, as required by the v0.6 representation policy. *)

Definition SvcJobCostRel (T : eqType)
    (costR : prosa.behavior.job.JobCost T)
    (costL : ImportedReady.Prosa_Behavior_Job_JobCost T
      (svc_decidable_eq T)) : SProp :=
  forall j : T,
    SubNatRel (@prosa.behavior.job.job_cost T costR j)
      (ImportedReady.Prosa_Behavior_Job_JobCost_job_cost T
        (svc_decidable_eq T) costL j).

Definition svc_import_job_cost (T : eqType)
    (costR : prosa.behavior.job.JobCost T) :
    ImportedReady.Prosa_Behavior_Job_JobCost T
      (svc_decidable_eq T) :=
  ImportedReady.Prosa_Behavior_Job_JobCost_mk T
    (svc_decidable_eq T)
    (fun j => sub_nat_to_imported
      (@prosa.behavior.job.job_cost T costR j)).

Definition svc_export_job_cost (T : eqType)
    (costL : ImportedReady.Prosa_Behavior_Job_JobCost T
      (svc_decidable_eq T)) : prosa.behavior.job.JobCost T :=
  fun j => sub_nat_to_rocq
    (ImportedReady.Prosa_Behavior_Job_JobCost_job_cost T
      (svc_decidable_eq T) costL j).

Lemma svc_job_cost_import (T : eqType)
    (costR : prosa.behavior.job.JobCost T) :
  SvcJobCostRel T costR (svc_import_job_cost T costR).
Proof. intro j. exact (sub_nat_rel_canonical _). Qed.

Lemma svc_job_cost_export (T : eqType)
    (costL : ImportedReady.Prosa_Behavior_Job_JobCost T
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
    (costL : ImportedReady.Prosa_Behavior_Job_JobCost T
      (svc_decidable_eq T)) (j : T) :
  Lean.eq
    (ImportedReady.Prosa_Behavior_Job_JobCost_job_cost T
      (svc_decidable_eq T)
      (svc_import_job_cost T (svc_export_job_cost T costL)) j)
    (ImportedReady.Prosa_Behavior_Job_JobCost_job_cost T
      (svc_decidable_eq T) costL j).
Proof. exact (sub_nat_imported_roundtrip _). Qed.

Definition SvcJobArrivalRel (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T)
    (arrivalL : ImportedReady.Prosa_Behavior_Job_JobArrival T
      (svc_decidable_eq T)) : SProp :=
  forall j : T,
    SubNatRel (@prosa.behavior.job.job_arrival T arrivalR j)
      (ImportedReady.Prosa_Behavior_Job_JobArrival_job_arrival T
        (svc_decidable_eq T) arrivalL j).

Definition svc_import_job_arrival (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T) :
    ImportedReady.Prosa_Behavior_Job_JobArrival T
      (svc_decidable_eq T) :=
  ImportedReady.Prosa_Behavior_Job_JobArrival_mk T
    (svc_decidable_eq T)
    (fun j => sub_nat_to_imported
      (@prosa.behavior.job.job_arrival T arrivalR j)).

Definition svc_export_job_arrival (T : eqType)
    (arrivalL : ImportedReady.Prosa_Behavior_Job_JobArrival T
      (svc_decidable_eq T)) : prosa.behavior.job.JobArrival T :=
  fun j => sub_nat_to_rocq
    (ImportedReady.Prosa_Behavior_Job_JobArrival_job_arrival T
      (svc_decidable_eq T) arrivalL j).

Lemma svc_job_arrival_import (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T) :
  SvcJobArrivalRel T arrivalR (svc_import_job_arrival T arrivalR).
Proof. intro j. exact (sub_nat_rel_canonical _). Qed.

Lemma svc_job_arrival_export (T : eqType)
    (arrivalL : ImportedReady.Prosa_Behavior_Job_JobArrival T
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
    (arrivalL : ImportedReady.Prosa_Behavior_Job_JobArrival T
      (svc_decidable_eq T)) (j : T) :
  Lean.eq
    (ImportedReady.Prosa_Behavior_Job_JobArrival_job_arrival T
      (svc_decidable_eq T)
      (svc_import_job_arrival T (svc_export_job_arrival T arrivalL)) j)
    (ImportedReady.Prosa_Behavior_Job_JobArrival_job_arrival T
      (svc_decidable_eq T) arrivalL j).
Proof. exact (sub_nat_imported_roundtrip _). Qed.

Definition SvcJobDeadlineRel (T : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline T)
    (deadlineL : ImportedReady.Prosa_Behavior_Job_JobDeadline T
      (svc_decidable_eq T)) : SProp :=
  forall j : T,
    SubNatRel (@prosa.behavior.job.job_deadline T deadlineR j)
      (ImportedReady.Prosa_Behavior_Job_JobDeadline_job_deadline T
        (svc_decidable_eq T) deadlineL j).

Definition svc_import_job_deadline (T : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline T) :
    ImportedReady.Prosa_Behavior_Job_JobDeadline T
      (svc_decidable_eq T) :=
  ImportedReady.Prosa_Behavior_Job_JobDeadline_mk T
    (svc_decidable_eq T)
    (fun j => sub_nat_to_imported
      (@prosa.behavior.job.job_deadline T deadlineR j)).

Definition svc_export_job_deadline (T : eqType)
    (deadlineL : ImportedReady.Prosa_Behavior_Job_JobDeadline T
      (svc_decidable_eq T)) : prosa.behavior.job.JobDeadline T :=
  fun j => sub_nat_to_rocq
    (ImportedReady.Prosa_Behavior_Job_JobDeadline_job_deadline T
      (svc_decidable_eq T) deadlineL j).

Lemma svc_job_deadline_import (T : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline T) :
  SvcJobDeadlineRel T deadlineR (svc_import_job_deadline T deadlineR).
Proof. intro j. exact (sub_nat_rel_canonical _). Qed.

Lemma svc_job_deadline_export (T : eqType)
    (deadlineL : ImportedReady.Prosa_Behavior_Job_JobDeadline T
      (svc_decidable_eq T)) :
  SvcJobDeadlineRel T (svc_export_job_deadline T deadlineL) deadlineL.
Proof. intro j. exact (sub_nat_rel_surjective _). Qed.

Lemma svc_job_deadline_source_roundtrip (T : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline T) (j : T) :
  Logic.eq
    (@prosa.behavior.job.job_deadline T
      (svc_export_job_deadline T (svc_import_job_deadline T deadlineR)) j)
    (@prosa.behavior.job.job_deadline T deadlineR j).
Proof. exact (sub_nat_rocq_roundtrip _). Qed.

Lemma svc_job_deadline_target_roundtrip (T : eqType)
    (deadlineL : ImportedReady.Prosa_Behavior_Job_JobDeadline T
      (svc_decidable_eq T)) (j : T) :
  Lean.eq
    (ImportedReady.Prosa_Behavior_Job_JobDeadline_job_deadline T
      (svc_decidable_eq T)
      (svc_import_job_deadline T (svc_export_job_deadline T deadlineL)) j)
    (ImportedReady.Prosa_Behavior_Job_JobDeadline_job_deadline T
      (svc_decidable_eq T) deadlineL j).
Proof. exact (sub_nat_imported_roundtrip _). Qed.

Lemma svc_has_arrived_related (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T)
    (arrivalL : ImportedReady.Prosa_Behavior_Job_JobArrival T
      (svc_decidable_eq T)) (j : T) :
  SvcJobArrivalRel T arrivalR arrivalL ->
  forall tR tL, SubNatRel tR tL ->
  SvcBoolRel
    (@prosa.behavior.arrival_sequence.has_arrived T arrivalR j tR)
    (ImportedReady.Prosa_Behavior_Arrival_sequence_has_arrived T
      (svc_decidable_eq T) arrivalL j tL).
Proof.
  intros Harrival tR tL Ht. cbn.
  exact (svc_decide_le_related _ _ _ _ (Harrival j) Ht).
Qed.

Lemma svc_arrived_before_related (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T)
    (arrivalL : ImportedReady.Prosa_Behavior_Job_JobArrival T
      (svc_decidable_eq T)) (j : T) :
  SvcJobArrivalRel T arrivalR arrivalL ->
  forall tR tL, SubNatRel tR tL ->
  SvcBoolRel
    (@prosa.behavior.arrival_sequence.arrived_before T arrivalR j tR)
    (ImportedReady.Prosa_Behavior_Arrival_sequence_arrived_before T
      (svc_decidable_eq T) arrivalL j tL).
Proof.
  intros Harrival tR tL Ht. cbn.
  exact (svc_decide_lt_related _ _ _ _ (Harrival j) Ht).
Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN svc_job_operations". exact I. Qed.
Print Assumptions svc_job_cost_import.
Print Assumptions svc_job_cost_export.
Print Assumptions svc_job_arrival_import.
Print Assumptions svc_job_arrival_export.
Print Assumptions svc_job_deadline_import.
Print Assumptions svc_job_deadline_export.
Print Assumptions svc_has_arrived_related.
Print Assumptions svc_arrived_before_related.
Goal Logic.True.
Proof. idtac "AUDIT_END svc_job_operations". exact I. Qed.
