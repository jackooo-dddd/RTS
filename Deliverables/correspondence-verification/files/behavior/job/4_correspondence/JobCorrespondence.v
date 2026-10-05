From mathcomp Require Import ssreflect ssrbool eqtype.
From prosa Require Import behavior.job.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTime ImportedJob.
From FoundationCertificates Require Import FoundationTimeCertificate
  JobEqTypeAdapter.

(** The actual imported Lean aliases [JobType], [work], and [instant] reduce
    to the carrier [Type] and imported [Nat], respectively.  The class
    correspondence below is deliberately observational: the Rocq classes
    elaborate to their sole function field, while Lean uses one-field
    structures carrying an explicit [DecidableEq] parameter. *)

Definition WorkRel
    (wR : prosa.behavior.job.work)
    (wL : ImportedJob.Prosa_Behavior_Job_work) : SProp :=
  eq (rocq_nat_to_imported wR) wL.

Definition work_to_imported
    (w : prosa.behavior.job.work) :
    ImportedJob.Prosa_Behavior_Job_work :=
  rocq_nat_to_imported w.

Definition imported_to_work
    (w : ImportedJob.Prosa_Behavior_Job_work) :
    prosa.behavior.job.work :=
  imported_nat_to_rocq w.

Lemma work_relation_total_certificate w :
  WorkRel w (work_to_imported w).
Proof. exact (eq_refl _). Qed.

Lemma work_source_roundtrip_certificate w :
  Logic.eq (imported_to_work (work_to_imported w)) w.
Proof. exact (rocq_nat_roundtrip w). Qed.

Lemma work_target_roundtrip_certificate w :
  eq (work_to_imported (imported_to_work w)) w.
Proof. exact (imported_nat_roundtrip w). Qed.

Definition JobCostRel (T : eqType)
    (costR : prosa.behavior.job.JobCost T)
    (costL : ImportedJob.Prosa_Behavior_Job_JobCost T
      (eqtype_to_job_decidable_eq T)) : SProp :=
  forall j : T,
    WorkRel (@prosa.behavior.job.job_cost T costR j)
      (ImportedJob.Prosa_Behavior_Job_JobCost_job_cost T
        (eqtype_to_job_decidable_eq T) costL j).

Definition import_job_cost (T : eqType)
    (costR : prosa.behavior.job.JobCost T) :
    ImportedJob.Prosa_Behavior_Job_JobCost T
      (eqtype_to_job_decidable_eq T) :=
  ImportedJob.Prosa_Behavior_Job_JobCost_mk T
    (eqtype_to_job_decidable_eq T)
    (fun j => work_to_imported
      (@prosa.behavior.job.job_cost T costR j)).

Definition export_job_cost (T : eqType)
    (costL : ImportedJob.Prosa_Behavior_Job_JobCost T
      (eqtype_to_job_decidable_eq T)) :
    prosa.behavior.job.JobCost T :=
  fun j => imported_to_work
    (ImportedJob.Prosa_Behavior_Job_JobCost_job_cost T
      (eqtype_to_job_decidable_eq T) costL j).

Lemma job_cost_import_certificate (T : eqType)
    (costR : prosa.behavior.job.JobCost T) :
  JobCostRel T costR (import_job_cost T costR).
Proof. intros j. exact (eq_refl _). Qed.

Lemma job_cost_export_certificate (T : eqType)
    (costL : ImportedJob.Prosa_Behavior_Job_JobCost T
      (eqtype_to_job_decidable_eq T)) :
  JobCostRel T (export_job_cost T costL) costL.
Proof.
  intros j. unfold WorkRel, export_job_cost, imported_to_work,
    work_to_imported.
  exact (imported_nat_roundtrip _).
Qed.

Lemma job_cost_source_roundtrip_certificate (T : eqType)
    (costR : prosa.behavior.job.JobCost T) (j : T) :
  Logic.eq
    (@prosa.behavior.job.job_cost T
      (export_job_cost T (import_job_cost T costR)) j)
    (@prosa.behavior.job.job_cost T costR j).
Proof. exact (rocq_nat_roundtrip _). Qed.

Lemma job_cost_target_roundtrip_certificate (T : eqType)
    (costL : ImportedJob.Prosa_Behavior_Job_JobCost T
      (eqtype_to_job_decidable_eq T)) (j : T) :
  eq
    (ImportedJob.Prosa_Behavior_Job_JobCost_job_cost T
      (eqtype_to_job_decidable_eq T)
      (import_job_cost T (export_job_cost T costL)) j)
    (ImportedJob.Prosa_Behavior_Job_JobCost_job_cost T
      (eqtype_to_job_decidable_eq T) costL j).
Proof. exact (imported_nat_roundtrip _). Qed.

Definition JobArrivalRel (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T)
    (arrivalL : ImportedJob.Prosa_Behavior_Job_JobArrival T
      (eqtype_to_job_decidable_eq T)) : SProp :=
  forall j : T,
    InstantRel (@prosa.behavior.job.job_arrival T arrivalR j)
      (ImportedJob.Prosa_Behavior_Job_JobArrival_job_arrival T
        (eqtype_to_job_decidable_eq T) arrivalL j).

Definition import_job_arrival (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T) :
    ImportedJob.Prosa_Behavior_Job_JobArrival T
      (eqtype_to_job_decidable_eq T) :=
  ImportedJob.Prosa_Behavior_Job_JobArrival_mk T
    (eqtype_to_job_decidable_eq T)
    (fun j => instant_to_imported
      (@prosa.behavior.job.job_arrival T arrivalR j)).

Definition export_job_arrival (T : eqType)
    (arrivalL : ImportedJob.Prosa_Behavior_Job_JobArrival T
      (eqtype_to_job_decidable_eq T)) :
    prosa.behavior.job.JobArrival T :=
  fun j => imported_to_instant
    (ImportedJob.Prosa_Behavior_Job_JobArrival_job_arrival T
      (eqtype_to_job_decidable_eq T) arrivalL j).

Lemma job_arrival_import_certificate (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T) :
  JobArrivalRel T arrivalR (import_job_arrival T arrivalR).
Proof. intros j. exact (eq_refl _). Qed.

Lemma job_arrival_export_certificate (T : eqType)
    (arrivalL : ImportedJob.Prosa_Behavior_Job_JobArrival T
      (eqtype_to_job_decidable_eq T)) :
  JobArrivalRel T (export_job_arrival T arrivalL) arrivalL.
Proof.
  intros j. unfold InstantRel, export_job_arrival, imported_to_instant,
    instant_to_imported.
  exact (imported_nat_roundtrip _).
Qed.

Lemma job_arrival_source_roundtrip_certificate (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T) (j : T) :
  Logic.eq
    (@prosa.behavior.job.job_arrival T
      (export_job_arrival T (import_job_arrival T arrivalR)) j)
    (@prosa.behavior.job.job_arrival T arrivalR j).
Proof. exact (rocq_nat_roundtrip _). Qed.

Lemma job_arrival_target_roundtrip_certificate (T : eqType)
    (arrivalL : ImportedJob.Prosa_Behavior_Job_JobArrival T
      (eqtype_to_job_decidable_eq T)) (j : T) :
  eq
    (ImportedJob.Prosa_Behavior_Job_JobArrival_job_arrival T
      (eqtype_to_job_decidable_eq T)
      (import_job_arrival T (export_job_arrival T arrivalL)) j)
    (ImportedJob.Prosa_Behavior_Job_JobArrival_job_arrival T
      (eqtype_to_job_decidable_eq T) arrivalL j).
Proof. exact (imported_nat_roundtrip _). Qed.

Definition JobDeadlineRel (T : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline T)
    (deadlineL : ImportedJob.Prosa_Behavior_Job_JobDeadline T
      (eqtype_to_job_decidable_eq T)) : SProp :=
  forall j : T,
    InstantRel (@prosa.behavior.job.job_deadline T deadlineR j)
      (ImportedJob.Prosa_Behavior_Job_JobDeadline_job_deadline T
        (eqtype_to_job_decidable_eq T) deadlineL j).

Definition import_job_deadline (T : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline T) :
    ImportedJob.Prosa_Behavior_Job_JobDeadline T
      (eqtype_to_job_decidable_eq T) :=
  ImportedJob.Prosa_Behavior_Job_JobDeadline_mk T
    (eqtype_to_job_decidable_eq T)
    (fun j => instant_to_imported
      (@prosa.behavior.job.job_deadline T deadlineR j)).

Definition export_job_deadline (T : eqType)
    (deadlineL : ImportedJob.Prosa_Behavior_Job_JobDeadline T
      (eqtype_to_job_decidable_eq T)) :
    prosa.behavior.job.JobDeadline T :=
  fun j => imported_to_instant
    (ImportedJob.Prosa_Behavior_Job_JobDeadline_job_deadline T
      (eqtype_to_job_decidable_eq T) deadlineL j).

Lemma job_deadline_import_certificate (T : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline T) :
  JobDeadlineRel T deadlineR (import_job_deadline T deadlineR).
Proof. intros j. exact (eq_refl _). Qed.

Lemma job_deadline_export_certificate (T : eqType)
    (deadlineL : ImportedJob.Prosa_Behavior_Job_JobDeadline T
      (eqtype_to_job_decidable_eq T)) :
  JobDeadlineRel T (export_job_deadline T deadlineL) deadlineL.
Proof.
  intros j. unfold InstantRel, export_job_deadline, imported_to_instant,
    instant_to_imported.
  exact (imported_nat_roundtrip _).
Qed.

Lemma job_deadline_source_roundtrip_certificate (T : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline T) (j : T) :
  Logic.eq
    (@prosa.behavior.job.job_deadline T
      (export_job_deadline T (import_job_deadline T deadlineR)) j)
    (@prosa.behavior.job.job_deadline T deadlineR j).
Proof. exact (rocq_nat_roundtrip _). Qed.

Lemma job_deadline_target_roundtrip_certificate (T : eqType)
    (deadlineL : ImportedJob.Prosa_Behavior_Job_JobDeadline T
      (eqtype_to_job_decidable_eq T)) (j : T) :
  eq
    (ImportedJob.Prosa_Behavior_Job_JobDeadline_job_deadline T
      (eqtype_to_job_decidable_eq T)
      (import_job_deadline T (export_job_deadline T deadlineL)) j)
    (ImportedJob.Prosa_Behavior_Job_JobDeadline_job_deadline T
      (eqtype_to_job_decidable_eq T) deadlineL j).
Proof. exact (imported_nat_roundtrip _). Qed.

Print Assumptions work_relation_total_certificate.
Print Assumptions work_source_roundtrip_certificate.
Print Assumptions work_target_roundtrip_certificate.
Print Assumptions job_cost_import_certificate.
Print Assumptions job_cost_export_certificate.
Print Assumptions job_cost_source_roundtrip_certificate.
Print Assumptions job_cost_target_roundtrip_certificate.
Print Assumptions job_arrival_import_certificate.
Print Assumptions job_arrival_export_certificate.
Print Assumptions job_arrival_source_roundtrip_certificate.
Print Assumptions job_arrival_target_roundtrip_certificate.
Print Assumptions job_deadline_import_certificate.
Print Assumptions job_deadline_export_certificate.
Print Assumptions job_deadline_source_roundtrip_certificate.
Print Assumptions job_deadline_target_roundtrip_certificate.
