From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From prosa Require Import behavior.job.
From LeanImport Require Import Lean.
Require Import ImportedEasy93 ImportedNatBridge TimeJobCertificates.

(** The Rocq source class is definitionally its sole function field, whereas
    Lean uses an actual one-field structure.  Equality of records/functions
    would require function extensionality, so the isomorphism is stated using
    complete field observation. *)
Definition export_job_arrival (Job : eqType)
    (arrivalL : Prosa_Behavior_Job_JobArrival Job) :
    prosa.behavior.job.JobArrival Job :=
  fun j => imported_to_instant
    (Prosa_Behavior_Job_JobArrival_job_arrival Job arrivalL j).

Definition JobArrivalRel (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (arrivalL : Prosa_Behavior_Job_JobArrival Job) : SProp :=
  forall j : Job,
    ImportedNatRel
      (@prosa.behavior.job.job_arrival Job arrivalR j)
      (Prosa_Behavior_Job_JobArrival_job_arrival Job arrivalL j).

Definition JobArrivalObsEqR (Job : eqType)
    (left right : prosa.behavior.job.JobArrival Job) : Prop :=
  forall j : Job,
    Logic.eq (@prosa.behavior.job.job_arrival Job left j)
      (@prosa.behavior.job.job_arrival Job right j).

Definition JobArrivalObsEqL (Job : eqType)
    (left right : Prosa_Behavior_Job_JobArrival Job) : SProp :=
  forall j : Job,
    eq (Prosa_Behavior_Job_JobArrival_job_arrival Job left j)
      (Prosa_Behavior_Job_JobArrival_job_arrival Job right j).

Lemma job_arrival_constructor_correspondence (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job) :
  JobArrivalRel Job arrivalR (import_job_arrival Job arrivalR).
Proof. intros j. exact (eq_refl _). Qed.

Lemma job_arrival_export_correspondence (Job : eqType)
    (arrivalL : Prosa_Behavior_Job_JobArrival Job) :
  JobArrivalRel Job (export_job_arrival Job arrivalL) arrivalL.
Proof.
  intros j. unfold ImportedNatRel, export_job_arrival, imported_to_instant,
    instant_to_imported.
  exact (imported_nat_roundtrip _).
Qed.

Lemma job_arrival_source_roundtrip (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job) :
  JobArrivalObsEqR Job
    (export_job_arrival Job (import_job_arrival Job arrivalR)) arrivalR.
Proof.
  intros j. unfold export_job_arrival, import_job_arrival,
    imported_to_instant, instant_to_imported.
  exact (rocq_nat_roundtrip _).
Qed.

Lemma job_arrival_target_roundtrip (Job : eqType)
    (arrivalL : Prosa_Behavior_Job_JobArrival Job) :
  JobArrivalObsEqL Job
    (import_job_arrival Job (export_job_arrival Job arrivalL)) arrivalL.
Proof.
  intros j. unfold import_job_arrival, export_job_arrival,
    imported_to_instant, instant_to_imported.
  exact (imported_nat_roundtrip _).
Qed.

Lemma job_arrival_projection_complete (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (arrivalL : Prosa_Behavior_Job_JobArrival Job)
    (Hrel : JobArrivalRel Job arrivalR arrivalL) (j : Job) :
  ImportedNatRel
    (@prosa.behavior.job.job_arrival Job arrivalR j)
    (Prosa_Behavior_Job_JobArrival_job_arrival Job arrivalL j).
Proof. exact (Hrel j). Qed.

Print Assumptions job_arrival_constructor_correspondence.
Print Assumptions job_arrival_export_correspondence.
Print Assumptions job_arrival_source_roundtrip.
Print Assumptions job_arrival_target_roundtrip.
Print Assumptions job_arrival_projection_complete.
