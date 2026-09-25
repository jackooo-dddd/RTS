From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From prosa Require Import model.readiness.jitter.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJitterPublic.
From FoundationCertificates Require Import PropSPropFoundation
  SubadditivityNatCorrespondence JitterBaseAdapter.

(** The Rocq class reduces to its one function field. The Lean class is a
    one-field structure with an explicit equality decision parameter. *)
Definition JiJitterRel (Job : eqType)
    (d : ImportedJitterPublic.DecidableEq Job)
    (jr : prosa.model.readiness.jitter.JobJitter Job)
    (jl : ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter
      Job d) : SProp :=
  forall j : Job,
    SubNatRel (@prosa.model.readiness.jitter.job_jitter Job jr j)
      (ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter_job_jitter
        Job d jl j).

Definition ji_import_jitter (Job : eqType)
    (d : ImportedJitterPublic.DecidableEq Job)
    (jr : prosa.model.readiness.jitter.JobJitter Job) :
    ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter Job d :=
  ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter_mk Job d
    (fun j => sub_nat_to_imported
      (@prosa.model.readiness.jitter.job_jitter Job jr j)).

Definition ji_export_jitter (Job : eqType)
    (d : ImportedJitterPublic.DecidableEq Job)
    (jl : ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter
      Job d) : prosa.model.readiness.jitter.JobJitter Job :=
  fun j => sub_nat_to_rocq
    (ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter_job_jitter
      Job d jl j).

Lemma ji_jitter_import_certificate (Job : eqType)
    (d : ImportedJitterPublic.DecidableEq Job)
    (jr : prosa.model.readiness.jitter.JobJitter Job) :
  JiJitterRel Job d jr (ji_import_jitter Job d jr).
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Lemma ji_jitter_export_certificate (Job : eqType)
    (d : ImportedJitterPublic.DecidableEq Job)
    (jl : ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter
      Job d) :
  JiJitterRel Job d (ji_export_jitter Job d jl) jl.
Proof. intro j. exact (sub_nat_imported_roundtrip _). Qed.

Lemma ji_jitter_source_roundtrip (Job : eqType)
    (d : ImportedJitterPublic.DecidableEq Job)
    (jr : prosa.model.readiness.jitter.JobJitter Job) (j : Job) :
  Logic.eq
    (@prosa.model.readiness.jitter.job_jitter Job
      (ji_export_jitter Job d (ji_import_jitter Job d jr)) j)
    (@prosa.model.readiness.jitter.job_jitter Job jr j).
Proof. exact (sub_nat_rocq_roundtrip _). Qed.

Lemma ji_jitter_target_roundtrip (Job : eqType)
    (d : ImportedJitterPublic.DecidableEq Job)
    (jl : ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter
      Job d) (j : Job) :
  Lean.eq
    (ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter_job_jitter
      Job d (ji_import_jitter Job d (ji_export_jitter Job d jl)) j)
    (ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter_job_jitter
      Job d jl j).
Proof. exact (sub_nat_imported_roundtrip _). Qed.

Record JiJitterClassCertificate (Job : eqType)
    (d : ImportedJitterPublic.DecidableEq Job) : Type := {
  ji_class_import : forall jr,
    JiJitterRel Job d jr (ji_import_jitter Job d jr);
  ji_class_export : forall jl,
    JiJitterRel Job d (ji_export_jitter Job d jl) jl;
  ji_class_source_roundtrip : forall jr j,
    Logic.eq
      (@prosa.model.readiness.jitter.job_jitter Job
        (ji_export_jitter Job d (ji_import_jitter Job d jr)) j)
      (@prosa.model.readiness.jitter.job_jitter Job jr j);
  ji_class_target_roundtrip : forall jl j,
    Lean.eq
      (ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter_job_jitter
        Job d (ji_import_jitter Job d (ji_export_jitter Job d jl)) j)
      (ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter_job_jitter
        Job d jl j)
}.

Definition ji_jitter_class_correspondence (Job : eqType)
    (d : ImportedJitterPublic.DecidableEq Job) :
    JiJitterClassCertificate Job d :=
  {| ji_class_import := ji_jitter_import_certificate Job d;
     ji_class_export := ji_jitter_export_certificate Job d;
     ji_class_source_roundtrip := ji_jitter_source_roundtrip Job d;
     ji_class_target_roundtrip := ji_jitter_target_roundtrip Job d |}.

(** The arrival function is an already accepted boundary. This relation
    states its pointwise input contract against the same actual imported
    Jitter artifact, avoiding any unverified re-encoding of arrival times. *)
Definition JiArrivalRel (Job : eqType)
    (d : ImportedJitterPublic.DecidableEq Job)
    (ar : prosa.behavior.job.JobArrival Job)
    (al : ImportedJitterPublic.Prosa_Behavior_Job_JobArrival Job d) : SProp :=
  forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job ar j)
      (ImportedJitterPublic.Prosa_Behavior_Job_JobArrival_job_arrival
        Job d al j).

Lemma ji_is_released_correspondence
    (Job : eqType) (d : ImportedJitterPublic.DecidableEq Job)
    (ar : prosa.behavior.job.JobArrival Job)
    (al : ImportedJitterPublic.Prosa_Behavior_Job_JobArrival Job d)
    (jr : prosa.model.readiness.jitter.JobJitter Job)
    (jl : ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter
      Job d) (j : Job) (tR : nat) (tL : Lean.Nat) :
  JiArrivalRel Job d ar al -> JiJitterRel Job d jr jl ->
  SubNatRel tR tL ->
  JiBoolRel (@prosa.model.readiness.jitter.is_released Job ar jr j tR)
    (ImportedJitterPublic.Prosa_Model_Readiness_Jitter_is_released
      Job d al jl j tL).
Proof.
  intros Harr Hjit Ht.
  unfold prosa.model.readiness.jitter.is_released.
  cbn [ImportedJitterPublic.Prosa_Model_Readiness_Jitter_is_released].
  apply ji_decide_bool_correspondence.
  apply sub_nat_le_correspondence.
  - apply sub_add_correspondence.
    + exact (Harr j).
    + exact (Hjit j).
  - exact Ht.
Qed.

Print Assumptions ji_jitter_import_certificate.
Print Assumptions ji_jitter_export_certificate.
Print Assumptions ji_jitter_source_roundtrip.
Print Assumptions ji_jitter_target_roundtrip.
Print Assumptions ji_jitter_class_correspondence.
Print Assumptions ji_is_released_correspondence.
