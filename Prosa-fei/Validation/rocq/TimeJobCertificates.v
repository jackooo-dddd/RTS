From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From prosa Require Import behavior.job.
From LeanImport Require Import Lean.
Require Import ImportedEasy93 ImportedNatBridge.

(** Actual alias declarations: each endpoint names the imported Lean
    declaration rather than merely [Nat]. *)
Definition instant_to_imported
    (t : prosa.behavior.time.instant) : Prosa_Behavior_Time_instant :=
  rocq_nat_to_imported t.

Definition imported_to_instant
    (t : Prosa_Behavior_Time_instant) : prosa.behavior.time.instant :=
  imported_nat_to_rocq t.

Lemma instant_roundtrip_rocq t :
  Logic.eq (imported_to_instant (instant_to_imported t)) t.
Proof. exact (rocq_nat_roundtrip t). Qed.

Lemma instant_roundtrip_imported t :
  eq (instant_to_imported (imported_to_instant t)) t.
Proof. exact (imported_nat_roundtrip t). Qed.

Definition duration_to_imported
    (t : prosa.behavior.time.duration) : Prosa_Behavior_Time_duration :=
  rocq_nat_to_imported t.

Definition imported_to_duration
    (t : Prosa_Behavior_Time_duration) : prosa.behavior.time.duration :=
  imported_nat_to_rocq t.

Lemma duration_roundtrip_rocq t :
  Logic.eq (imported_to_duration (duration_to_imported t)) t.
Proof. exact (rocq_nat_roundtrip t). Qed.

Lemma duration_roundtrip_imported t :
  eq (duration_to_imported (imported_to_duration t)) t.
Proof. exact (imported_nat_roundtrip t). Qed.

Definition work_to_imported
    (w : prosa.behavior.job.work) : Prosa_Behavior_Job_work :=
  rocq_nat_to_imported w.

Definition imported_to_work
    (w : Prosa_Behavior_Job_work) : prosa.behavior.job.work :=
  imported_nat_to_rocq w.

Lemma work_roundtrip_rocq w :
  Logic.eq (imported_to_work (work_to_imported w)) w.
Proof. exact (rocq_nat_roundtrip w). Qed.

Lemma work_roundtrip_imported w :
  eq (work_to_imported (imported_to_work w)) w.
Proof. exact (imported_nat_roundtrip w). Qed.

(** Canonical record-representation maps on a shared eqType carrier. *)
Definition import_job_cost (Job : eqType)
    (costR : prosa.behavior.job.JobCost Job) :
    Prosa_Behavior_Job_JobCost Job :=
  Prosa_Behavior_Job_JobCost_mk Job
    (fun j => work_to_imported (@prosa.behavior.job.job_cost Job costR j)).

Lemma job_cost_projection_certificate (Job : eqType)
    (costR : prosa.behavior.job.JobCost Job) (j : Job) :
  ImportedNatRel
    (@prosa.behavior.job.job_cost Job costR j)
    (Prosa_Behavior_Job_JobCost_job_cost
       Job (import_job_cost Job costR) j).
Proof. exact (eq_refl _). Qed.

Definition import_job_arrival (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job) :
    Prosa_Behavior_Job_JobArrival Job :=
  Prosa_Behavior_Job_JobArrival_mk Job
    (fun j => instant_to_imported
      (@prosa.behavior.job.job_arrival Job arrivalR j)).

Lemma job_arrival_projection_certificate (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job) (j : Job) :
  ImportedNatRel
    (@prosa.behavior.job.job_arrival Job arrivalR j)
    (Prosa_Behavior_Job_JobArrival_job_arrival
       Job (import_job_arrival Job arrivalR) j).
Proof. exact (eq_refl _). Qed.

Definition import_job_deadline (Job : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline Job) :
    Prosa_Behavior_Job_JobDeadline Job :=
  Prosa_Behavior_Job_JobDeadline_mk Job
    (fun j => instant_to_imported
      (@prosa.behavior.job.job_deadline Job deadlineR j)).

Lemma job_deadline_projection_certificate (Job : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline Job) (j : Job) :
  ImportedNatRel
    (@prosa.behavior.job.job_deadline Job deadlineR j)
    (Prosa_Behavior_Job_JobDeadline_job_deadline
       Job (import_job_deadline Job deadlineR) j).
Proof. exact (eq_refl _). Qed.

Print Assumptions instant_roundtrip_imported.
Print Assumptions duration_roundtrip_imported.
Print Assumptions work_roundtrip_imported.
Print Assumptions job_cost_projection_certificate.
Print Assumptions job_arrival_projection_certificate.
Print Assumptions job_deadline_projection_certificate.
