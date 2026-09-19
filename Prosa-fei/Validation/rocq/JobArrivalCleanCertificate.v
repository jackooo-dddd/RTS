From mathcomp Require Import eqtype.
From prosa Require Import behavior.job.
From LeanImport Require Import Lean.
Require Import ImportedJobArrivalClean93.

Fixpoint clean_nat_to_imported (n : Datatypes.nat) : Nat :=
  match n with
  | Datatypes.O => Nat_zero
  | Datatypes.S n' => Nat_succ (clean_nat_to_imported n')
  end.

Fixpoint clean_imported_to_nat (n : Nat) : Datatypes.nat :=
  match n with
  | Nat_zero => Datatypes.O
  | Nat_succ n' => Datatypes.S (clean_imported_to_nat n')
  end.

Lemma clean_nat_roundtrip (n : Datatypes.nat) :
  Logic.eq (clean_imported_to_nat (clean_nat_to_imported n)) n.
Proof. induction n; cbn; first reflexivity. f_equal. exact IHn. Qed.

Definition clean_succ_congr (a b : Nat) :
    Logic.eq a b -> Logic.eq (Nat_succ a) (Nat_succ b) :=
  fun H => match H in Logic.eq _ z return Logic.eq (Nat_succ a) (Nat_succ z) with
           | Logic.eq_refl => Logic.eq_refl
           end.

Lemma clean_imported_roundtrip (n : Nat) :
  Logic.eq (clean_nat_to_imported (clean_imported_to_nat n)) n.
Proof.
  induction n; cbn; first reflexivity.
  exact (clean_succ_congr _ _ IHn).
Qed.

Definition clean_import_job_arrival (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job) :
    Prosa_Behavior_Job_JobArrival Job :=
  Prosa_Behavior_Job_JobArrival_mk Job
    (fun j => clean_nat_to_imported
      (@prosa.behavior.job.job_arrival Job arrivalR j)).

Definition clean_export_job_arrival (Job : eqType)
    (arrivalL : Prosa_Behavior_Job_JobArrival Job) :
    prosa.behavior.job.JobArrival Job :=
  fun j => clean_imported_to_nat
    (Prosa_Behavior_Job_JobArrival_job_arrival Job arrivalL j).

Theorem clean_job_arrival_source_roundtrip (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job) (j : Job) :
  Logic.eq
    (@prosa.behavior.job.job_arrival Job
      (clean_export_job_arrival Job (clean_import_job_arrival Job arrivalR)) j)
    (@prosa.behavior.job.job_arrival Job arrivalR j).
Proof. exact (clean_nat_roundtrip _). Qed.

Theorem clean_job_arrival_target_roundtrip (Job : eqType)
    (arrivalL : Prosa_Behavior_Job_JobArrival Job) (j : Job) :
  Logic.eq
    (Prosa_Behavior_Job_JobArrival_job_arrival Job
      (clean_import_job_arrival Job (clean_export_job_arrival Job arrivalL)) j)
    (Prosa_Behavior_Job_JobArrival_job_arrival Job arrivalL j).
Proof. exact (clean_imported_roundtrip _). Qed.

Print Assumptions clean_job_arrival_source_roundtrip.
Print Assumptions clean_job_arrival_target_roundtrip.
