From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From prosa Require Import behavior.arrival_sequence.
From LeanImport Require Import Lean.
Require Import ImportedEasy93 TimeJobCertificates ImportedNatOrderBridge.
Require Import ImportedListBridge.

Lemma has_arrived_certificate (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (j : Job) (t : prosa.behavior.time.instant) :
  ImportedBoolSPropRel
    (@prosa.behavior.arrival_sequence.has_arrived Job arrivalR j t)
    (Prosa_Behavior_Arrival_sequence_has_arrived
       Job (import_job_arrival Job arrivalR) j (instant_to_imported t)).
Proof.
  unfold prosa.behavior.arrival_sequence.has_arrived.
  unfold Prosa_Behavior_Arrival_sequence_has_arrived.
  cbv [import_job_arrival instant_to_imported
       Prosa_Behavior_Job_JobArrival_job_arrival
       LE_le_inst1 instLENat].
  exact (imported_nat_le_bridge
    (@prosa.behavior.job.job_arrival Job arrivalR j) t).
Qed.

Lemma arrived_before_certificate (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (j : Job) (t : prosa.behavior.time.instant) :
  ImportedBoolSPropRel
    (@prosa.behavior.arrival_sequence.arrived_before Job arrivalR j t)
    (Prosa_Behavior_Arrival_sequence_arrived_before
       Job (import_job_arrival Job arrivalR) j (instant_to_imported t)).
Proof.
  unfold prosa.behavior.arrival_sequence.arrived_before.
  unfold Prosa_Behavior_Arrival_sequence_arrived_before.
  cbv [import_job_arrival instant_to_imported
       Prosa_Behavior_Job_JobArrival_job_arrival
       LT_lt_inst1 instLTNat].
  exact (imported_nat_lt_bridge
    (@prosa.behavior.job.job_arrival Job arrivalR j) t).
Qed.

Lemma arrived_between_certificate (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (j : Job) (t1 t2 : prosa.behavior.time.instant) :
  ImportedBoolSPropRel
    (@prosa.behavior.arrival_sequence.arrived_between
       Job arrivalR j t1 t2)
    (Prosa_Behavior_Arrival_sequence_arrived_between
       Job (import_job_arrival Job arrivalR) j
       (instant_to_imported t1) (instant_to_imported t2)).
Proof.
  unfold prosa.behavior.arrival_sequence.arrived_between.
  unfold Prosa_Behavior_Arrival_sequence_arrived_between.
  cbv [import_job_arrival instant_to_imported
       Prosa_Behavior_Job_JobArrival_job_arrival
       LE_le_inst1 LT_lt_inst1 instLENat instLTNat].
  apply imported_bool_sprop_and_bridge.
  - exact (imported_nat_le_bridge t1
      (@prosa.behavior.job.job_arrival Job arrivalR j)).
  - exact (imported_nat_lt_bridge
      (@prosa.behavior.job.job_arrival Job arrivalR j) t2).
Qed.

Print Assumptions has_arrived_certificate.
Print Assumptions arrived_before_certificate.
Print Assumptions arrived_between_certificate.
