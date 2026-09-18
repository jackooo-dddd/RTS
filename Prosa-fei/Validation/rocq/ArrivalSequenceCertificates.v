From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From prosa Require Import behavior.arrival_sequence.
From LeanImport Require Import Lean.
Require Import ImportedEasy93 ImportedNatBridge TimeJobCertificates.
Require Import EqTypeBridge ImportedListBridge.

Definition import_arrival_sequence (Job : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job) :
    Prosa_Behavior_Arrival_sequence_arrival_sequence Job :=
  fun tL => seq_to_imported_list (arrR (imported_nat_to_rocq tL)).

Lemma arrival_sequence_pointwise_certificate (Job : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job)
    (t : prosa.behavior.time.instant) :
  ImportedListRel
    (arrR t)
    (import_arrival_sequence Job arrR (instant_to_imported t)).
Proof.
  unfold ImportedListRel, import_arrival_sequence, instant_to_imported.
  apply imported_list_congr_of_seq_eq.
  apply f_equal.
  exact (Logic.eq_sym (rocq_nat_roundtrip t)).
Qed.

Lemma arrivals_at_certificate (Job : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job)
    (t : prosa.behavior.time.instant) :
  ImportedListRel
    (prosa.behavior.arrival_sequence.arrivals_at arrR t)
    (Prosa_Behavior_Arrival_sequence_arrivals_at
       Job (import_arrival_sequence Job arrR) (instant_to_imported t)).
Proof. exact (arrival_sequence_pointwise_certificate Job arrR t). Qed.

Lemma arrives_at_certificate (Job : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job)
    (j : Job) (t : prosa.behavior.time.instant) :
  ImportedBoolSPropRel
    (prosa.behavior.arrival_sequence.arrives_at arrR j t)
    (Prosa_Behavior_Arrival_sequence_arrives_at
       Job (import_arrival_sequence Job arrR) j (instant_to_imported t)).
Proof.
  unfold prosa.behavior.arrival_sequence.arrives_at.
  unfold prosa.behavior.arrival_sequence.arrivals_at.
  unfold Prosa_Behavior_Arrival_sequence_arrives_at.
  unfold Prosa_Behavior_Arrival_sequence_arrivals_at.
  cbn [Membership_mem_inst3 List_instMembership_inst1].
  apply seq_membership_related_bridge.
  exact (arrival_sequence_pointwise_certificate Job arrR t).
Qed.

Print Assumptions arrival_sequence_pointwise_certificate.
Print Assumptions arrivals_at_certificate.
Print Assumptions arrives_at_certificate.
