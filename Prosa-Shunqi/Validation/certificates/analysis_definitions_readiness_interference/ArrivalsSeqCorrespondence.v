(* Re-bound copy of accepted certificates/model_task_arrivals/ArrivalsSeqCorrespondence.v for the readiness_interference artifact;
   only the imported module name differs. *)
(* Re-bound copy of the accepted behavior/arrival_sequence ArrivalSequenceCorrespondence.v
   for the model/task/arrivals artifact; only module names differ. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import behavior.arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReadinessInterference
  ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ArrivalsSeqBaseAdapter
  ArrivalsSeqOperations.

(** Fourteen compositional certificates for the official v0.6 definitions
    and the actual imported production Lean bodies.  Related-input hypotheses
    are the representation relation's ordinary parameters; there is no
    declaration-specific semantic premise. *)

Lemma arrival_sequence_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T) :
  ArArrivalSequenceRel T arrR
    (ar_arrival_sequence_to_imported T arrR).
Proof. exact (ar_arrival_sequence_canonical T arrR). Qed.

Lemma arrivals_at_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) :
  ArArrivalSequenceRel T arrR arrL ->
  forall tR tL, SubNatRel tR tL ->
  ArListRel
    (prosa.behavior.arrival_sequence.arrivals_at arrR tR)
    (ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrivals_at T
      (ar_decidable_eq T) arrL tL).
Proof.
  intros Harr tR tL Ht. cbn.
  exact (Harr tR tL Ht).
Qed.

Lemma arrives_at_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) (j : T) :
  ArArrivalSequenceRel T arrR arrL ->
  forall tR tL, SubNatRel tR tL ->
  ArBoolRel
    (prosa.behavior.arrival_sequence.arrives_at arrR j tR)
    (ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrives_at T
      (ar_decidable_eq T) arrL j tL).
Proof.
  intros Harr tR tL Ht. cbn.
  apply ar_decide_mem_related.
  exact (Harr tR tL Ht).
Qed.

Lemma arrives_in_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) (j : T) :
  ArArrivalSequenceRel T arrR arrL ->
  PropSPropRel
    (prosa.behavior.arrival_sequence.arrives_in arrR j)
    (ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrives_in T
      (ar_decidable_eq T) arrL j).
Proof.
  intro Harr. cbn.
  apply ar_exists_nat_correspondence.
  intros tR tL Ht. apply ar_bool_truth_correspondence.
  exact (arrives_at_correspondence_certificate T arrR arrL j
    Harr tR tL Ht).
Qed.

Lemma consistent_arrival_times_correspondence_certificate (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T)
    (arrivalL : ImportedReadinessInterference.Prosa_Behavior_Job_JobArrival T
      (ar_decidable_eq T))
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) :
  ArJobArrivalRel T arrivalR arrivalL ->
  ArArrivalSequenceRel T arrR arrL ->
  PropSPropRel
    (@prosa.behavior.arrival_sequence.consistent_arrival_times T arrivalR arrR)
    (ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_consistent_arrival_times
      T (ar_decidable_eq T) arrivalL arrL).
Proof.
  intros Harrival Harr. cbn.
  apply ar_forall_identity_correspondence. intro j.
  apply ar_forall_nat_correspondence. intros tR tL Ht.
  apply ar_imp_correspondence.
  - apply ar_bool_truth_correspondence.
    exact (arrives_at_correspondence_certificate T arrR arrL j
      Harr tR tL Ht).
  - exact (sub_nat_eq_correspondence _ _ _ _ (Harrival j) Ht).
Qed.

Lemma arrival_sequence_uniq_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) :
  ArArrivalSequenceRel T arrR arrL ->
  PropSPropRel
    (prosa.behavior.arrival_sequence.arrival_sequence_uniq arrR)
    (ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq
      T (ar_decidable_eq T) arrL).
Proof.
  intro Harr. cbn.
  apply ar_forall_nat_correspondence. intros tR tL Ht.
  apply ar_uniq_correspondence.
  exact (Harr tR tL Ht).
Qed.

Lemma valid_arrival_sequence_correspondence_certificate (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T)
    (arrivalL : ImportedReadinessInterference.Prosa_Behavior_Job_JobArrival T
      (ar_decidable_eq T))
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) :
  ArJobArrivalRel T arrivalR arrivalL ->
  ArArrivalSequenceRel T arrR arrL ->
  PropSPropRel
    (@prosa.behavior.arrival_sequence.valid_arrival_sequence T arrivalR arrR)
    (ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_valid_arrival_sequence
      T (ar_decidable_eq T) arrivalL arrL).
Proof.
  intros Harrival Harr. cbn.
  apply ar_and_correspondence.
  - exact (consistent_arrival_times_correspondence_certificate
      T arrivalR arrivalL arrR arrL Harrival Harr).
  - exact (arrival_sequence_uniq_correspondence_certificate
      T arrR arrL Harr).
Qed.

Lemma has_arrived_correspondence_certificate (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T)
    (arrivalL : ImportedReadinessInterference.Prosa_Behavior_Job_JobArrival T
      (ar_decidable_eq T)) (j : T) :
  ArJobArrivalRel T arrivalR arrivalL ->
  forall tR tL, SubNatRel tR tL ->
  ArBoolRel
    (@prosa.behavior.arrival_sequence.has_arrived T arrivalR j tR)
    (ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_has_arrived T
      (ar_decidable_eq T) arrivalL j tL).
Proof.
  intros Harrival tR tL Ht. cbn.
  exact (ar_decide_le_related _ _ _ _ (Harrival j) Ht).
Qed.

Lemma arrived_before_correspondence_certificate (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T)
    (arrivalL : ImportedReadinessInterference.Prosa_Behavior_Job_JobArrival T
      (ar_decidable_eq T)) (j : T) :
  ArJobArrivalRel T arrivalR arrivalL ->
  forall tR tL, SubNatRel tR tL ->
  ArBoolRel
    (@prosa.behavior.arrival_sequence.arrived_before T arrivalR j tR)
    (ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrived_before T
      (ar_decidable_eq T) arrivalL j tL).
Proof.
  intros Harrival tR tL Ht. cbn.
  exact (ar_decide_lt_related _ _ _ _ (Harrival j) Ht).
Qed.

Lemma arrived_between_correspondence_certificate (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T)
    (arrivalL : ImportedReadinessInterference.Prosa_Behavior_Job_JobArrival T
      (ar_decidable_eq T)) (j : T) :
  ArJobArrivalRel T arrivalR arrivalL ->
  forall t1R t1L t2R t2L,
  SubNatRel t1R t1L -> SubNatRel t2R t2L ->
  ArBoolRel
    (@prosa.behavior.arrival_sequence.arrived_between
      T arrivalR j t1R t2R)
    (ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrived_between T
      (ar_decidable_eq T) arrivalL j t1L t2L).
Proof.
  intros Harrival t1R t1L t2R t2L Ht1 Ht2. cbn.
  apply ar_bool_and_related.
  - exact (ar_decide_le_related _ _ _ _ Ht1 (Harrival j)).
  - exact (ar_decide_lt_related _ _ _ _ (Harrival j) Ht2).
Qed.

Lemma arrivals_between_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) :
  ArArrivalSequenceRel T arrR arrL ->
  forall t1R t1L t2R t2L,
  SubNatRel t1R t1L -> SubNatRel t2R t2L ->
  ArListRel
    (prosa.behavior.arrival_sequence.arrivals_between arrR t1R t2R)
    (ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrivals_between T
      (ar_decidable_eq T) arrL t1L t2L).
Proof.
  intros Harr t1R t1L t2R t2L Ht1 Ht2. cbn.
  exact (ar_bigCatNat_related_any T arrR arrL
    t1R t2R t1L t2L Harr Ht1 Ht2).
Qed.

Lemma arrivals_up_to_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) :
  ArArrivalSequenceRel T arrR arrL ->
  forall tR tL, SubNatRel tR tL ->
  ArListRel
    (prosa.behavior.arrival_sequence.arrivals_up_to arrR tR)
    (ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrivals_up_to T
      (ar_decidable_eq T) arrL tL).
Proof.
  intros Harr tR tL Ht. cbn.
  apply (arrivals_between_correspondence_certificate T arrR arrL Harr
    0 Lean.Nat_zero tR.+1 (Lean.Nat_succ tL)).
  - exact (sub_nat_rel_canonical 0).
  - exact (sub_imported_eq_congr Lean.Nat_succ _ _ Ht).
Qed.

Lemma arrivals_before_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) :
  ArArrivalSequenceRel T arrR arrL ->
  forall tR tL, SubNatRel tR tL ->
  ArListRel
    (prosa.behavior.arrival_sequence.arrivals_before arrR tR)
    (ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrivals_before T
      (ar_decidable_eq T) arrL tL).
Proof.
  intros Harr tR tL Ht. cbn.
  exact (arrivals_between_correspondence_certificate T arrR arrL Harr
    0 Lean.Nat_zero tR tL (sub_nat_rel_canonical 0) Ht).
Qed.

Lemma arrivals_between_P_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T))
    (PR : T -> bool) (PL : T -> ImportedReadinessInterference.Bool) :
  ArArrivalSequenceRel T arrR arrL -> ArPredRel PR PL ->
  forall t1R t1L t2R t2L,
  SubNatRel t1R t1L -> SubNatRel t2R t2L ->
  ArListRel
    (prosa.behavior.arrival_sequence.arrivals_between_P arrR PR t1R t2R)
    (ImportedReadinessInterference.Prosa_Behavior_Arrival_sequence_arrivals_between_P
      T (ar_decidable_eq T) arrL PL t1L t2L).
Proof.
  intros Harr HP t1R t1L t2R t2L Ht1 Ht2. cbn.
  apply ar_filter_related; first exact HP.
  exact (arrivals_between_correspondence_certificate T arrR arrL Harr
    t1R t1L t2R t2L Ht1 Ht2).
Qed.

Print Assumptions arrival_sequence_correspondence_certificate.
Print Assumptions arrivals_at_correspondence_certificate.
Print Assumptions arrives_at_correspondence_certificate.
Print Assumptions arrives_in_correspondence_certificate.
Print Assumptions consistent_arrival_times_correspondence_certificate.
Print Assumptions arrival_sequence_uniq_correspondence_certificate.
Print Assumptions valid_arrival_sequence_correspondence_certificate.
Print Assumptions has_arrived_correspondence_certificate.
Print Assumptions arrived_before_correspondence_certificate.
Print Assumptions arrived_between_correspondence_certificate.
Print Assumptions arrivals_between_correspondence_certificate.
Print Assumptions arrivals_up_to_correspondence_certificate.
Print Assumptions arrivals_before_correspondence_certificate.
Print Assumptions arrivals_between_P_correspondence_certificate.
