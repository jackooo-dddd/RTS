(** GENERATED ARTIFACT-LOCAL INSTANTIATION.
    source: /Users/shunqiwang/CityuHK/Research/Lean/TranslationProof/Prosa-Shunqi/Validation/certificates/behavior_arrival_sequence/ArrivalSequenceCorrespondence.v
    source-sha256: 5b5f0de2cf8a7f00dbbd6809c8e96ef8ae0d368a0b87801f8a3657d9493ff453
    imported-artifact-sha256: 83ce15ec777b3ecaf9444952d0e3f31ed4f667f5b9fb4b93736302a524a7b210 *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import behavior.arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReady
  ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ReadyArrivalBaseAdapter
  ReadyArrivalOperations.

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
      ImportedReady.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) :
  ArArrivalSequenceRel T arrR arrL ->
  forall tR tL, SubNatRel tR tL ->
  ArListRel
    (prosa.behavior.arrival_sequence.arrivals_at arrR tR)
    (ImportedReady.Prosa_Behavior_Arrival_sequence_arrivals_at T
      (ar_decidable_eq T) arrL tL).
Proof.
  intros Harr tR tL Ht. cbn.
  exact (Harr tR tL Ht).
Qed.

Lemma arrives_at_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedReady.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) (j : T) :
  ArArrivalSequenceRel T arrR arrL ->
  forall tR tL, SubNatRel tR tL ->
  ArBoolRel
    (prosa.behavior.arrival_sequence.arrives_at arrR j tR)
    (ImportedReady.Prosa_Behavior_Arrival_sequence_arrives_at T
      (ar_decidable_eq T) arrL j tL).
Proof.
  intros Harr tR tL Ht. cbn.
  apply ar_decide_mem_related.
  exact (Harr tR tL Ht).
Qed.

Lemma arrives_in_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedReady.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) (j : T) :
  ArArrivalSequenceRel T arrR arrL ->
  PropSPropRel
    (prosa.behavior.arrival_sequence.arrives_in arrR j)
    (ImportedReady.Prosa_Behavior_Arrival_sequence_arrives_in T
      (ar_decidable_eq T) arrL j).
Proof.
  intro Harr. cbn.
  apply ar_exists_nat_correspondence.
  intros tR tL Ht. apply ar_bool_truth_correspondence.
  exact (arrives_at_correspondence_certificate T arrR arrL j
    Harr tR tL Ht).
Qed.

Lemma has_arrived_correspondence_certificate (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T)
    (arrivalL : ImportedReady.Prosa_Behavior_Job_JobArrival T
      (ar_decidable_eq T)) (j : T) :
  ArJobArrivalRel T arrivalR arrivalL ->
  forall tR tL, SubNatRel tR tL ->
  ArBoolRel
    (@prosa.behavior.arrival_sequence.has_arrived T arrivalR j tR)
    (ImportedReady.Prosa_Behavior_Arrival_sequence_has_arrived T
      (ar_decidable_eq T) arrivalL j tL).
Proof.
  intros Harrival tR tL Ht. cbn.
  exact (ar_decide_le_related _ _ _ _ (Harrival j) Ht).
Qed.

Print Assumptions arrival_sequence_correspondence_certificate.
Print Assumptions arrivals_at_correspondence_certificate.
Print Assumptions arrives_at_correspondence_certificate.
Print Assumptions arrives_in_correspondence_certificate.
Print Assumptions has_arrived_correspondence_certificate.
