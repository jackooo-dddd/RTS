(** GENERATED ARTIFACT-LOCAL INSTANTIATION.
    source: Validation/certificates/behavior_arrival_sequence/ArrivalSequenceCorrespondence.v
    source-sha256: 5b5f0de2cf8a7f00dbbd6809c8e96ef8ae0d368a0b87801f8a3657d9493ff453
    imported-artifact-sha256: ee9b3f089b6133c959d3a0ac3ff09f484b54386b18522f95fbbb9252363424c5 *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import behavior.arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedScheduledFull
  ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ReadyArrivalBaseAdapter
  ReadyArrivalOperations.

(** Fourteen compositional certificates for the official v0.6 definitions
    and the actual imported production Lean bodies.  Related-input hypotheses
    are the representation relation's ordinary parameters; there is no
    declaration-specific semantic premise. *)

Lemma arrivals_between_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedScheduledFull.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) :
  ArArrivalSequenceRel T arrR arrL ->
  forall t1R t1L t2R t2L,
  SubNatRel t1R t1L -> SubNatRel t2R t2L ->
  ArListRel
    (prosa.behavior.arrival_sequence.arrivals_between arrR t1R t2R)
    (ImportedScheduledFull.Prosa_Behavior_Arrival_sequence_arrivals_between T
      (ar_decidable_eq T) arrL t1L t2L).
Proof.
  intros Harr t1R t1L t2R t2L Ht1 Ht2. cbn.
  exact (ar_bigCatNat_related_any T arrR arrL
    t1R t2R t1L t2L Harr Ht1 Ht2).
Qed.

Lemma arrivals_up_to_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedScheduledFull.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) :
  ArArrivalSequenceRel T arrR arrL ->
  forall tR tL, SubNatRel tR tL ->
  ArListRel
    (prosa.behavior.arrival_sequence.arrivals_up_to arrR tR)
    (ImportedScheduledFull.Prosa_Behavior_Arrival_sequence_arrivals_up_to T
      (ar_decidable_eq T) arrL tL).
Proof.
  intros Harr tR tL Ht. cbn.
  apply (arrivals_between_correspondence_certificate T arrR arrL Harr
    0 Lean.Nat_zero tR.+1 (Lean.Nat_succ tL)).
  - exact (sub_nat_rel_canonical 0).
  - exact (sub_imported_eq_congr Lean.Nat_succ _ _ Ht).
Qed.

Print Assumptions arrivals_between_correspondence_certificate.
Print Assumptions arrivals_up_to_correspondence_certificate.
