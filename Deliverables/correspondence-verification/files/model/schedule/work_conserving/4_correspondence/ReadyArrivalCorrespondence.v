(** GENERATED ARTIFACT-LOCAL INSTANTIATION.
    source: /Users/shunqiwang/CityuHK/Research/Lean/TranslationProof/Prosa-Shunqi/Validation/certificates/behavior_arrival_sequence/ArrivalSequenceCorrespondence.v
    source-sha256: 5b5f0de2cf8a7f00dbbd6809c8e96ef8ae0d368a0b87801f8a3657d9493ff453
    imported-artifact-sha256: 3952d4e1d2dc45e4d67bb664c9be76820ed73421d0e2483bc4dc66fb4feb7ac8 *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import behavior.arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedWorkConserving
  ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ReadyArrivalBaseAdapter
  ReadyArrivalOperations.

(** Fourteen compositional certificates for the official v0.6 definitions
    and the actual imported production Lean bodies.  Related-input hypotheses
    are the representation relation's ordinary parameters; there is no
    declaration-specific semantic premise. *)

Lemma arrivals_at_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedWorkConserving.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) :
  ArArrivalSequenceRel T arrR arrL ->
  forall tR tL, SubNatRel tR tL ->
  ArListRel
    (prosa.behavior.arrival_sequence.arrivals_at arrR tR)
    (ImportedWorkConserving.Prosa_Behavior_Arrival_sequence_arrivals_at T
      (ar_decidable_eq T) arrL tL).
Proof.
  intros Harr tR tL Ht. cbn.
  exact (Harr tR tL Ht).
Qed.

Lemma arrives_at_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedWorkConserving.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) (j : T) :
  ArArrivalSequenceRel T arrR arrL ->
  forall tR tL, SubNatRel tR tL ->
  ArBoolRel
    (prosa.behavior.arrival_sequence.arrives_at arrR j tR)
    (ImportedWorkConserving.Prosa_Behavior_Arrival_sequence_arrives_at T
      (ar_decidable_eq T) arrL j tL).
Proof.
  intros Harr tR tL Ht. cbn.
  apply ar_decide_mem_related.
  exact (Harr tR tL Ht).
Qed.

Lemma arrives_in_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedWorkConserving.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) (j : T) :
  ArArrivalSequenceRel T arrR arrL ->
  PropSPropRel
    (prosa.behavior.arrival_sequence.arrives_in arrR j)
    (ImportedWorkConserving.Prosa_Behavior_Arrival_sequence_arrives_in T
      (ar_decidable_eq T) arrL j).
Proof.
  intro Harr. cbn.
  apply ar_exists_nat_correspondence.
  intros tR tL Ht. apply ar_bool_truth_correspondence.
  exact (arrives_at_correspondence_certificate T arrR arrL j
    Harr tR tL Ht).
Qed.

Lemma arrivals_between_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedWorkConserving.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) :
  ArArrivalSequenceRel T arrR arrL ->
  forall t1R t1L t2R t2L,
  SubNatRel t1R t1L -> SubNatRel t2R t2L ->
  ArListRel
    (prosa.behavior.arrival_sequence.arrivals_between arrR t1R t2R)
    (ImportedWorkConserving.Prosa_Behavior_Arrival_sequence_arrivals_between T
      (ar_decidable_eq T) arrL t1L t2L).
Proof.
  intros Harr t1R t1L t2R t2L Ht1 Ht2. cbn.
  exact (ar_bigCatNat_related_any T arrR arrL
    t1R t2R t1L t2L Harr Ht1 Ht2).
Qed.

Lemma arrivals_up_to_correspondence_certificate (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedWorkConserving.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) :
  ArArrivalSequenceRel T arrR arrL ->
  forall tR tL, SubNatRel tR tL ->
  ArListRel
    (prosa.behavior.arrival_sequence.arrivals_up_to arrR tR)
    (ImportedWorkConserving.Prosa_Behavior_Arrival_sequence_arrivals_up_to T
      (ar_decidable_eq T) arrL tL).
Proof.
  intros Harr tR tL Ht. cbn.
  apply (arrivals_between_correspondence_certificate T arrR arrL Harr
    0 Lean.Nat_zero tR.+1 (Lean.Nat_succ tL)).
  - exact (sub_nat_rel_canonical 0).
  - exact (sub_imported_eq_congr Lean.Nat_succ _ _ Ht).
Qed.

Print Assumptions arrivals_at_correspondence_certificate.
Print Assumptions arrives_at_correspondence_certificate.
Print Assumptions arrives_in_correspondence_certificate.
Print Assumptions arrivals_between_correspondence_certificate.
Print Assumptions arrivals_up_to_correspondence_certificate.
