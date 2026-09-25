From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import behavior.arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedAbstractDefinitions ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  AbstractDefinitionsBaseAdapter ServiceNatBoolOperations.

(** Reinstantiation of the accepted ArrivalSequence operation pattern in the
    present actual imported module; no cross-artifact definitional equality
    or unproved semantic premise is assumed. *)
Definition AdArrivalSequenceRel (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL : ImportedAbstractDefinitions.Prosa_Behavior_Arrival_sequence_arrival_sequence
      T (ad_decidable_eq T)) : SProp :=
  forall tR tL, SubNatRel tR tL -> AdListRel (arrR tR) (arrL tL).

Lemma ad_arrives_at_related (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL : ImportedAbstractDefinitions.Prosa_Behavior_Arrival_sequence_arrival_sequence
      T (ad_decidable_eq T)) (j : T) :
  AdArrivalSequenceRel T arrR arrL ->
  forall tR tL, SubNatRel tR tL ->
  AdBoolRel (prosa.behavior.arrival_sequence.arrives_at arrR j tR)
    (ImportedAbstractDefinitions.Prosa_Behavior_Arrival_sequence_arrives_at
      T (ad_decidable_eq T) arrL j tL).
Proof.
  intros Harr tR tL Ht.
  cbn [prosa.behavior.arrival_sequence.arrives_at
    prosa.behavior.arrival_sequence.arrivals_at
    ImportedAbstractDefinitions.Prosa_Behavior_Arrival_sequence_arrives_at
    ImportedAbstractDefinitions.Prosa_Behavior_Arrival_sequence_arrivals_at].
  apply svc_decide_bool_correspondence.
  exact (ad_membership_correspondence T j (arrR tR) (arrL tL)
    (Harr tR tL Ht)).
Qed.

Lemma ad_exists_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall tR tL, SubNatRel tR tL -> PropSPropRel (PR tR) (PL tL)) ->
  PropSPropRel (exists tR, PR tR)
    (ImportedAbstractDefinitions.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [tR Ht].
    exact (ImportedAbstractDefinitions.Exists_intro Lean.Nat PL
      (sub_nat_to_imported tR)
      (prop_to_sprop _ _
        (HP tR (sub_nat_to_imported tR) (sub_nat_rel_canonical tR)) Ht)).
  - intros [tL Ht]. apply strictly_inhabits.
    exists (sub_nat_to_rocq tL).
    exact (sprop_to_prop _ _
      (HP (sub_nat_to_rocq tL) tL (sub_nat_rel_surjective tL)) Ht).
Qed.

Lemma ad_arrives_in_related (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL : ImportedAbstractDefinitions.Prosa_Behavior_Arrival_sequence_arrival_sequence
      T (ad_decidable_eq T)) (j : T) :
  AdArrivalSequenceRel T arrR arrL ->
  PropSPropRel (prosa.behavior.arrival_sequence.arrives_in arrR j)
    (ImportedAbstractDefinitions.Prosa_Behavior_Arrival_sequence_arrives_in
      T (ad_decidable_eq T) arrL j).
Proof.
  intro Harr.
  cbn [prosa.behavior.arrival_sequence.arrives_in
    ImportedAbstractDefinitions.Prosa_Behavior_Arrival_sequence_arrives_in].
  apply ad_exists_nat_correspondence. intros tR tL Ht.
  apply ad_bool_truth_correspondence.
  exact (ad_arrives_at_related T arrR arrL j Harr tR tL Ht).
Qed.

Print Assumptions ad_arrives_at_related.
Print Assumptions ad_arrives_in_related.
