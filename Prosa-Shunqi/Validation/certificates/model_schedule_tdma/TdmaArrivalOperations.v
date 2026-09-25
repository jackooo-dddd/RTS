From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.schedule.tdma.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTdmaProjectedFull.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  TdmaBaseAdapter TdmaArithmeticAdapter.

(** Pointwise relation for the already accepted ArrivalSequence dependency. *)
Definition TdmaArrivalSequenceRel (Job : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job)
    (arrL : ImportedTdmaProjectedFull.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job (ar_decidable_eq Job)) : SProp :=
  forall tR tL, SubNatRel tR tL ->
    ArListRel (@prosa.behavior.arrival_sequence.arrivals_at Job arrR tR)
      (ImportedTdmaProjectedFull.Prosa_Behavior_Arrival_sequence_arrivals_at
        Job (ar_decidable_eq Job) arrL tL).

Definition tdma_arrival_sequence_to_target (Job : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job) :
    ImportedTdmaProjectedFull.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job (ar_decidable_eq Job) :=
  fun tL => ar_list_to_imported (arrR (sub_nat_to_rocq tL)).

Lemma tdma_arrival_sequence_source_total (Job : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job) :
  TdmaArrivalSequenceRel Job arrR
    (tdma_arrival_sequence_to_target Job arrR).
Proof.
  intros tR tL Ht. unfold TdmaArrivalSequenceRel in *.
  unfold ArListRel, tdma_arrival_sequence_to_target.
  destruct Ht.
  cbn [ImportedTdmaProjectedFull.Prosa_Behavior_Arrival_sequence_arrivals_at].
  pose proof (sub_nat_rocq_roundtrip tR) as Hround.
  destruct Hround.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma tdma_exists_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL ->
    PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (exists nR, PR nR)
    (ImportedTdmaProjectedFull.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [nR Hn].
    exact (ImportedTdmaProjectedFull.Exists_intro Lean.Nat PL
      (sub_nat_to_imported nR)
      (prop_to_sprop _ _
        (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) Hn)).
  - intros [nL Hn]. apply strictly_inhabits.
    exists (sub_nat_to_rocq nL).
    exact (sprop_to_prop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL)) Hn).
Qed.

Section ArrivalObservations.
  Context (Job : eqType).
  Context (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job).
  Context (arrL : ImportedTdmaProjectedFull.Prosa_Behavior_Arrival_sequence_arrival_sequence
    Job (ar_decidable_eq Job)).
  Context (Harr : TdmaArrivalSequenceRel Job arrR arrL).

  Lemma tdma_arrives_at_bool_related (j : Job) tR tL :
    SubNatRel tR tL ->
    ArBoolRel
      (@prosa.behavior.arrival_sequence.arrives_at Job arrR j tR)
      (ImportedTdmaProjectedFull.Prosa_Behavior_Arrival_sequence_arrives_at
        Job (ar_decidable_eq Job) arrL j tL).
  Proof.
    intro Ht.
    change (ArBoolRel
      (j \in @prosa.behavior.arrival_sequence.arrivals_at Job arrR tR)
      (ImportedTdmaProjectedFull.Decidable_decide
        (ar_target_mem j
          (ImportedTdmaProjectedFull.Prosa_Behavior_Arrival_sequence_arrivals_at
            Job (ar_decidable_eq Job) arrL tL))
        (ImportedTdmaProjectedFull.List_instDecidableMemOfLawfulBEq
          Job
          (ImportedTdmaProjectedFull.instBEqOfDecidableEq
            Job (ar_decidable_eq Job))
          (ImportedTdmaProjectedFull.instLawfulBEq
            Job (ar_decidable_eq Job))
          j
          (ImportedTdmaProjectedFull.Prosa_Behavior_Arrival_sequence_arrivals_at
            Job (ar_decidable_eq Job) arrL tL)))).
    apply tdma_decide_bool_related.
    exact (ar_membership_correspondence Job j _ _ (Harr tR tL Ht)).
  Qed.

  Theorem tdma_arrives_in_related (j : Job) :
    PropSPropRel
      (@prosa.behavior.arrival_sequence.arrives_in Job arrR j)
      (ImportedTdmaProjectedFull.Prosa_Behavior_Arrival_sequence_arrives_in
        Job (ar_decidable_eq Job) arrL j).
  Proof.
    change (PropSPropRel
      (exists tR : nat,
        is_true (@prosa.behavior.arrival_sequence.arrives_at
          Job arrR j tR))
      (ImportedTdmaProjectedFull.Exists Lean.Nat
        (fun tL => Lean.eq
          (ImportedTdmaProjectedFull.Prosa_Behavior_Arrival_sequence_arrives_at
            Job (ar_decidable_eq Job) arrL j tL)
          ImportedTdmaProjectedFull.Bool_true))).
    apply tdma_exists_nat_correspondence.
    intros tR tL Ht.
    exact (ar_bool_truth_correspondence _ _
      (tdma_arrives_at_bool_related j tR tL Ht)).
  Qed.
End ArrivalObservations.

Print Assumptions tdma_arrival_sequence_source_total.
Print Assumptions tdma_arrives_at_bool_related.
Print Assumptions tdma_arrives_in_related.
