From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From prosa Require Import FactsSbfAverageSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsSbfAverage ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalSequenceBaseAdapter ArrivalSequenceOperations ArrivalSequenceCorrespondence
  SupplyBaseAdapter SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations
  SupplyScheduleOperations SupplyNatBoolOperations SupplyIntervalOperations
  SupplyCorrespondence PredCorrespondence PlainCorrespondence
  NatSubCorrespondence DivModCorrespondence AverageCorrespondence.

Module I := ImportedFactsSbfAverage.
Module S := FactsSbfAverageSemanticSource.FactsSbfAverageSemanticSource.

(** Statement correspondences for [analysis/facts/model/sbf/average.v].

    Source side: the extracted statement [S.statement_X] specialised at its
    input binders (job type, processor state, arrival sequence, schedule and
    the three model parameters [Π Θ ν]); target side: the type of the
    imported Lean theorem.  Inputs: the model parameters by [SubNatRel], the
    processor state and schedule by the accepted [SupplyProcessorStateRel] /
    [SupplyScheduleRel], and arrival sequences by [ArArrivalSequenceRel].
    [arm_sbf] is related pointwise by the accepted DivMod-based
    [arm_sbf_correspondence]; the predicates are closed by the accepted
    pred/plain/average definition correspondences. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section ArmSbf.
  Variables (periodR allocR delayR : nat) (periodL allocL delayL : Lean.Nat).
  Hypothesis Hperiod : SubNatRel periodR periodL.
  Hypothesis Halloc : SubNatRel allocR allocL.
  Hypothesis Hdelay : SubNatRel delayR delayL.

  Lemma fsa_arm_sbf_related :
    PredFunctionRel
      (prosa.analysis.definitions.sbf.average.arm_sbf periodR allocR delayR)
      (I.Prosa_Analysis_Definitions_Sbf_Average_arm_sbf periodL allocL delayL).
  Proof.
    intros nR nL Hn.
    exact (arm_sbf_correspondence _ _ _ _ _ _ _ _ Hperiod Halloc Hdelay Hn).
  Qed.

  Definition src_arm_sbf_monotone : Prop :=
    ltac:(body_of (fun s : S.statement_arm_sbf_monotone => s periodR allocR delayR)).
  Definition tgt_arm_sbf_monotone : SProp :=
    ltac:(type_of_term (I.Prosa_Analysis_Facts_Model_Sbf_Average_arm_sbf_monotone
      periodL allocL delayL)).

  Theorem arm_sbf_monotone_correspondence :
    PropSPropRel src_arm_sbf_monotone tgt_arm_sbf_monotone.
  Proof.
    exact (pred_sbf_is_monotone_correspondence _ _ fsa_arm_sbf_related).
  Qed.

  Section Schedule.
    Context (Job : eqType).
    Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
    Variable PStateL :
      I.Prosa_Behavior_Schedule_ProcessorState Job (sch_decidable_eq Job).
    Variable Rstate : SupplyProcessorStateRel Job PStateR PStateL.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job
      (sch_decidable_eq Job) PStateL.
    Hypothesis Hsched :
      SupplyScheduleRel Job PStateR PStateL Rstate schedR schedL.

    Let MODEL := average_resource_model_correspondence Job PStateR PStateL Rstate
      schedR schedL Hsched periodR allocR delayR periodL allocL delayL
      Hperiod Halloc Hdelay.

    Definition src_arm_sbf_unit : Prop :=
      ltac:(body_of (fun s : S.statement_arm_sbf_unit =>
        s Job PStateR schedR periodR allocR delayR)).
    Definition tgt_arm_sbf_unit : SProp :=
      ltac:(type_of_term (I.Prosa_Analysis_Facts_Model_Sbf_Average_arm_sbf_unit
        Job (sch_decidable_eq Job) PStateL schedL periodL allocL delayL)).

    Theorem arm_sbf_unit_correspondence :
      PropSPropRel src_arm_sbf_unit tgt_arm_sbf_unit.
    Proof.
      apply ar_imp_correspondence; [exact MODEL|].
      exact (pred_unit_supply_bound_function_correspondence _ _ fsa_arm_sbf_related).
    Qed.

    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job (ar_decidable_eq Job).
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Definition src_arm_sbf_valid : Prop :=
      ltac:(body_of (fun s : S.statement_arm_sbf_valid =>
        s Job PStateR arrR schedR periodR allocR delayR)).
    Definition tgt_arm_sbf_valid : SProp :=
      ltac:(type_of_term (I.Prosa_Analysis_Facts_Model_Sbf_Average_arm_sbf_valid
        Job (sch_decidable_eq Job) PStateL arrL schedL periodL allocL delayL)).

    Theorem arm_sbf_valid_correspondence :
      PropSPropRel src_arm_sbf_valid tgt_arm_sbf_valid.
    Proof.
      apply ar_imp_correspondence; [exact MODEL|].
      exact (plain_valid_supply_bound_function_correspondence Job PStateR PStateL
        Rstate schedR schedL Hsched arrR arrL Harr _ _ fsa_arm_sbf_related).
    Qed.
  End Schedule.
End ArmSbf.
