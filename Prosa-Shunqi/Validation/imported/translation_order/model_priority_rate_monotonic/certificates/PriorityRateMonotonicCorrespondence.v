From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From prosa Require Import model.priority.rate_monotonic.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityRateMonotonic.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder
  PriorityCoercionCorrespondence.

Module I := ImportedPriorityRateMonotonic.

(** Certificates for [model/priority/rate_monotonic.v]: the parameter class ([SporadicModel]) is related
    pointwise on Nat with two-way totals; the policy instance(s) are related
    as [PdFPRel] for related parameters; the reflexive/transitive/total
    statements: source side is the exact elaborated type of the pinned source
    lemma (via [type of], the source proof is not used), target side the type
    of the imported Lean theorem, related through the accepted
    [pd_*_priorities_certificate]s. *)

Ltac type_of_term t := let T := type of t in exact T.

Section Policy.
  Context (Task : eqType).
  Let dT := pd_decidable_eq Task.
  Definition PpParamRel (cR : prosa.model.task.arrival.sporadic.SporadicModel Task) (cL : I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task dT) : SProp :=
    forall x : Task, SubNatRel (@prosa.model.task.arrival.sporadic.task_min_inter_arrival_time Task cR x) (I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time Task dT cL x).
  Lemma SporadicModel_source_total cR : PpParamRel cR (I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel_mk Task dT (fun x => sub_nat_to_imported (@prosa.model.task.arrival.sporadic.task_min_inter_arrival_time Task cR x))).
  Proof. intro x. exact (sub_nat_rel_canonical _). Qed.
  Lemma SporadicModel_target_total cL : PpParamRel (fun x => sub_nat_to_rocq (I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time Task dT cL x)) cL.
  Proof. intro x. exact (sub_nat_rel_surjective _). Qed.

  Variable cR : prosa.model.task.arrival.sporadic.SporadicModel Task.
  Variable cL : I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task dT.
  Hypothesis Hc : PpParamRel cR cL.

  Theorem RM_correspondence :
    PdFPRel Task (@prosa.model.priority.rate_monotonic.RM Task cR) (I.Prosa_Model_Priority_RateMonotonic_RM Task dT cL).
  Proof. intros x y. exact (pd_decide_le_related _ _ _ _ (Hc x) (Hc y)). Qed.

  Definition src_RM_is_reflexive : Prop := ltac:(type_of_term (@prosa.model.priority.rate_monotonic.RM_is_reflexive Task cR)).
  Definition tgt_RM_is_reflexive : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_RateMonotonic_RM_is_reflexive Task dT cL)).
  Theorem RM_is_reflexive_correspondence : PropSPropRel src_RM_is_reflexive tgt_RM_is_reflexive.
  Proof. exact (pd_reflexive_task_priorities_certificate Task _ _ RM_correspondence). Qed.

  Definition src_RM_is_transitive : Prop := ltac:(type_of_term (@prosa.model.priority.rate_monotonic.RM_is_transitive Task cR)).
  Definition tgt_RM_is_transitive : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_RateMonotonic_RM_is_transitive Task dT cL)).
  Theorem RM_is_transitive_correspondence : PropSPropRel src_RM_is_transitive tgt_RM_is_transitive.
  Proof. exact (pd_transitive_task_priorities_certificate Task _ _ RM_correspondence). Qed.

  Definition src_RM_is_total : Prop := ltac:(type_of_term (@prosa.model.priority.rate_monotonic.RM_is_total Task cR)).
  Definition tgt_RM_is_total : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_RateMonotonic_RM_is_total Task dT cL)).
  Theorem RM_is_total_correspondence : PropSPropRel src_RM_is_total tgt_RM_is_total.
  Proof. exact (pd_total_task_priorities_certificate Task _ _ RM_correspondence). Qed.

End Policy.
