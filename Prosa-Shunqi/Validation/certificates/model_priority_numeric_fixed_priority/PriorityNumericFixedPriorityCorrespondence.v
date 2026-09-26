From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From prosa Require Import model.priority.numeric_fixed_priority.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityNumericFixedPriority.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder
  PriorityCoercionCorrespondence.

Module I := ImportedPriorityNumericFixedPriority.

(** Certificates for [model/priority/numeric_fixed_priority.v]: the parameter class ([TaskPriority]) is related
    pointwise on Nat with two-way totals; the policy instance(s) are related
    as [PdFPRel] for related parameters; the reflexive/transitive/total
    statements: source side is the exact elaborated type of the pinned source
    lemma (via [type of], the source proof is not used), target side the type
    of the imported Lean theorem, related through the accepted
    [pd_*_priorities_certificate]s. *)

Ltac type_of_term t := let T := type of t in exact T.

Lemma pp_decide_ge_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PdBoolRel (aR >= bR) (I.Decidable_decide (I.GE_ge_inst1 Lean.Nat I.instLENat aL bL)
    (I.Nat_decLe bL aL)).
Proof. intros Ha Hb. exact (pd_decide_le_related _ _ _ _ Hb Ha). Qed.

Section Policy.
  Context (Task : eqType).
  Let dT := pd_decidable_eq Task.
  Definition PpParamRel (cR : prosa.model.priority.numeric_fixed_priority.TaskPriority Task) (cL : I.Prosa_Model_Priority_NumericFixedPriority_TaskPriority Task dT) : SProp :=
    forall x : Task, SubNatRel (@prosa.model.priority.numeric_fixed_priority.task_priority Task cR x) (I.Prosa_Model_Priority_NumericFixedPriority_TaskPriority_task_priority Task dT cL x).
  Lemma TaskPriority_source_total cR : PpParamRel cR (I.Prosa_Model_Priority_NumericFixedPriority_TaskPriority_mk Task dT (fun x => sub_nat_to_imported (@prosa.model.priority.numeric_fixed_priority.task_priority Task cR x))).
  Proof. intro x. exact (sub_nat_rel_canonical _). Qed.
  Lemma TaskPriority_target_total cL : PpParamRel (fun x => sub_nat_to_rocq (I.Prosa_Model_Priority_NumericFixedPriority_TaskPriority_task_priority Task dT cL x)) cL.
  Proof. intro x. exact (sub_nat_rel_surjective _). Qed.

  Variable cR : prosa.model.priority.numeric_fixed_priority.TaskPriority Task.
  Variable cL : I.Prosa_Model_Priority_NumericFixedPriority_TaskPriority Task dT.
  Hypothesis Hc : PpParamRel cR cL.

  Theorem NumericFPAscending_correspondence :
    PdFPRel Task (@prosa.model.priority.numeric_fixed_priority.NumericFPAscending Task cR) (I.Prosa_Model_Priority_NumericFixedPriority_NumericFPAscending Task dT cL).
  Proof. intros x y. exact (pp_decide_ge_related _ _ _ _ (Hc x) (Hc y)). Qed.

  Definition src_NFPA_is_reflexive : Prop := ltac:(type_of_term (@prosa.model.priority.numeric_fixed_priority.NFPA_is_reflexive Task cR)).
  Definition tgt_NFPA_is_reflexive : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_NumericFixedPriority_NFPA_is_reflexive Task dT cL)).
  Theorem NFPA_is_reflexive_correspondence : PropSPropRel src_NFPA_is_reflexive tgt_NFPA_is_reflexive.
  Proof. exact (pd_reflexive_task_priorities_certificate Task _ _ NumericFPAscending_correspondence). Qed.

  Definition src_NFPA_is_transitive : Prop := ltac:(type_of_term (@prosa.model.priority.numeric_fixed_priority.NFPA_is_transitive Task cR)).
  Definition tgt_NFPA_is_transitive : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_NumericFixedPriority_NFPA_is_transitive Task dT cL)).
  Theorem NFPA_is_transitive_correspondence : PropSPropRel src_NFPA_is_transitive tgt_NFPA_is_transitive.
  Proof. exact (pd_transitive_task_priorities_certificate Task _ _ NumericFPAscending_correspondence). Qed.

  Definition src_NFPA_is_total : Prop := ltac:(type_of_term (@prosa.model.priority.numeric_fixed_priority.NFPA_is_total Task cR)).
  Definition tgt_NFPA_is_total : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_NumericFixedPriority_NFPA_is_total Task dT cL)).
  Theorem NFPA_is_total_correspondence : PropSPropRel src_NFPA_is_total tgt_NFPA_is_total.
  Proof. exact (pd_total_task_priorities_certificate Task _ _ NumericFPAscending_correspondence). Qed.

  Theorem NumericFPDescending_correspondence :
    PdFPRel Task (@prosa.model.priority.numeric_fixed_priority.NumericFPDescending Task cR) (I.Prosa_Model_Priority_NumericFixedPriority_NumericFPDescending Task dT cL).
  Proof. intros x y. exact (pd_decide_le_related _ _ _ _ (Hc x) (Hc y)). Qed.

  Definition src_NFPD_is_reflexive : Prop := ltac:(type_of_term (@prosa.model.priority.numeric_fixed_priority.NFPD_is_reflexive Task cR)).
  Definition tgt_NFPD_is_reflexive : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_NumericFixedPriority_NFPD_is_reflexive Task dT cL)).
  Theorem NFPD_is_reflexive_correspondence : PropSPropRel src_NFPD_is_reflexive tgt_NFPD_is_reflexive.
  Proof. exact (pd_reflexive_task_priorities_certificate Task _ _ NumericFPDescending_correspondence). Qed.

  Definition src_NFPD_is_transitive : Prop := ltac:(type_of_term (@prosa.model.priority.numeric_fixed_priority.NFPD_is_transitive Task cR)).
  Definition tgt_NFPD_is_transitive : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_NumericFixedPriority_NFPD_is_transitive Task dT cL)).
  Theorem NFPD_is_transitive_correspondence : PropSPropRel src_NFPD_is_transitive tgt_NFPD_is_transitive.
  Proof. exact (pd_transitive_task_priorities_certificate Task _ _ NumericFPDescending_correspondence). Qed.

  Definition src_NFPD_is_total : Prop := ltac:(type_of_term (@prosa.model.priority.numeric_fixed_priority.NFPD_is_total Task cR)).
  Definition tgt_NFPD_is_total : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_NumericFixedPriority_NFPD_is_total Task dT cL)).
  Theorem NFPD_is_total_correspondence : PropSPropRel src_NFPD_is_total tgt_NFPD_is_total.
  Proof. exact (pd_total_task_priorities_certificate Task _ _ NumericFPDescending_correspondence). Qed.

End Policy.
