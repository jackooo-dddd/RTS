From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From prosa Require Import model.priority.edf.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityEdf.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder
  PriorityCoercionCorrespondence.

Module I := ImportedPriorityEdf.

(** Certificates for [model/priority/edf.v]: the parameter class ([JobDeadline]) is related
    pointwise on Nat with two-way totals; the policy instance(s) are related
    as [PdJLFPRel] for related parameters; the reflexive/transitive/total
    statements: source side is the exact elaborated type of the pinned source
    lemma (via [type of], the source proof is not used), target side the type
    of the imported Lean theorem, related through the accepted
    [pd_*_priorities_certificate]s. *)

Ltac type_of_term t := let T := type of t in exact T.

Section Policy.
  Context (Job : eqType).
  Let dJ := pd_decidable_eq Job.
  Definition PpParamRel (cR : prosa.behavior.job.JobDeadline Job) (cL : I.Prosa_Behavior_Job_JobDeadline Job dJ) : SProp :=
    forall x : Job, SubNatRel (@prosa.behavior.job.job_deadline Job cR x) (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ cL x).
  Lemma JobDeadline_source_total cR : PpParamRel cR (I.Prosa_Behavior_Job_JobDeadline_mk Job dJ (fun x => sub_nat_to_imported (@prosa.behavior.job.job_deadline Job cR x))).
  Proof. intro x. exact (sub_nat_rel_canonical _). Qed.
  Lemma JobDeadline_target_total cL : PpParamRel (fun x => sub_nat_to_rocq (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ cL x)) cL.
  Proof. intro x. exact (sub_nat_rel_surjective _). Qed.

  Variable cR : prosa.behavior.job.JobDeadline Job.
  Variable cL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
  Hypothesis Hc : PpParamRel cR cL.

  Theorem EDF_correspondence :
    PdJLFPRel Job (@prosa.model.priority.edf.EDF Job cR) (I.Prosa_Model_Priority_Edf_EDF Job dJ cL).
  Proof. intros x y. exact (pd_decide_le_related _ _ _ _ (Hc x) (Hc y)). Qed.

  Definition src_EDF_is_reflexive : Prop := ltac:(type_of_term (@prosa.model.priority.edf.EDF_is_reflexive Job cR)).
  Definition tgt_EDF_is_reflexive : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_Edf_EDF_is_reflexive Job dJ cL)).
  Theorem EDF_is_reflexive_correspondence : PropSPropRel src_EDF_is_reflexive tgt_EDF_is_reflexive.
  Proof. exact (pd_reflexive_job_priorities_certificate Job _ _ EDF_correspondence). Qed.

  Definition src_EDF_is_transitive : Prop := ltac:(type_of_term (@prosa.model.priority.edf.EDF_is_transitive Job cR)).
  Definition tgt_EDF_is_transitive : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_Edf_EDF_is_transitive Job dJ cL)).
  Theorem EDF_is_transitive_correspondence : PropSPropRel src_EDF_is_transitive tgt_EDF_is_transitive.
  Proof. exact (pd_transitive_job_priorities_certificate Job _ _ EDF_correspondence). Qed.

  Definition src_EDF_is_total : Prop := ltac:(type_of_term (@prosa.model.priority.edf.EDF_is_total Job cR)).
  Definition tgt_EDF_is_total : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_Edf_EDF_is_total Job dJ cL)).
  Theorem EDF_is_total_correspondence : PropSPropRel src_EDF_is_total tgt_EDF_is_total.
  Proof. exact (pd_total_job_priorities_certificate Job _ _ EDF_correspondence). Qed.

End Policy.
