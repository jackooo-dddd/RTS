From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From prosa Require Import model.priority.fifo.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityFifo.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder
  PriorityCoercionCorrespondence.

Module I := ImportedPriorityFifo.

(** Certificates for [model/priority/fifo.v]: the parameter class ([JobArrival]) is related
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
  Definition PpParamRel (cR : prosa.behavior.job.JobArrival Job) (cL : I.Prosa_Behavior_Job_JobArrival Job dJ) : SProp :=
    forall x : Job, SubNatRel (@prosa.behavior.job.job_arrival Job cR x) (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ cL x).
  Lemma JobArrival_source_total cR : PpParamRel cR (I.Prosa_Behavior_Job_JobArrival_mk Job dJ (fun x => sub_nat_to_imported (@prosa.behavior.job.job_arrival Job cR x))).
  Proof. intro x. exact (sub_nat_rel_canonical _). Qed.
  Lemma JobArrival_target_total cL : PpParamRel (fun x => sub_nat_to_rocq (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ cL x)) cL.
  Proof. intro x. exact (sub_nat_rel_surjective _). Qed.

  Variable cR : prosa.behavior.job.JobArrival Job.
  Variable cL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hc : PpParamRel cR cL.

  Theorem FIFO_correspondence :
    PdJLFPRel Job (@prosa.model.priority.fifo.FIFO Job cR) (I.Prosa_Model_Priority_Fifo_FIFO Job dJ cL).
  Proof. intros x y. exact (pd_decide_le_related _ _ _ _ (Hc x) (Hc y)). Qed.

  Definition src_FIFO_is_reflexive : Prop := ltac:(type_of_term (@prosa.model.priority.fifo.FIFO_is_reflexive Job cR)).
  Definition tgt_FIFO_is_reflexive : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_Fifo_FIFO_is_reflexive Job dJ cL)).
  Theorem FIFO_is_reflexive_correspondence : PropSPropRel src_FIFO_is_reflexive tgt_FIFO_is_reflexive.
  Proof. exact (pd_reflexive_job_priorities_certificate Job _ _ FIFO_correspondence). Qed.

  Definition src_FIFO_is_transitive : Prop := ltac:(type_of_term (@prosa.model.priority.fifo.FIFO_is_transitive Job cR)).
  Definition tgt_FIFO_is_transitive : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_Fifo_FIFO_is_transitive Job dJ cL)).
  Theorem FIFO_is_transitive_correspondence : PropSPropRel src_FIFO_is_transitive tgt_FIFO_is_transitive.
  Proof. exact (pd_transitive_job_priorities_certificate Job _ _ FIFO_correspondence). Qed.

  Definition src_FIFO_is_total : Prop := ltac:(type_of_term (@prosa.model.priority.fifo.FIFO_is_total Job cR)).
  Definition tgt_FIFO_is_total : SProp := ltac:(type_of_term (@I.Prosa_Model_Priority_Fifo_FIFO_is_total Job dJ cL)).
  Theorem FIFO_is_total_correspondence : PropSPropRel src_FIFO_is_total tgt_FIFO_is_total.
  Proof. exact (pd_total_job_priorities_certificate Job _ _ FIFO_correspondence). Qed.

End Policy.
