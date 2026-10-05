From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From prosa Require Import analysis.definitions.priority.classes.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedAnalysisPriorityClasses.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder
  PriorityCoercionCorrespondence.

Module I := ImportedAnalysisPriorityClasses.

(** Definition certificate for [analysis/definitions/priority/classes.v]:
    related task maps ([PdJobTaskRel]), JLFP policies ([PdJLFPRel]) and FP
    policies ([PdFPRel]) -- each with the accepted two-way import/export
    certificates -- give related [JLFP_FP_compatible] propositions. *)

Lemma apc_and_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P /\ Q) (And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p q]. exact (And_intro PL QL (prop_to_sprop _ _ HP p) (prop_to_sprop _ _ HQ q)).
  - intros [p q]. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ HP p).
    + exact (sprop_to_prop _ _ HQ q).
Qed.

Section Compatible.
  Context (Task Job : eqType).
  Let dT := pd_decidable_eq Task.
  Let dJ := pd_decidable_eq Job.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : PdJobTaskRel Job Task jtR jtL.
  Variable fR : prosa.model.priority.definitions.FP_policy Task.
  Variable fL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hf : PdFPRel Task fR fL.

  Let jtl j := I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j.
  Let jtr j := @prosa.model.task.concept.job_task Job Task jtR j.

  Lemma apc_hep_task_related (j1 j2 : Job) :
    PdBoolRel (@prosa.model.priority.definitions.hep_task Task fR (jtr j1) (jtr j2))
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL (jtl j1) (jtl j2)).
  Proof.
    refine (pco_transport (fun v => PdBoolRel _
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL v (jtl j2))) _ _ (Hjt j1) _).
    refine (pco_transport (fun v => PdBoolRel _
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL (jtr j1) v)) _ _ (Hjt j2) _).
    exact (Hf _ _).
  Qed.

  Lemma apc_hp_task_related (j1 j2 : Job) :
    PdBoolRel (@prosa.model.priority.definitions.hp_task Task fR (jtr j1) (jtr j2))
      (I.Prosa_Model_Priority_Definitions_hp_task Task dT fL (jtl j1) (jtl j2)).
  Proof.
    unfold prosa.model.priority.definitions.hp_task.
    cbn [I.Prosa_Model_Priority_Definitions_hp_task].
    exact (pd_bool_and_related _ _ _ _ (apc_hep_task_related j1 j2)
      (pd_bool_not_related _ _ (apc_hep_task_related j2 j1))).
  Qed.

  Theorem JLFP_FP_compatible_correspondence pR pL :
    PdJLFPRel Job pR pL ->
    PropSPropRel
      (@prosa.analysis.definitions.priority.classes.JLFP_FP_compatible Task Job jtR pR fR)
      (I.Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible Task dT Job dJ jtL pL fL).
  Proof.
    intro Hp.
    unfold prosa.analysis.definitions.priority.classes.JLFP_FP_compatible.
    cbn [I.Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible].
    apply apc_and_correspondence.
    - apply pco_forall_id => j1. apply pco_forall_id => j2.
      apply pco_imp; [exact (pd_bool_truth_correspondence _ _ (Hp j1 j2))|].
      exact (pd_bool_truth_correspondence _ _ (apc_hep_task_related j1 j2)).
    - apply pco_forall_id => j1. apply pco_forall_id => j2.
      apply pco_imp; [exact (pd_bool_truth_correspondence _ _ (apc_hp_task_related j1 j2))|].
      exact (pd_bool_truth_correspondence _ _ (Hp j1 j2)).
  Qed.
End Compatible.
