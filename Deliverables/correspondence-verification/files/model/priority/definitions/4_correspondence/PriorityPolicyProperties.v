From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From prosa Require Import model.priority.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityDefinitions.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence.
From PriorityCertificates Require Import PriorityBaseAdapter.

Lemma pd_policy_is_FIFO_certificate (Job : eqType)
    (aR : prosa.behavior.job.JobArrival Job)
    (aL : ImportedPriorityDefinitions.Prosa_Behavior_Job_JobArrival
      Job (pd_decidable_eq Job))
    (pR : prosa.model.priority.definitions.JLFP_policy Job)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_JLFP_policy
      Job (pd_decidable_eq Job)) :
  PdJobArrivalRel Job aR aL -> PdJLFPRel Job pR pL ->
  PropSPropRel
    (@prosa.model.priority.definitions.policy_is_FIFO Job aR pR)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_policy_is_FIFO
      Job (pd_decidable_eq Job) aL pL).
Proof.
  intros Ha Hp.
  unfold prosa.model.priority.definitions.policy_is_FIFO,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_policy_is_FIFO.
  apply prop_sprop_rel_intro.
  - intros H j1 j2.
    exact (prop_to_sprop _ _
      (pd_bool_eq_correspondence _ _ _ _ (Hp j1 j2)
        (pd_decide_le_related _ _ _ _ (Ha j1) (Ha j2)))
      (H j1 j2)).
  - intro H. apply strictly_inhabits. intros j1 j2.
    exact (sprop_to_prop _ _
      (pd_bool_eq_correspondence _ _ _ _ (Hp j1 j2)
        (pd_decide_le_related _ _ _ _ (Ha j1) (Ha j2)))
      (H j1 j2)).
Qed.

Lemma pd_policy_respects_sequential_tasks_certificate (Task Job : eqType)
    (jtR : prosa.model.task.concept.JobTask Job Task)
    (jtL : ImportedPriorityDefinitions.Prosa_Model_Task_Concept_JobTask
      Job (pd_decidable_eq Job) Task (pd_decidable_eq Task))
    (aR : prosa.behavior.job.JobArrival Job)
    (aL : ImportedPriorityDefinitions.Prosa_Behavior_Job_JobArrival
      Job (pd_decidable_eq Job))
    (pR : prosa.model.priority.definitions.JLFP_policy Job)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_JLFP_policy
      Job (pd_decidable_eq Job)) :
  PdJobTaskRel Job Task jtR jtL -> PdJobArrivalRel Job aR aL ->
  PdJLFPRel Job pR pL ->
  PropSPropRel
    (@prosa.model.priority.definitions.policy_respects_sequential_tasks
      Task Job jtR aR pR)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks
      Task (pd_decidable_eq Task) Job (pd_decidable_eq Job)
      jtL aL pL).
Proof.
  intros Hjt Ha Hp.
  unfold prosa.model.priority.definitions.policy_respects_sequential_tasks,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks.
  apply prop_sprop_rel_intro.
  - intros H j1 j2 HsameL HarrL.
    apply (prop_to_sprop _ _
      (pd_bool_truth_correspondence _ _ (Hp j1 j2))).
    apply H.
    + exact (sprop_to_prop _ _
        (pd_bool_truth_correspondence _ _
          (pd_eq_observation_transport Task _ _ _ _ (Hjt j1) (Hjt j2)))
        HsameL).
    + exact (sprop_to_prop _ _
        (sub_nat_le_correspondence _ _ _ _ (Ha j1) (Ha j2))
        HarrL).
  - intro H. apply strictly_inhabits.
    intros j1 j2 HsameR HarrR.
    apply (sprop_to_prop _ _
      (pd_bool_truth_correspondence _ _ (Hp j1 j2))).
    apply H.
    + exact (prop_to_sprop _ _
        (pd_bool_truth_correspondence _ _
          (pd_eq_observation_transport Task _ _ _ _ (Hjt j1) (Hjt j2)))
        HsameR).
    + exact (prop_to_sprop _ _
        (sub_nat_le_correspondence _ _ _ _ (Ha j1) (Ha j2))
        HarrR).
Qed.

Print Assumptions pd_policy_is_FIFO_certificate.
Print Assumptions pd_policy_respects_sequential_tasks_certificate.
