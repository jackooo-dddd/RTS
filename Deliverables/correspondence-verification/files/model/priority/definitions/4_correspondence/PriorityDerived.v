From mathcomp Require Import ssreflect ssrbool eqtype.
From prosa Require Import model.priority.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityDefinitions.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation.
From PriorityCertificates Require Import PriorityBaseAdapter.

Lemma pd_another_hep_job_certificate (Job : eqType)
    (pR : prosa.model.priority.definitions.JLFP_policy Job)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_JLFP_policy
      Job (pd_decidable_eq Job)) (j1 j2 : Job) :
  PdJLFPRel Job pR pL ->
  PdBoolRel
    (@prosa.model.priority.definitions.another_hep_job Job pR j1 j2)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_another_hep_job
      Job (pd_decidable_eq Job) pL j1 j2).
Proof.
  intro Hp. unfold prosa.model.priority.definitions.another_hep_job,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_another_hep_job.
  exact (pd_bool_and_related _ _ _ _
    (Hp j1 j2) (pd_ne_observation Job j1 j2)).
Qed.

Lemma pd_another_task_hep_job_certificate (Task Job : eqType)
    (jtR : prosa.model.task.concept.JobTask Job Task)
    (jtL : ImportedPriorityDefinitions.Prosa_Model_Task_Concept_JobTask
      Job (pd_decidable_eq Job) Task (pd_decidable_eq Task))
    (pR : prosa.model.priority.definitions.JLFP_policy Job)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_JLFP_policy
      Job (pd_decidable_eq Job)) (j1 j2 : Job) :
  PdJobTaskRel Job Task jtR jtL -> PdJLFPRel Job pR pL ->
  PdBoolRel
    (@prosa.model.priority.definitions.another_task_hep_job
      Task Job jtR pR j1 j2)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_another_task_hep_job
      Task (pd_decidable_eq Task) Job (pd_decidable_eq Job)
      jtL pL j1 j2).
Proof.
  intros Hjt Hp.
  unfold prosa.model.priority.definitions.another_task_hep_job,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_another_task_hep_job.
  exact (pd_bool_and_related _ _ _ _ (Hp j1 j2)
    (pd_ne_observation_transport Task _ _ _ _ (Hjt j1) (Hjt j2))).
Qed.

Lemma pd_another_hep_job_of_same_task_certificate (Task Job : eqType)
    (jtR : prosa.model.task.concept.JobTask Job Task)
    (jtL : ImportedPriorityDefinitions.Prosa_Model_Task_Concept_JobTask
      Job (pd_decidable_eq Job) Task (pd_decidable_eq Task))
    (pR : prosa.model.priority.definitions.JLFP_policy Job)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_JLFP_policy
      Job (pd_decidable_eq Job)) (j1 j2 : Job) :
  PdJobTaskRel Job Task jtR jtL -> PdJLFPRel Job pR pL ->
  PdBoolRel
    (@prosa.model.priority.definitions.another_hep_job_of_same_task
      Task Job jtR pR j1 j2)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_another_hep_job_of_same_task
      Task (pd_decidable_eq Task) Job (pd_decidable_eq Job)
      jtL pL j1 j2).
Proof.
  intros Hjt Hp.
  unfold prosa.model.priority.definitions.another_hep_job_of_same_task,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_another_hep_job_of_same_task.
  exact (pd_bool_and_related _ _ _ _
    (pd_another_hep_job_certificate Job pR pL j1 j2 Hp)
    (pd_eq_observation_transport Task _ _ _ _ (Hjt j1) (Hjt j2))).
Qed.

Lemma pd_hp_task_certificate (Task : eqType)
    (pR : prosa.model.priority.definitions.FP_policy Task)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_FP_policy
      Task (pd_decidable_eq Task)) (x y : Task) :
  PdFPRel Task pR pL ->
  PdBoolRel (@prosa.model.priority.definitions.hp_task Task pR x y)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_hp_task
      Task (pd_decidable_eq Task) pL x y).
Proof.
  intro Hp. unfold prosa.model.priority.definitions.hp_task,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_hp_task.
  exact (pd_bool_and_related _ _ _ _ (Hp x y)
    (pd_bool_not_related _ _ (Hp y x))).
Qed.

Lemma pd_ep_task_certificate (Task : eqType)
    (pR : prosa.model.priority.definitions.FP_policy Task)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_FP_policy
      Task (pd_decidable_eq Task)) (x y : Task) :
  PdFPRel Task pR pL ->
  PdBoolRel (@prosa.model.priority.definitions.ep_task Task pR x y)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_ep_task
      Task (pd_decidable_eq Task) pL x y).
Proof.
  intro Hp. unfold prosa.model.priority.definitions.ep_task,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_ep_task.
  exact (pd_bool_and_related _ _ _ _ (Hp x y) (Hp y x)).
Qed.

Print Assumptions pd_another_hep_job_certificate.
Print Assumptions pd_another_task_hep_job_certificate.
Print Assumptions pd_another_hep_job_of_same_task_certificate.
Print Assumptions pd_hp_task_certificate.
Print Assumptions pd_ep_task_certificate.
