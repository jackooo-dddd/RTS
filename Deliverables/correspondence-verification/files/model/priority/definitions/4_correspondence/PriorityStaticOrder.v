From mathcomp Require Import ssreflect ssrbool eqtype seq.
From prosa Require Import model.priority.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityDefinitions.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation.
From PriorityCertificates Require Import PriorityBaseAdapter.

(** The nine order-property definitions are related by the actual policy
    field operation.  These lemmas never infer correspondence merely from
    separate provability of the two definitions. *)

Lemma pd_reflexive_bool_certificate (T : eqType)
    (RR : T -> T -> bool)
    (RL : T -> T -> ImportedPriorityDefinitions.Bool) :
  (forall x y, PdBoolRel (RR x y) (RL x y)) ->
  PropSPropRel (reflexive RR)
    (forall x, Lean.eq (RL x x) ImportedPriorityDefinitions.Bool_true).
Proof.
  intro HR. apply prop_sprop_rel_intro.
  - intros H x. exact (prop_to_sprop _ _
      (pd_bool_truth_correspondence _ _ (HR x x)) (H x)).
  - intro H. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _
      (pd_bool_truth_correspondence _ _ (HR x x)) (H x)).
Qed.

Lemma pd_transitive_bool_certificate (T : eqType)
    (RR : T -> T -> bool)
    (RL : T -> T -> ImportedPriorityDefinitions.Bool) :
  (forall x y, PdBoolRel (RR x y) (RL x y)) ->
  PropSPropRel (transitive RR)
    (forall y x z,
      Lean.eq (RL x y) ImportedPriorityDefinitions.Bool_true ->
      Lean.eq (RL y z) ImportedPriorityDefinitions.Bool_true ->
      Lean.eq (RL x z) ImportedPriorityDefinitions.Bool_true).
Proof.
  intro HR. apply prop_sprop_rel_intro.
  - intros H y x z Hxy Hyz.
    apply (prop_to_sprop _ _ (pd_bool_truth_correspondence _ _ (HR x z))).
    apply (H y x z).
    + exact (sprop_to_prop _ _
        (pd_bool_truth_correspondence _ _ (HR x y)) Hxy).
    + exact (sprop_to_prop _ _
        (pd_bool_truth_correspondence _ _ (HR y z)) Hyz).
  - intro H. apply strictly_inhabits. intros y x z Hxy Hyz.
    apply (sprop_to_prop _ _ (pd_bool_truth_correspondence _ _ (HR x z))).
    apply (H y x z).
    + exact (prop_to_sprop _ _
        (pd_bool_truth_correspondence _ _ (HR x y)) Hxy).
    + exact (prop_to_sprop _ _
        (pd_bool_truth_correspondence _ _ (HR y z)) Hyz).
Qed.

Lemma pd_total_bool_certificate (T : eqType)
    (RR : T -> T -> bool)
    (RL : T -> T -> ImportedPriorityDefinitions.Bool) :
  (forall x y, PdBoolRel (RR x y) (RL x y)) ->
  PropSPropRel (total RR)
    (forall x y,
      Lean.eq (ImportedPriorityDefinitions.Bool_or (RL x y) (RL y x))
        ImportedPriorityDefinitions.Bool_true).
Proof.
  intro HR. apply prop_sprop_rel_intro.
  - intros H x y.
    exact (prop_to_sprop _ _
      (pd_bool_truth_correspondence _ _
        (pd_bool_or_related _ _ _ _ (HR x y) (HR y x))) (H x y)).
  - intro H. apply strictly_inhabits. intros x y.
    exact (sprop_to_prop _ _
      (pd_bool_truth_correspondence _ _
        (pd_bool_or_related _ _ _ _ (HR x y) (HR y x))) (H x y)).
Qed.

Lemma pd_reflexive_job_priorities_certificate (Job : eqType)
    (pR : prosa.model.priority.definitions.JLFP_policy Job)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_JLFP_policy
      Job (pd_decidable_eq Job)) :
  PdJLFPRel Job pR pL ->
  PropSPropRel
    (@prosa.model.priority.definitions.reflexive_job_priorities Job pR)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_reflexive_job_priorities
      Job (pd_decidable_eq Job) pL).
Proof.
  intro Hp.
  unfold prosa.model.priority.definitions.reflexive_job_priorities,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_reflexive_job_priorities.
  exact (pd_reflexive_bool_certificate Job _ _ Hp).
Qed.

Lemma pd_transitive_job_priorities_certificate (Job : eqType)
    (pR : prosa.model.priority.definitions.JLFP_policy Job)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_JLFP_policy
      Job (pd_decidable_eq Job)) :
  PdJLFPRel Job pR pL ->
  PropSPropRel
    (@prosa.model.priority.definitions.transitive_job_priorities Job pR)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_transitive_job_priorities
      Job (pd_decidable_eq Job) pL).
Proof.
  intro Hp.
  unfold prosa.model.priority.definitions.transitive_job_priorities,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_transitive_job_priorities.
  exact (pd_transitive_bool_certificate Job _ _ Hp).
Qed.

Lemma pd_total_job_priorities_certificate (Job : eqType)
    (pR : prosa.model.priority.definitions.JLFP_policy Job)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_JLFP_policy
      Job (pd_decidable_eq Job)) :
  PdJLFPRel Job pR pL ->
  PropSPropRel
    (@prosa.model.priority.definitions.total_job_priorities Job pR)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_total_job_priorities
      Job (pd_decidable_eq Job) pL).
Proof.
  intro Hp.
  unfold prosa.model.priority.definitions.total_job_priorities,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_total_job_priorities.
  exact (pd_total_bool_certificate Job _ _ Hp).
Qed.

Lemma pd_reflexive_task_priorities_certificate (Task : eqType)
    (pR : prosa.model.priority.definitions.FP_policy Task)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_FP_policy
      Task (pd_decidable_eq Task)) :
  PdFPRel Task pR pL ->
  PropSPropRel
    (@prosa.model.priority.definitions.reflexive_task_priorities Task pR)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_reflexive_task_priorities
      Task (pd_decidable_eq Task) pL).
Proof.
  intro Hp.
  unfold prosa.model.priority.definitions.reflexive_task_priorities,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_reflexive_task_priorities.
  exact (pd_reflexive_bool_certificate Task _ _ Hp).
Qed.

Lemma pd_transitive_task_priorities_certificate (Task : eqType)
    (pR : prosa.model.priority.definitions.FP_policy Task)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_FP_policy
      Task (pd_decidable_eq Task)) :
  PdFPRel Task pR pL ->
  PropSPropRel
    (@prosa.model.priority.definitions.transitive_task_priorities Task pR)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_transitive_task_priorities
      Task (pd_decidable_eq Task) pL).
Proof.
  intro Hp.
  unfold prosa.model.priority.definitions.transitive_task_priorities,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_transitive_task_priorities.
  exact (pd_transitive_bool_certificate Task _ _ Hp).
Qed.

Lemma pd_total_task_priorities_certificate (Task : eqType)
    (pR : prosa.model.priority.definitions.FP_policy Task)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_FP_policy
      Task (pd_decidable_eq Task)) :
  PdFPRel Task pR pL ->
  PropSPropRel
    (@prosa.model.priority.definitions.total_task_priorities Task pR)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_total_task_priorities
      Task (pd_decidable_eq Task) pL).
Proof.
  intro Hp.
  unfold prosa.model.priority.definitions.total_task_priorities,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_total_task_priorities.
  exact (pd_total_bool_certificate Task _ _ Hp).
Qed.

Print Assumptions pd_reflexive_job_priorities_certificate.
Print Assumptions pd_transitive_job_priorities_certificate.
Print Assumptions pd_total_job_priorities_certificate.
Print Assumptions pd_reflexive_task_priorities_certificate.
Print Assumptions pd_transitive_task_priorities_certificate.
Print Assumptions pd_total_task_priorities_certificate.
