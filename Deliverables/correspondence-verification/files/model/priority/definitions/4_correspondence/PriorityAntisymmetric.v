From mathcomp Require Import ssreflect ssrbool eqtype seq.
From prosa Require Import model.priority.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityDefinitions.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation.
From PriorityCertificates Require Import PriorityBaseAdapter PriorityListAdapter.

Lemma pd_antisymmetric_over_taskset_certificate (Task : eqType)
    (pR : prosa.model.priority.definitions.FP_policy Task)
    (pL : ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_FP_policy
      Task (pd_decidable_eq Task))
    (tsR : seq Task) (tsL : ImportedPriorityDefinitions.List Task) :
  PdFPRel Task pR pL -> PdListRel tsR tsL ->
  PropSPropRel
    (@prosa.model.priority.definitions.antisymmetric_over_taskset
      Task pR tsR)
    (ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_antisymmetric_over_taskset
      Task (pd_decidable_eq Task) pL tsL).
Proof.
  intros Hp Hts.
  unfold prosa.model.priority.definitions.antisymmetric_over_taskset,
    ImportedPriorityDefinitions.Prosa_Model_Priority_Definitions_antisymmetric_over_taskset,
    prosa.util.rel.antisymmetric_over_list,
    ImportedPriorityDefinitions.Prosa_Util_Rel_antisymmetric_over_list.
  apply prop_sprop_rel_intro.
  - intros H x y HxL HyL HxyL HyxL.
    apply coq_eq_to_imported_eq. apply H.
    + exact (sprop_to_prop _ _
        (pd_membership_correspondence Task x tsR tsL Hts) HxL).
    + exact (sprop_to_prop _ _
        (pd_membership_correspondence Task y tsR tsL Hts) HyL).
    + exact (sprop_to_prop _ _
        (pd_bool_truth_correspondence _ _ (Hp x y)) HxyL).
    + exact (sprop_to_prop _ _
        (pd_bool_truth_correspondence _ _ (Hp y x)) HyxL).
  - intro H. apply strictly_inhabits.
    intros x y HxR HyR HxyR HyxR.
    apply imported_eq_to_coq_eq. apply H.
    + exact (prop_to_sprop _ _
        (pd_membership_correspondence Task x tsR tsL Hts) HxR).
    + exact (prop_to_sprop _ _
        (pd_membership_correspondence Task y tsR tsL Hts) HyR).
    + exact (prop_to_sprop _ _
        (pd_bool_truth_correspondence _ _ (Hp x y)) HxyR).
    + exact (prop_to_sprop _ _
        (pd_bool_truth_correspondence _ _ (Hp y x)) HyxR).
Qed.

Print Assumptions pd_antisymmetric_over_taskset_certificate.
