From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.job.properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJobProperties ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence JobPropertiesBaseAdapter
  JobPropertiesOperations.

(** Both certificates refer to the official v0.6 definitions and this run's
    actual imported compiled Lean definitions.  The second composes only
    independently checked operation correspondences, never either target
    definition as a proof. *)

Lemma job_cost_positive_correspondence (T : eqType)
    (costR : prosa.behavior.job.JobCost T)
    (costL : ImportedJobProperties.Prosa_Behavior_Job_JobCost T
      (jp_decidable_eq T)) (j : T) :
  JpJobCostRel T costR costL ->
  JpBoolRel (@prosa.model.job.properties.job_cost_positive T costR j)
    (ImportedJobProperties.Prosa_Model_Job_Properties_job_cost_positive T
      (jp_decidable_eq T) costL j).
Proof.
  intro Hcost.
  unfold prosa.model.job.properties.job_cost_positive.
  unfold ImportedJobProperties.Prosa_Model_Job_Properties_job_cost_positive.
  change (JpBoolRel
    (ltn O (@prosa.behavior.job.job_cost T costR j))
    (jp_target_decide_lt Lean.Nat_zero
      (ImportedJobProperties.Prosa_Behavior_Job_JobCost_job_cost T
        (jp_decidable_eq T) costL j))).
  apply jp_decide_lt_related.
  - exact (sub_nat_rel_canonical O).
  - exact (Hcost j).
Qed.

Lemma arrivals_have_positive_job_costs_correspondence (T : eqType)
    (costR : prosa.behavior.job.JobCost T)
    (costL : ImportedJobProperties.Prosa_Behavior_Job_JobCost T
      (jp_decidable_eq T))
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL : ImportedJobProperties.Prosa_Behavior_Arrival_sequence_arrival_sequence
      T (jp_decidable_eq T)) :
  JpJobCostRel T costR costL ->
  JpArrivalSequenceRel T arrR arrL ->
  PropSPropRel
    (@prosa.model.job.properties.arrivals_have_positive_job_costs
      T costR arrR)
    (ImportedJobProperties.Prosa_Model_Job_Properties_arrivals_have_positive_job_costs
      T (jp_decidable_eq T) costL arrL).
Proof.
  intros Hcost Harr.
  unfold prosa.model.job.properties.arrivals_have_positive_job_costs.
  unfold ImportedJobProperties.Prosa_Model_Job_Properties_arrivals_have_positive_job_costs.
  apply jp_forall_identity_correspondence. intro j.
  apply jp_imp_correspondence.
  - exact (jp_arrives_in_related T arrR arrL j Harr).
  - apply jp_bool_truth_correspondence.
    exact (job_cost_positive_correspondence T costR costL j Hcost).
Qed.

Print Assumptions job_cost_positive_correspondence.
Print Assumptions arrivals_have_positive_job_costs_correspondence.
