From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import analysis.abstract.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedAbstractDefinitions ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence AbstractDefinitionsBaseAdapter
  AbstractDefinitionsClasses AbstractDefinitionsOperations
  AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations.

(** Both interval sums use the same accepted, artifact-replayed finite-sum
    correspondence.  The target bodies are kernel-guarded projections of the
    current compiled Finset.Ico definitions. *)

Lemma ad_bool_to_nat_related (bR : bool)
    (bL : ImportedAbstractDefinitions.Bool) :
  AdBoolRel bR bL ->
  SubNatRel (nat_of_bool bR) (ImportedAbstractDefinitions.Bool_toNat bL).
Proof.
  intro Hb. destruct bR, bL; cbn in Hb |- *.
  - exact (ad_false_elim _
      (ad_false_ne_true (sub_imported_eq_sym _ _ Hb))).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical O).
  - exact (ad_false_elim _ (ad_false_ne_true Hb)).
Qed.

Section InterferenceSums.

Context (Job : eqType).
Variable interR : prosa.analysis.abstract.definitions.Interference Job.
Variable interL :
  ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_Interference
    Job (ad_decidable_eq Job).
Hypothesis Hinter : AdInterferenceRel Job interR interL.

Variable predR : Job -> nat -> bool.
Variable predL : Job -> Lean.Nat -> ImportedAbstractDefinitions.Bool.
Hypothesis Hpred : AdBoolPredRel Job predR predL.

Lemma cumul_cond_interference_correspondence (j : Job)
    (t1R t2R : nat) (t1L t2L : Lean.Nat) :
  SubNatRel t1R t1L -> SubNatRel t2R t2L ->
  SubNatRel
    (@prosa.analysis.abstract.definitions.cumul_cond_interference
      Job interR predR j t1R t2R)
    (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_cumul_cond_interference
      Job (ad_decidable_eq Job) interL predL j t1L t2L).
Proof.
  intros Ht1 Ht2.
  have Hsum := svc_interval_sum_related t1R t2R t1L t2L
    (fun t => nat_of_bool
      (@prosa.analysis.abstract.definitions.cond_interference
        Job interR predR j t))
    (fun t => ImportedAbstractDefinitions.Bool_toNat
      (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_cond_interference
        Job (ad_decidable_eq Job) interL predL j t))
    Ht1 Ht2
    (fun a b Hab => ad_bool_to_nat_related _ _
      (cond_interference_correspondence_general Job interR interL
        predR predL j a b Hinter Hpred Hab)).
  change (SubNatRel
    (@prosa.analysis.abstract.definitions.cumul_cond_interference
      Job interR predR j t1R t2R)
    (ImportedAbstractDefinitions.Prosa_Validation_AbstractDefinitionsInterface_cumulCondInterferenceProjection
      Job (ad_decidable_eq Job) interL predL j t1L t2L)) in Hsum.
  exact Hsum.
Qed.

End InterferenceSums.

Lemma cumulative_interference_correspondence (Job : eqType)
    (interR : prosa.analysis.abstract.definitions.Interference Job)
    (interL :
      ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_Interference
        Job (ad_decidable_eq Job))
    (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
  AdInterferenceRel Job interR interL ->
  SubNatRel t1R t1L -> SubNatRel t2R t2L ->
  SubNatRel
    (@prosa.analysis.abstract.definitions.cumulative_interference
      Job interR j t1R t2R)
    (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_cumulative_interference
      Job (ad_decidable_eq Job) interL j t1L t2L).
Proof.
  intros Hinter Ht1 Ht2.
  change (SubNatRel
    (@prosa.analysis.abstract.definitions.cumul_cond_interference
      Job interR (fun _ _ => true) j t1R t2R)
    (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_cumul_cond_interference
      Job (ad_decidable_eq Job) interL
      (fun _ _ => ImportedAbstractDefinitions.Bool_true) j t1L t2L)).
  apply cumul_cond_interference_correspondence; try assumption.
  intros j0 t. exact (@Lean.eq_refl _ _).
Qed.

Section WorkloadSums.

Context (Job : eqType).
Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
Variable workloadL :
  ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_InterferingWorkload
    Job (ad_decidable_eq Job).
Hypothesis Hworkload : AdInterferingWorkloadRel Job workloadR workloadL.

Lemma cumulative_interfering_workload_correspondence (j : Job)
    (t1R t2R : nat) (t1L t2L : Lean.Nat) :
  SubNatRel t1R t1L -> SubNatRel t2R t2L ->
  SubNatRel
    (@prosa.analysis.abstract.definitions.cumulative_interfering_workload
      Job workloadR j t1R t2R)
    (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_cumulative_interfering_workload
      Job (ad_decidable_eq Job) workloadL j t1L t2L).
Proof.
  intros Ht1 Ht2.
  have Hsum := svc_interval_sum_related t1R t2R t1L t2L
    (fun t => @prosa.analysis.abstract.definitions.interfering_workload
      Job workloadR j t)
    (fun t => ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_InterferingWorkload_interfering_workload
      Job (ad_decidable_eq Job) workloadL j t)
    Ht1 Ht2
    (fun a b Hab => ad_workload_related_general Job workloadR workloadL
      j a b Hworkload Hab).
  change (SubNatRel
    (@prosa.analysis.abstract.definitions.cumulative_interfering_workload
      Job workloadR j t1R t2R)
    (ImportedAbstractDefinitions.Prosa_Validation_AbstractDefinitionsInterface_cumulInterferingWorkloadProjection
      Job (ad_decidable_eq Job) workloadL j t1L t2L)) in Hsum.
  exact Hsum.
Qed.

End WorkloadSums.

Print Assumptions ad_bool_to_nat_related.
Print Assumptions cumul_cond_interference_correspondence.
Print Assumptions cumulative_interference_correspondence.
Print Assumptions cumulative_interfering_workload_correspondence.
