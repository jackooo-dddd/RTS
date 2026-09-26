(* Re-bound copy of accepted imported/translation_order/abstract_definitions/certificates/AbstractDefinitionsLogical.v for the readiness_interference artifact;
   only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import analysis.abstract.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReadinessInterference ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence AbstractDefinitionsBaseAdapter
  AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations
  AbstractDefinitionsSums.

(** Small structural combinators for the actual imported [Job] and [Nat]
    binders.  They do not refer to any source/target theorem proof. *)
Lemma ad_forall_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (HP x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _ (HP x) (HL x)).
Qed.

Lemma ad_forall_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL ->
    PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall nR, PR nR) (forall nL, PL nL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR nL. exact (prop_to_sprop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL))
      (HR (sub_nat_to_rocq nL))).
  - intro HL. apply strictly_inhabits. intro nR.
    exact (sprop_to_prop _ _
      (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR))
      (HL (sub_nat_to_imported nR))).
Qed.

Lemma no_speculative_execution_correspondence (Job : eqType)
    (interR : prosa.analysis.abstract.definitions.Interference Job)
    (interL :
      ImportedReadinessInterference.Prosa_Analysis_Abstract_Definitions_Interference
        Job (ad_decidable_eq Job))
    (workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job)
    (workloadL :
      ImportedReadinessInterference.Prosa_Analysis_Abstract_Definitions_InterferingWorkload
        Job (ad_decidable_eq Job)) :
  AdInterferenceRel Job interR interL ->
  AdInterferingWorkloadRel Job workloadR workloadL ->
  PropSPropRel
    (@prosa.analysis.abstract.definitions.no_speculative_execution
      Job interR workloadR)
    (ImportedReadinessInterference.Prosa_Analysis_Abstract_Definitions_no_speculative_execution
      Job (ad_decidable_eq Job) interL workloadL).
Proof.
  intros Hinter Hworkload.
  apply ad_forall_identity_correspondence. intro j.
  apply ad_forall_nat_correspondence. intros tR tL Ht.
  change (PropSPropRel
    (is_true (leq
      (@prosa.analysis.abstract.definitions.cumulative_interference
        Job interR j 0 tR)
      (@prosa.analysis.abstract.definitions.cumulative_interfering_workload
        Job workloadR j 0 tR)))
    (sub_imported_le
      (ImportedReadinessInterference.Prosa_Analysis_Abstract_Definitions_cumulative_interference
        Job (ad_decidable_eq Job) interL j svc_target_zero tL)
      (ImportedReadinessInterference.Prosa_Analysis_Abstract_Definitions_cumulative_interfering_workload
        Job (ad_decidable_eq Job) workloadL j svc_target_zero tL))).
  apply sub_nat_le_correspondence.
  - exact (cumulative_interference_correspondence Job interR interL j
      0 tR svc_target_zero tL Hinter (sub_nat_rel_canonical 0) Ht).
  - exact (cumulative_interfering_workload_correspondence Job
      workloadR workloadL Hworkload j 0 tR svc_target_zero tL
      (sub_nat_rel_canonical 0) Ht).
Qed.

Print Assumptions ad_forall_identity_correspondence.
Print Assumptions ad_forall_nat_correspondence.
Print Assumptions no_speculative_execution_correspondence.
