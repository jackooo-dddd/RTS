(* Re-bound copy of accepted imported/translation_order/abstract_definitions/certificates/AbstractDefinitionsClasses.v for the busy_sbf artifact; only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import analysis.abstract.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskIntraInterferenceBound ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence AbstractDefinitionsBaseAdapter.

(** Bidirectional observations for the two one-field v0.6 classes.  The
    imported carrier uses the approved eqType -> Type + DecidableEq map. *)

Definition AdInterferenceRel (Job : eqType)
    (src : prosa.analysis.abstract.definitions.Interference Job)
    (dst : ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_Interference
      Job (ad_decidable_eq Job)) : SProp :=
  forall (j : Job) (t : nat),
    AdBoolRel
      (@prosa.analysis.abstract.definitions.interference Job src j t)
      (ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_Interference_interference
        Job (ad_decidable_eq Job) dst j (sub_nat_to_imported t)).

Definition ad_import_interference (Job : eqType)
    (src : prosa.analysis.abstract.definitions.Interference Job) :
    ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_Interference
      Job (ad_decidable_eq Job) :=
  ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_Interference_mk
    Job (ad_decidable_eq Job)
    (fun j t => ad_bool_to_imported
      (@prosa.analysis.abstract.definitions.interference Job src j
        (sub_nat_to_rocq t))).

Definition ad_export_interference (Job : eqType)
    (dst : ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_Interference
      Job (ad_decidable_eq Job)) :
    prosa.analysis.abstract.definitions.Interference Job :=
  fun j t => ad_bool_to_rocq
    (ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_Interference_interference
      Job (ad_decidable_eq Job) dst j (sub_nat_to_imported t)).

Lemma ad_interference_import_certificate (Job : eqType)
    (src : prosa.analysis.abstract.definitions.Interference Job) :
  AdInterferenceRel Job src (ad_import_interference Job src).
Proof.
  intros j t. unfold AdBoolRel, ad_import_interference.
  cbn [ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_Interference_interference
       ImportedTaskIntraInterferenceBound.interference].
  rw (sub_nat_rocq_roundtrip t).
  exact (@Lean.eq_refl _ _).
Qed.

Lemma ad_interference_export_certificate (Job : eqType)
    (dst : ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_Interference
      Job (ad_decidable_eq Job)) :
  AdInterferenceRel Job (ad_export_interference Job dst) dst.
Proof.
  intros j t. unfold AdBoolRel, ad_export_interference.
  exact (ad_bool_target_roundtrip
    (ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_Interference_interference
      Job (ad_decidable_eq Job) dst j (sub_nat_to_imported t))).
Qed.

Definition AdInterferingWorkloadRel (Job : eqType)
    (src : prosa.analysis.abstract.definitions.InterferingWorkload Job)
    (dst : ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_InterferingWorkload
      Job (ad_decidable_eq Job)) : SProp :=
  forall (j : Job) (t : nat),
    SubNatRel
      (@prosa.analysis.abstract.definitions.interfering_workload Job src j t)
      (ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_InterferingWorkload_interfering_workload
        Job (ad_decidable_eq Job) dst j (sub_nat_to_imported t)).

Definition ad_import_workload (Job : eqType)
    (src : prosa.analysis.abstract.definitions.InterferingWorkload Job) :
    ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_InterferingWorkload
      Job (ad_decidable_eq Job) :=
  ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_InterferingWorkload_mk
    Job (ad_decidable_eq Job)
    (fun j t => sub_nat_to_imported
      (@prosa.analysis.abstract.definitions.interfering_workload Job src j
        (sub_nat_to_rocq t))).

Definition ad_export_workload (Job : eqType)
    (dst : ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_InterferingWorkload
      Job (ad_decidable_eq Job)) :
    prosa.analysis.abstract.definitions.InterferingWorkload Job :=
  fun j t => sub_nat_to_rocq
    (ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_InterferingWorkload_interfering_workload
      Job (ad_decidable_eq Job) dst j (sub_nat_to_imported t)).

Lemma ad_workload_import_certificate (Job : eqType)
    (src : prosa.analysis.abstract.definitions.InterferingWorkload Job) :
  AdInterferingWorkloadRel Job src (ad_import_workload Job src).
Proof.
  intros j t. unfold ad_import_workload.
  cbn [ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_InterferingWorkload_interfering_workload
       ImportedTaskIntraInterferenceBound.interfering_workload].
  rw (sub_nat_rocq_roundtrip t).
  exact (sub_nat_rel_canonical _).
Qed.

Lemma ad_workload_export_certificate (Job : eqType)
    (dst : ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_InterferingWorkload
      Job (ad_decidable_eq Job)) :
  AdInterferingWorkloadRel Job (ad_export_workload Job dst) dst.
Proof. intros j t. exact (sub_nat_rel_surjective _). Qed.

Lemma ad_workload_related_general (Job : eqType)
    (src : prosa.analysis.abstract.definitions.InterferingWorkload Job)
    (dst : ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_InterferingWorkload
      Job (ad_decidable_eq Job))
    (j : Job) (tR : nat) (tL : Lean.Nat) :
  AdInterferingWorkloadRel Job src dst -> SubNatRel tR tL ->
  SubNatRel
    (@prosa.analysis.abstract.definitions.interfering_workload Job src j tR)
    (ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_InterferingWorkload_interfering_workload
      Job (ad_decidable_eq Job) dst j tL).
Proof.
  intros Hfield Ht. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _ (Hfield j tR)
    (sub_imported_eq_congr
      (ImportedTaskIntraInterferenceBound.Prosa_Analysis_Abstract_Definitions_InterferingWorkload_interfering_workload
        Job (ad_decidable_eq Job) dst j) _ _ Ht)).
Qed.

Print Assumptions ad_interference_import_certificate.
Print Assumptions ad_interference_export_certificate.
Print Assumptions ad_workload_import_certificate.
Print Assumptions ad_workload_export_certificate.
Print Assumptions ad_workload_related_general.
