(* Re-bound copy of accepted imported/translation_order/abstract_definitions/certificates/AbstractDefinitionsOperations.v for the busy_sbf artifact; only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import analysis.abstract.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBusySbf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence AbstractDefinitionsBaseAdapter
  AbstractDefinitionsClasses.

(** The first operational certificate uses the already certified one-field
    class relation and an artifact-local Boolean conjunction lemma. *)

Lemma ad_bool_and_related aR aL bR bL :
  AdBoolRel aR aL -> AdBoolRel bR bL ->
  AdBoolRel (aR && bR) (ImportedBusySbf.Bool_and aL bL).
Proof.
  intros Ha Hb. destruct aR, aL, bR, bL; cbn in *;
    try exact (@Lean.eq_refl _ _);
    try exact (ad_false_elim _ (ad_false_ne_true Ha));
    try exact (ad_false_elim _ (ad_false_ne_true Hb));
    try exact (ad_false_elim _
      (ad_false_ne_true (sub_imported_eq_sym _ _ Ha)));
    try exact (ad_false_elim _
      (ad_false_ne_true (sub_imported_eq_sym _ _ Hb))).
Qed.

Definition AdBoolPredRel (Job : eqType)
    (predR : Job -> nat -> bool)
    (predL : Job -> Lean.Nat -> ImportedBusySbf.Bool) : SProp :=
  forall (j : Job) (t : nat),
    AdBoolRel (predR j t) (predL j (sub_nat_to_imported t)).

Lemma cond_interference_correspondence (Job : eqType)
    (interR : prosa.analysis.abstract.definitions.Interference Job)
    (interL : ImportedBusySbf.Prosa_Analysis_Abstract_Definitions_Interference
      Job (ad_decidable_eq Job))
    (predR : Job -> nat -> bool)
    (predL : Job -> Lean.Nat -> ImportedBusySbf.Bool)
    (j : Job) (t : nat) :
  AdInterferenceRel Job interR interL ->
  AdBoolPredRel Job predR predL ->
  AdBoolRel
    (@prosa.analysis.abstract.definitions.cond_interference
      Job interR predR j t)
    (ImportedBusySbf.Prosa_Analysis_Abstract_Definitions_cond_interference
      Job (ad_decidable_eq Job) interL predL j (sub_nat_to_imported t)).
Proof.
  intros Hinter Hpred.
  cbn [prosa.analysis.abstract.definitions.cond_interference
       ImportedBusySbf.Prosa_Analysis_Abstract_Definitions_cond_interference].
  exact (ad_bool_and_related _ _ _ _ (Hpred j t) (Hinter j t)).
Qed.

Lemma cond_interference_correspondence_general (Job : eqType)
    (interR : prosa.analysis.abstract.definitions.Interference Job)
    (interL : ImportedBusySbf.Prosa_Analysis_Abstract_Definitions_Interference
      Job (ad_decidable_eq Job))
    (predR : Job -> nat -> bool)
    (predL : Job -> Lean.Nat -> ImportedBusySbf.Bool)
    (j : Job) (tR : nat) (tL : Lean.Nat) :
  AdInterferenceRel Job interR interL ->
  AdBoolPredRel Job predR predL ->
  SubNatRel tR tL ->
  AdBoolRel
    (@prosa.analysis.abstract.definitions.cond_interference
      Job interR predR j tR)
    (ImportedBusySbf.Prosa_Analysis_Abstract_Definitions_cond_interference
      Job (ad_decidable_eq Job) interL predL j tL).
Proof.
  intros Hinter Hpred Ht. unfold AdBoolRel.
  exact (sub_imported_eq_trans _ _ _
    (cond_interference_correspondence Job interR interL
      predR predL j tR Hinter Hpred)
    (sub_imported_eq_congr
      (ImportedBusySbf.Prosa_Analysis_Abstract_Definitions_cond_interference
        Job (ad_decidable_eq Job) interL predL j) _ _ Ht)).
Qed.

Print Assumptions ad_bool_and_related.
Print Assumptions cond_interference_correspondence.
Print Assumptions cond_interference_correspondence_general.
