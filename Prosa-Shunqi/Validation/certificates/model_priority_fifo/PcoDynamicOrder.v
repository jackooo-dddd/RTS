(* Re-bound copy of the accepted certificates/model_priority_definitions/PriorityDynamicOrder.v:
   only the imported module (ImportedPriorityDefinitions -> ImportedPriorityFifo),
   the certificate module prefix (Priority -> Pco) and its logical path are renamed. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From prosa Require Import model.priority.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityFifo.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence.
From FoundationCertificates Require Import PcoBaseAdapter.

Lemma pd_reflexive_priorities_certificate (Job : eqType)
    (pR : prosa.model.priority.definitions.JLDP_policy Job)
    (pL : ImportedPriorityFifo.Prosa_Model_Priority_Definitions_JLDP_policy
      Job (pd_decidable_eq Job)) :
  PdJLDPRel Job pR pL ->
  PropSPropRel
    (@prosa.model.priority.definitions.reflexive_priorities Job pR)
    (ImportedPriorityFifo.Prosa_Model_Priority_Definitions_reflexive_priorities
      Job (pd_decidable_eq Job) pL).
Proof.
  intro Hp. unfold prosa.model.priority.definitions.reflexive_priorities,
    ImportedPriorityFifo.Prosa_Model_Priority_Definitions_reflexive_priorities.
  apply prop_sprop_rel_intro.
  - intros H tL x.
    exact (prop_to_sprop _ _
      (pd_bool_truth_correspondence _ _
        (pd_jldp_field_at Job pR pL (sub_nat_to_rocq tL) tL x x
          Hp (sub_nat_rel_surjective tL)))
      (H (sub_nat_to_rocq tL) x)).
  - intro H. apply strictly_inhabits. intros tR x.
    exact (sprop_to_prop _ _
      (pd_bool_truth_correspondence _ _
        (pd_jldp_field_at Job pR pL tR (sub_nat_to_imported tR) x x
          Hp (sub_nat_rel_canonical tR)))
      (H (sub_nat_to_imported tR) x)).
Qed.

Lemma pd_transitive_priorities_certificate (Job : eqType)
    (pR : prosa.model.priority.definitions.JLDP_policy Job)
    (pL : ImportedPriorityFifo.Prosa_Model_Priority_Definitions_JLDP_policy
      Job (pd_decidable_eq Job)) :
  PdJLDPRel Job pR pL ->
  PropSPropRel
    (@prosa.model.priority.definitions.transitive_priorities Job pR)
    (ImportedPriorityFifo.Prosa_Model_Priority_Definitions_transitive_priorities
      Job (pd_decidable_eq Job) pL).
Proof.
  intro Hp. unfold prosa.model.priority.definitions.transitive_priorities,
    ImportedPriorityFifo.Prosa_Model_Priority_Definitions_transitive_priorities.
  apply prop_sprop_rel_intro.
  - intros H tL y x z Hxy Hyz.
    set (tR := sub_nat_to_rocq tL).
    set (Hxyr := pd_jldp_field_at Job pR pL tR tL x y
      Hp (sub_nat_rel_surjective tL)).
    set (Hyzr := pd_jldp_field_at Job pR pL tR tL y z
      Hp (sub_nat_rel_surjective tL)).
    exact (prop_to_sprop _ _
      (pd_bool_truth_correspondence _ _
        (pd_jldp_field_at Job pR pL tR tL x z
          Hp (sub_nat_rel_surjective tL)))
      (H tR y x z
        (sprop_to_prop _ _ (pd_bool_truth_correspondence _ _ Hxyr) Hxy)
        (sprop_to_prop _ _ (pd_bool_truth_correspondence _ _ Hyzr) Hyz))).
  - intro H. apply strictly_inhabits. intros tR y x z Hxy Hyz.
    exact (sprop_to_prop _ _
      (pd_bool_truth_correspondence _ _
        (pd_jldp_field_at Job pR pL tR (sub_nat_to_imported tR) x z
          Hp (sub_nat_rel_canonical tR)))
      (H (sub_nat_to_imported tR) y x z
        (prop_to_sprop _ _
          (pd_bool_truth_correspondence _ _
            (pd_jldp_field_at Job pR pL tR (sub_nat_to_imported tR) x y
              Hp (sub_nat_rel_canonical tR))) Hxy)
        (prop_to_sprop _ _
          (pd_bool_truth_correspondence _ _
            (pd_jldp_field_at Job pR pL tR (sub_nat_to_imported tR) y z
              Hp (sub_nat_rel_canonical tR))) Hyz))).
Qed.

Lemma pd_total_priorities_certificate (Job : eqType)
    (pR : prosa.model.priority.definitions.JLDP_policy Job)
    (pL : ImportedPriorityFifo.Prosa_Model_Priority_Definitions_JLDP_policy
      Job (pd_decidable_eq Job)) :
  PdJLDPRel Job pR pL ->
  PropSPropRel
    (@prosa.model.priority.definitions.total_priorities Job pR)
    (ImportedPriorityFifo.Prosa_Model_Priority_Definitions_total_priorities
      Job (pd_decidable_eq Job) pL).
Proof.
  intro Hp. unfold prosa.model.priority.definitions.total_priorities,
    ImportedPriorityFifo.Prosa_Model_Priority_Definitions_total_priorities.
  apply prop_sprop_rel_intro.
  - intros H tL x y.
    exact (prop_to_sprop _ _
      (pd_bool_truth_correspondence _ _
        (pd_bool_or_related _ _ _ _
          (pd_jldp_field_at Job pR pL (sub_nat_to_rocq tL) tL x y
            Hp (sub_nat_rel_surjective tL))
          (pd_jldp_field_at Job pR pL (sub_nat_to_rocq tL) tL y x
            Hp (sub_nat_rel_surjective tL))))
      (H (sub_nat_to_rocq tL) x y)).
  - intro H. apply strictly_inhabits. intros tR x y.
    exact (sprop_to_prop _ _
      (pd_bool_truth_correspondence _ _
        (pd_bool_or_related _ _ _ _
          (pd_jldp_field_at Job pR pL tR (sub_nat_to_imported tR) x y
            Hp (sub_nat_rel_canonical tR))
          (pd_jldp_field_at Job pR pL tR (sub_nat_to_imported tR) y x
            Hp (sub_nat_rel_canonical tR))))
      (H (sub_nat_to_imported tR) x y)).
Qed.

Print Assumptions pd_reflexive_priorities_certificate.
Print Assumptions pd_transitive_priorities_certificate.
Print Assumptions pd_total_priorities_certificate.
