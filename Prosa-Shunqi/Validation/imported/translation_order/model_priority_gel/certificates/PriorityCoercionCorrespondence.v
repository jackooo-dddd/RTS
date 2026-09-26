From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From prosa Require Import model.priority.coercion.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityGel.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder.

Module I := ImportedPriorityGel.

(** Correspondence certificates for [model/priority/coercion.v].

    The two conversions are definitional certificates (related inputs give
    related policies).  For the eight remarks/lemmas the source side is the
    exact elaborated type of the pinned source declaration (taken with
    [type of], so the source proof is not referenced) and the target side is
    the type of the imported Lean theorem.  Policy binders are covered in both
    directions by the accepted import/export certificates. *)

Ltac type_of_term t := let T := type of t in exact T.

Lemma pco_transport {A : Type} (P : A -> SProp) (x y : A) : Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma pco_forall_id (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (HP x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x. exact (sprop_to_prop _ _ (HP x) (HL x)).
Qed.

Lemma pco_forall_nat (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall nR, PR nR) (forall nL, PL nL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR nL. exact (prop_to_sprop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL)) (HR (sub_nat_to_rocq nL))).
  - intro HL. apply strictly_inhabits. intro nR.
    exact (sprop_to_prop _ _
      (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) (HL (sub_nat_to_imported nR))).
Qed.

Lemma pco_imp (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. apply (prop_to_sprop _ _ HQ). exact (H (sprop_to_prop _ _ HP p)).
  - intro H. apply strictly_inhabits. intro p.
    apply (sprop_to_prop _ _ HQ). exact (H (prop_to_sprop _ _ HP p)).
Qed.

(** Two-way coverage of FP and JLFP policies. *)
Lemma pco_forall_fp (Task : eqType)
    (PR : prosa.model.priority.definitions.FP_policy Task -> Prop)
    (PL : I.Prosa_Model_Priority_Definitions_FP_policy Task (pd_decidable_eq Task) -> SProp) :
  (forall pR pL, PdFPRel Task pR pL -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall pR, PR pR) (forall pL, PL pL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H _ _ (pd_fp_export_certificate Task pL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ (H _ _ (pd_fp_import_certificate Task pR)) (HL _)).
Qed.

Lemma pco_forall_jlfp (Job : eqType)
    (PR : prosa.model.priority.definitions.JLFP_policy Job -> Prop)
    (PL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job (pd_decidable_eq Job) -> SProp) :
  (forall pR pL, PdJLFPRel Job pR pL -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall pR, PR pR) (forall pL, PL pL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H _ _ (pd_jlfp_export_certificate Job pL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ (H _ _ (pd_jlfp_import_certificate Job pR)) (HL _)).
Qed.

(** ** JLFP -> JLDP (input: Job) *)

Section JLFPtoJLDP.
  Context (Job : eqType).
  Let dJ := pd_decidable_eq Job.

  Theorem JLFP_to_JLDP_correspondence pR pL :
    PdJLFPRel Job pR pL ->
    PdJLDPRel Job (@prosa.model.priority.coercion.JLFP_to_JLDP Job pR)
      (I.Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job dJ pL).
  Proof. intros Hp t x y. exact (Hp x y). Qed.

  Let JLDP := JLFP_to_JLDP_correspondence.

  Definition src_hep_job_at_jlfp : Prop :=
    ltac:(type_of_term (@prosa.model.priority.coercion.hep_job_at_jlfp Job)).
  Definition tgt_hep_job_at_jlfp : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Priority_Coercion_hep_job_at_jlfp Job dJ)).
  Theorem hep_job_at_jlfp_correspondence :
    PropSPropRel src_hep_job_at_jlfp tgt_hep_job_at_jlfp.
  Proof.
    apply pco_forall_jlfp => pR pL Hp.
    apply pco_forall_id => j.
    apply pco_forall_id => j'.
    apply pco_forall_nat => tR tL Ht.
    exact (pd_bool_eq_correspondence _ _ _ _
      (pd_jldp_field_at Job _ _ tR tL j j' (JLDP pR pL Hp) Ht) (Hp j j')).
  Qed.

  Definition src_reflexive_priorities_JLFP_implies_JLDP : Prop :=
    ltac:(type_of_term (@prosa.model.priority.coercion.reflexive_priorities_JLFP_implies_JLDP Job)).
  Definition tgt_reflexive_priorities_JLFP_implies_JLDP : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Priority_Coercion_reflexive_priorities_JLFP_implies_JLDP Job dJ)).
  Theorem reflexive_priorities_JLFP_implies_JLDP_correspondence :
    PropSPropRel src_reflexive_priorities_JLFP_implies_JLDP tgt_reflexive_priorities_JLFP_implies_JLDP.
  Proof.
    apply pco_forall_jlfp => pR pL Hp.
    apply pco_imp; [exact (pd_reflexive_job_priorities_certificate Job pR pL Hp)|].
    exact (pd_reflexive_priorities_certificate Job _ _ (JLDP pR pL Hp)).
  Qed.

  Definition src_transitive_priorities_JLFP_implies_JLDP : Prop :=
    ltac:(type_of_term (@prosa.model.priority.coercion.transitive_priorities_JLFP_implies_JLDP Job)).
  Definition tgt_transitive_priorities_JLFP_implies_JLDP : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Priority_Coercion_transitive_priorities_JLFP_implies_JLDP Job dJ)).
  Theorem transitive_priorities_JLFP_implies_JLDP_correspondence :
    PropSPropRel src_transitive_priorities_JLFP_implies_JLDP tgt_transitive_priorities_JLFP_implies_JLDP.
  Proof.
    apply pco_forall_jlfp => pR pL Hp.
    apply pco_imp; [exact (pd_transitive_job_priorities_certificate Job pR pL Hp)|].
    exact (pd_transitive_priorities_certificate Job _ _ (JLDP pR pL Hp)).
  Qed.

  Definition src_total_priorities_JLFP_implies_JLDP : Prop :=
    ltac:(type_of_term (@prosa.model.priority.coercion.total_priorities_JLFP_implies_JLDP Job)).
  Definition tgt_total_priorities_JLFP_implies_JLDP : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Priority_Coercion_total_priorities_JLFP_implies_JLDP Job dJ)).
  Theorem total_priorities_JLFP_implies_JLDP_correspondence :
    PropSPropRel src_total_priorities_JLFP_implies_JLDP tgt_total_priorities_JLFP_implies_JLDP.
  Proof.
    apply pco_forall_jlfp => pR pL Hp.
    apply pco_imp; [exact (pd_total_job_priorities_certificate Job pR pL Hp)|].
    exact (pd_total_priorities_certificate Job _ _ (JLDP pR pL Hp)).
  Qed.
End JLFPtoJLDP.

(** ** FP -> JLFP (inputs: Task, Job, related JobTask instances) *)

Section FPtoJLFP.
  Context (Task Job : eqType).
  Let dJ := pd_decidable_eq Job.
  Let dT := pd_decidable_eq Task.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : PdJobTaskRel Job Task jtR jtL.

  Lemma pco_hep_task_of_jobs fpR fpL (x y : Job) :
    PdFPRel Task fpR fpL ->
    PdBoolRel
      (@prosa.model.priority.definitions.hep_task Task fpR
        (@prosa.model.task.concept.job_task Job Task jtR x)
        (@prosa.model.task.concept.job_task Job Task jtR y))
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL x)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y)).
  Proof.
    intro Hfp.
    refine (pco_transport (fun v => PdBoolRel _
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL v
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))) _ _ (Hjt x) _).
    refine (pco_transport (fun v => PdBoolRel _
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL
        (@prosa.model.task.concept.job_task Job Task jtR x) v)) _ _ (Hjt y) _).
    exact (Hfp _ _).
  Qed.

  Theorem FP_to_JLFP_correspondence fpR fpL :
    PdFPRel Task fpR fpL ->
    PdJLFPRel Job (@prosa.model.priority.coercion.FP_to_JLFP Job Task jtR fpR)
      (I.Prosa_Model_Priority_Coercion_FP_to_JLFP Job dJ Task dT jtL fpL).
  Proof. intros Hfp x y. exact (pco_hep_task_of_jobs fpR fpL x y Hfp). Qed.

  Let JLFP := FP_to_JLFP_correspondence.

  Definition src_hep_job_at_fp : Prop :=
    ltac:(type_of_term (@prosa.model.priority.coercion.hep_job_at_fp Task Job jtR)).
  Definition tgt_hep_job_at_fp : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Priority_Coercion_hep_job_at_fp Task dT Job dJ jtL)).
  Theorem hep_job_at_fp_correspondence :
    PropSPropRel src_hep_job_at_fp tgt_hep_job_at_fp.
  Proof.
    apply pco_forall_fp => fpR fpL Hfp.
    apply pco_forall_id => j.
    apply pco_forall_id => j'.
    apply pco_forall_nat => tR tL Ht.
    exact (pd_bool_eq_correspondence _ _ _ _
      (pd_jldp_field_at Job _ _ tR tL j j'
        (JLFP_to_JLDP_correspondence Job _ _ (JLFP fpR fpL Hfp)) Ht)
      (pco_hep_task_of_jobs fpR fpL j j' Hfp)).
  Qed.

  Definition src_reflexive_priorities_FP_implies_JLFP : Prop :=
    ltac:(type_of_term (@prosa.model.priority.coercion.reflexive_priorities_FP_implies_JLFP Task Job jtR)).
  Definition tgt_reflexive_priorities_FP_implies_JLFP : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Priority_Coercion_reflexive_priorities_FP_implies_JLFP Task dT Job dJ jtL)).
  Theorem reflexive_priorities_FP_implies_JLFP_correspondence :
    PropSPropRel src_reflexive_priorities_FP_implies_JLFP tgt_reflexive_priorities_FP_implies_JLFP.
  Proof.
    apply pco_forall_fp => fpR fpL Hfp.
    apply pco_imp; [exact (pd_reflexive_task_priorities_certificate Task fpR fpL Hfp)|].
    exact (pd_reflexive_job_priorities_certificate Job _ _ (JLFP fpR fpL Hfp)).
  Qed.

  Definition src_transitive_priorities_FP_implies_JLFP : Prop :=
    ltac:(type_of_term (@prosa.model.priority.coercion.transitive_priorities_FP_implies_JLFP Task Job jtR)).
  Definition tgt_transitive_priorities_FP_implies_JLFP : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Priority_Coercion_transitive_priorities_FP_implies_JLFP Task dT Job dJ jtL)).
  Theorem transitive_priorities_FP_implies_JLFP_correspondence :
    PropSPropRel src_transitive_priorities_FP_implies_JLFP tgt_transitive_priorities_FP_implies_JLFP.
  Proof.
    apply pco_forall_fp => fpR fpL Hfp.
    apply pco_imp; [exact (pd_transitive_task_priorities_certificate Task fpR fpL Hfp)|].
    exact (pd_transitive_job_priorities_certificate Job _ _ (JLFP fpR fpL Hfp)).
  Qed.

  Definition src_total_priorities_FP_implies_JLFP : Prop :=
    ltac:(type_of_term (@prosa.model.priority.coercion.total_priorities_FP_implies_JLFP Task Job jtR)).
  Definition tgt_total_priorities_FP_implies_JLFP : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Priority_Coercion_total_priorities_FP_implies_JLFP Task dT Job dJ jtL)).
  Theorem total_priorities_FP_implies_JLFP_correspondence :
    PropSPropRel src_total_priorities_FP_implies_JLFP tgt_total_priorities_FP_implies_JLFP.
  Proof.
    apply pco_forall_fp => fpR fpL Hfp.
    apply pco_imp; [exact (pd_total_task_priorities_certificate Task fpR fpL Hfp)|].
    exact (pd_total_job_priorities_certificate Job _ _ (JLFP fpR fpL Hfp)).
  Qed.
End FPtoJLFP.
