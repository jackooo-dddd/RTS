From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsPriorityClassesSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPriorityClasses.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder
  PriorityCoercionCorrespondence AnalysisPriorityClassesCorrespondence.

Module I := ImportedFactsPriorityClasses.
Module S := FactsPriorityClassesSemanticSource.FactsPriorityClassesSemanticSource.

(** Statement correspondences for [analysis/facts/priority/classes.v].

    Source side: the extracted statement [S.statement_X] specialised at the
    task and job types; target side: the type of the imported Lean theorem at
    the same types.  All class inputs ([JobTask], [JobArrival], JLFP and FP
    policies) and all later binders are covered in both directions: the
    classes through the accepted import/export certificates of the Pco layer,
    jobs and tasks as identity carriers.  The derived priority relations and
    [JLFP_FP_compatible] are the accepted Pco/APC correspondences.  No source
    or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.

(** ** Combinators *)

Lemma fpc_forall_jt (Job Task : eqType)
    (PR : prosa.model.task.concept.JobTask Job Task -> Prop)
    (PL : I.Prosa_Model_Task_Concept_JobTask Job (pd_decidable_eq Job) Task (pd_decidable_eq Task) -> SProp) :
  (forall a b, PdJobTaskRel Job Task a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (pd_job_task_export_certificate Job Task b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a.
    exact (sprop_to_prop _ _ (H _ _ (pd_job_task_import_certificate Job Task a)) (HL _)).
Qed.

Lemma fpc_forall_ja (Job : eqType)
    (PR : prosa.behavior.job.JobArrival Job -> Prop)
    (PL : I.Prosa_Behavior_Job_JobArrival Job (pd_decidable_eq Job) -> SProp) :
  (forall a b, PdJobArrivalRel Job a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (pd_job_arrival_export_certificate Job b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a.
    exact (sprop_to_prop _ _ (H _ _ (pd_job_arrival_import_certificate Job a)) (HL _)).
Qed.

Lemma fpc_not_correspondence (P : Prop) (PL : SProp) :
  PropSPropRel P PL -> PropSPropRel (~ P) (I.Not PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros Hn p. exact (pd_false_to_imported (Hn (sprop_to_prop _ _ HP p))).
  - intro Hn. apply strictly_inhabits. intro p.
    exact (interpret_strict _ (pd_target_false_elim _ (Hn (prop_to_sprop _ _ HP p)))).
Qed.

Lemma fpc_false_correspondence (bR : bool) (bL : I.Bool) :
  PdBoolRel bR bL -> PropSPropRel (bR = false) (Lean.eq bL I.Bool_false).
Proof.
  intro Hb.
  exact (pd_bool_eq_correspondence _ _ false I.Bool_false Hb (@Lean.eq_refl _ _)).
Qed.

(** ** Derived relations *)

Section Derived.
  Context (Task Job : eqType).
  Let dT := pd_decidable_eq Task.
  Let dJ := pd_decidable_eq Job.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : PdJobTaskRel Job Task jtR jtL.
  Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hp : PdJLFPRel Job pR pL.

  Let jtl j := I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j.
  Let jtr j := @prosa.model.task.concept.job_task Job Task jtR j.

  Lemma fpc_another_hep_job_related (x y : Job) :
    PdBoolRel (@prosa.model.priority.definitions.another_hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_another_hep_job Job dJ pL x y).
  Proof.
    unfold prosa.model.priority.definitions.another_hep_job.
    cbn [I.Prosa_Model_Priority_Definitions_another_hep_job].
    exact (pd_bool_and_related _ _ _ _ (Hp x y) (pd_ne_observation Job x y)).
  Qed.

  Lemma fpc_same_task_related (x y : Job) :
    PdBoolRel (@prosa.model.task.concept.same_task Job Task jtR x y)
      (I.Prosa_Model_Task_Concept_same_task Job dJ Task dT jtL x y).
  Proof.
    unfold prosa.model.task.concept.same_task.
    cbn [I.Prosa_Model_Task_Concept_same_task].
    exact (pd_eq_observation_transport Task _ _ _ _ (Hjt x) (Hjt y)).
  Qed.

  Lemma fpc_job_of_task_related (tsk : Task) (x : Job) :
    PdBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk x)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk x).
  Proof.
    unfold prosa.model.task.concept.job_of_task.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    exact (pd_eq_observation_transport Task _ _ _ _ (Hjt x) (@Lean.eq_refl _ tsk)).
  Qed.

  Lemma fpc_another_task_hep_job_related (x y : Job) :
    PdBoolRel (@prosa.model.priority.definitions.another_task_hep_job Task Job jtR pR x y)
      (I.Prosa_Model_Priority_Definitions_another_task_hep_job Task dT Job dJ jtL pL x y).
  Proof.
    unfold prosa.model.priority.definitions.another_task_hep_job.
    cbn [I.Prosa_Model_Priority_Definitions_another_task_hep_job].
    exact (pd_bool_and_related _ _ _ _ (Hp x y) (pd_ne_observation_transport Task _ _ _ _ (Hjt x) (Hjt y))).
  Qed.

  Lemma fpc_another_hep_job_of_same_task_related (x y : Job) :
    PdBoolRel (@prosa.model.priority.definitions.another_hep_job_of_same_task Task Job jtR pR x y)
      (I.Prosa_Model_Priority_Definitions_another_hep_job_of_same_task Task dT Job dJ jtL pL x y).
  Proof.
    unfold prosa.model.priority.definitions.another_hep_job_of_same_task.
    cbn [I.Prosa_Model_Priority_Definitions_another_hep_job_of_same_task].
    exact (pd_bool_and_related _ _ _ _ (fpc_another_hep_job_related x y)
      (pd_eq_observation_transport Task _ _ _ _ (Hjt x) (Hjt y))).
  Qed.
End Derived.

Section FPDerived.
  Context (Task : eqType).
  Let dT := pd_decidable_eq Task.
  Variable fR : prosa.model.priority.definitions.FP_policy Task.
  Variable fL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hf : PdFPRel Task fR fL.

  Lemma fpc_hp_task_related (x y : Task) :
    PdBoolRel (@prosa.model.priority.definitions.hp_task Task fR x y)
      (I.Prosa_Model_Priority_Definitions_hp_task Task dT fL x y).
  Proof.
    unfold prosa.model.priority.definitions.hp_task.
    cbn [I.Prosa_Model_Priority_Definitions_hp_task].
    exact (pd_bool_and_related _ _ _ _ (Hf x y) (pd_bool_not_related _ _ (Hf y x))).
  Qed.

  Lemma fpc_ep_task_related (x y : Task) :
    PdBoolRel (@prosa.model.priority.definitions.ep_task Task fR x y)
      (I.Prosa_Model_Priority_Definitions_ep_task Task dT fL x y).
  Proof.
    unfold prosa.model.priority.definitions.ep_task.
    cbn [I.Prosa_Model_Priority_Definitions_ep_task].
    exact (pd_bool_and_related _ _ _ _ (Hf x y) (Hf y x)).
  Qed.
End FPDerived.

(** ** Statements *)

Section Statements.
  Context (Task Job : eqType).
  Let dT := pd_decidable_eq Task.
  Let dJ := pd_decidable_eq Job.

  Let T := pd_bool_truth_correspondence.
  Let N := pd_bool_not_related.
  Let AHJ := fpc_another_hep_job_related.
  Let ST := fpc_same_task_related.
  Let JOT := fpc_job_of_task_related.
  Let ATHJ := fpc_another_task_hep_job_related.
  Let AHJST := fpc_another_hep_job_of_same_task_related.
  Let HP := fpc_hp_task_related.
  Let EP := fpc_ep_task_related.

  Definition src_another_hep_job_antireflexive : Prop :=
    ltac:(body_of (fun s : S.statement_another_hep_job_antireflexive => s Job)).
  Definition tgt_another_hep_job_antireflexive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_another_hep_job_antireflexive Job dJ)).
  Theorem another_hep_job_antireflexive_correspondence :
    PropSPropRel src_another_hep_job_antireflexive tgt_another_hep_job_antireflexive.
  Proof.
    apply pco_forall_jlfp => pR pL Hp. apply pco_forall_id => j.
    exact (fpc_not_correspondence _ _ (T _ _ (AHJ Job pR pL Hp j j))).
  Qed.

  Definition src_another_hep_job_diff_task : Prop :=
    ltac:(body_of (fun s : S.statement_another_hep_job_diff_task => s Task Job)).
  Definition tgt_another_hep_job_diff_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_another_hep_job_diff_task Task dT Job dJ)).
  Theorem another_hep_job_diff_task_correspondence :
    PropSPropRel src_another_hep_job_diff_task tgt_another_hep_job_diff_task.
  Proof.
    apply fpc_forall_jt => jtR jtL Hjt. apply pco_forall_jlfp => pR pL Hp.
    apply pco_forall_id => j. apply pco_forall_id => j'.
    apply pco_imp; [exact (T _ _ (N _ _ (ST Task Job jtR jtL Hjt j j')))|].
    exact (pd_bool_eq_correspondence _ _ _ _ (AHJ Job pR pL Hp j j') (Hp j j')).
  Qed.

  Definition src_another_task_hep_job_taskwise_antireflexive : Prop :=
    ltac:(body_of (fun s : S.statement_another_task_hep_job_taskwise_antireflexive => s Task Job)).
  Definition tgt_another_task_hep_job_taskwise_antireflexive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_another_task_hep_job_taskwise_antireflexive
      Task dT Job dJ)).
  Theorem another_task_hep_job_taskwise_antireflexive_correspondence :
    PropSPropRel src_another_task_hep_job_taskwise_antireflexive tgt_another_task_hep_job_taskwise_antireflexive.
  Proof.
    apply fpc_forall_jt => jtR jtL Hjt. apply pco_forall_jlfp => pR pL Hp.
    apply pco_forall_id => tsk. apply pco_forall_id => j. apply pco_forall_id => j'.
    apply pco_imp; [exact (T _ _ (JOT Task Job jtR jtL Hjt tsk j))|].
    apply pco_imp; [exact (T _ _ (JOT Task Job jtR jtL Hjt tsk j'))|].
    exact (fpc_not_correspondence _ _ (T _ _ (ATHJ Task Job jtR jtL Hjt pR pL Hp j' j))).
  Qed.

  Definition src_another_task_hep_job_another_hep_job : Prop :=
    ltac:(body_of (fun s : S.statement_another_task_hep_job_another_hep_job => s Task Job)).
  Definition tgt_another_task_hep_job_another_hep_job : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_another_task_hep_job_another_hep_job
      Task dT Job dJ)).
  Theorem another_task_hep_job_another_hep_job_correspondence :
    PropSPropRel src_another_task_hep_job_another_hep_job tgt_another_task_hep_job_another_hep_job.
  Proof.
    apply fpc_forall_jt => jtR jtL Hjt. apply pco_forall_jlfp => pR pL Hp.
    apply pco_forall_id => j1. apply pco_forall_id => j2.
    exact (pd_bool_eq_correspondence _ _ _ _ (ATHJ Task Job jtR jtL Hjt pR pL Hp j1 j2)
      (pd_bool_and_related _ _ _ _ (AHJ Job pR pL Hp j1 j2)
        (pd_ne_observation_transport Task _ _ _ _ (Hjt j1) (Hjt j2)))).
  Qed.

  Definition src_another_hep_job_split_task : Prop :=
    ltac:(body_of (fun s : S.statement_another_hep_job_split_task => s Task Job)).
  Definition tgt_another_hep_job_split_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_another_hep_job_split_task Task dT Job dJ)).
  Theorem another_hep_job_split_task_correspondence :
    PropSPropRel src_another_hep_job_split_task tgt_another_hep_job_split_task.
  Proof.
    apply fpc_forall_jt => jtR jtL Hjt. apply pco_forall_jlfp => pR pL Hp.
    apply pco_forall_id => j1. apply pco_forall_id => j2.
    exact (pd_bool_eq_correspondence _ _ _ _ (AHJ Job pR pL Hp j1 j2)
      (pd_bool_or_related _ _ _ _ (ATHJ Task Job jtR jtL Hjt pR pL Hp j1 j2)
        (AHJST Task Job jtR jtL Hjt pR pL Hp j1 j2))).
  Qed.

  Definition src_another_hep_job_exclusive : Prop :=
    ltac:(body_of (fun s : S.statement_another_hep_job_exclusive => s Task Job)).
  Definition tgt_another_hep_job_exclusive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_another_hep_job_exclusive Task dT Job dJ)).
  Theorem another_hep_job_exclusive_correspondence :
    PropSPropRel src_another_hep_job_exclusive tgt_another_hep_job_exclusive.
  Proof.
    apply fpc_forall_jt => jtR jtL Hjt. apply pco_forall_jlfp => pR pL Hp.
    apply pco_forall_id => j1. apply pco_forall_id => j2.
    exact (T _ _ (N _ _ (pd_bool_and_related _ _ _ _ (ATHJ Task Job jtR jtL Hjt pR pL Hp j1 j2)
      (AHJST Task Job jtR jtL Hjt pR pL Hp j1 j2)))).
  Qed.

  Definition src_hp_task_irrefl : Prop :=
    ltac:(body_of (fun s : S.statement_hp_task_irrefl => s Task)).
  Definition tgt_hp_task_irrefl : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_hp_task_irrefl Task dT)).
  Theorem hp_task_irrefl_correspondence : PropSPropRel src_hp_task_irrefl tgt_hp_task_irrefl.
  Proof.
    apply pco_forall_fp => fR fL Hf. unfold irreflexive.
    apply pco_forall_id => x.
    exact (fpc_false_correspondence _ _ (HP Task fR fL Hf x x)).
  Qed.

  Definition src_hp_hep_task : Prop := ltac:(body_of (fun s : S.statement_hp_hep_task => s Task)).
  Definition tgt_hp_hep_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_hp_hep_task Task dT)).
  Theorem hp_hep_task_correspondence : PropSPropRel src_hp_hep_task tgt_hp_hep_task.
  Proof.
    apply pco_forall_fp => fR fL Hf. apply pco_forall_id => x. apply pco_forall_id => y.
    apply pco_imp; [exact (T _ _ (HP Task fR fL Hf x y))|]. exact (T _ _ (Hf x y)).
  Qed.

  Definition src_ep_hep_task : Prop := ltac:(body_of (fun s : S.statement_ep_hep_task => s Task)).
  Definition tgt_ep_hep_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_ep_hep_task Task dT)).
  Theorem ep_hep_task_correspondence : PropSPropRel src_ep_hep_task tgt_ep_hep_task.
  Proof.
    apply pco_forall_fp => fR fL Hf. apply pco_forall_id => x. apply pco_forall_id => y.
    apply pco_imp; [exact (T _ _ (EP Task fR fL Hf x y))|]. exact (T _ _ (Hf x y)).
  Qed.

  Definition src_ep_not_hp_task : Prop := ltac:(body_of (fun s : S.statement_ep_not_hp_task => s Task)).
  Definition tgt_ep_not_hp_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_ep_not_hp_task Task dT)).
  Theorem ep_not_hp_task_correspondence : PropSPropRel src_ep_not_hp_task tgt_ep_not_hp_task.
  Proof.
    apply pco_forall_fp => fR fL Hf. apply pco_forall_id => x. apply pco_forall_id => y.
    apply pco_imp; [exact (T _ _ (EP Task fR fL Hf x y))|]. exact (T _ _ (N _ _ (HP Task fR fL Hf x y))).
  Qed.

  Definition src_ep_task_sym : Prop := ltac:(body_of (fun s : S.statement_ep_task_sym => s Task)).
  Definition tgt_ep_task_sym : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_ep_task_sym Task dT)).
  Theorem ep_task_sym_correspondence : PropSPropRel src_ep_task_sym tgt_ep_task_sym.
  Proof.
    apply pco_forall_fp => fR fL Hf. apply pco_forall_id => x. apply pco_forall_id => y.
    exact (pd_bool_eq_correspondence _ _ _ _ (EP Task fR fL Hf x y) (EP Task fR fL Hf y x)).
  Qed.

  Definition src_hep_hp_ep_task : Prop := ltac:(body_of (fun s : S.statement_hep_hp_ep_task => s Task)).
  Definition tgt_hep_hp_ep_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_hep_hp_ep_task Task dT)).
  Theorem hep_hp_ep_task_correspondence : PropSPropRel src_hep_hp_ep_task tgt_hep_hp_ep_task.
  Proof.
    apply pco_forall_fp => fR fL Hf. apply pco_forall_id => x. apply pco_forall_id => y.
    exact (pd_bool_eq_correspondence _ _ _ _ (Hf x y)
      (pd_bool_or_related _ _ _ _ (HP Task fR fL Hf x y) (EP Task fR fL Hf x y))).
  Qed.

  Definition src_eq_reflexive : Prop := ltac:(body_of (fun s : S.statement_eq_reflexive => s Task)).
  Definition tgt_eq_reflexive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_eq_reflexive Task dT)).
  Theorem eq_reflexive_correspondence : PropSPropRel src_eq_reflexive tgt_eq_reflexive.
  Proof.
    apply pco_forall_fp => fR fL Hf.
    apply pco_imp; [exact (pd_reflexive_bool_certificate Task _ _ Hf)|].
    exact (pd_reflexive_bool_certificate Task _ _ (EP Task fR fL Hf)).
  Qed.

  Definition src_hp_trans : Prop := ltac:(body_of (fun s : S.statement_hp_trans => s Task)).
  Definition tgt_hp_trans : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_hp_trans Task dT)).
  Theorem hp_trans_correspondence : PropSPropRel src_hp_trans tgt_hp_trans.
  Proof.
    apply pco_forall_fp => fR fL Hf.
    apply pco_imp; [exact (pd_transitive_bool_certificate Task _ _ Hf)|].
    exact (pd_transitive_bool_certificate Task _ _ (HP Task fR fL Hf)).
  Qed.

  Definition src_hp_hep_trans : Prop := ltac:(body_of (fun s : S.statement_hp_hep_trans => s Task)).
  Definition tgt_hp_hep_trans : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_hp_hep_trans Task dT)).
  Theorem hp_hep_trans_correspondence : PropSPropRel src_hp_hep_trans tgt_hp_hep_trans.
  Proof.
    apply pco_forall_fp => fR fL Hf.
    apply pco_imp; [exact (pd_transitive_bool_certificate Task _ _ Hf)|].
    apply pco_forall_id => x. apply pco_forall_id => y. apply pco_forall_id => z.
    apply pco_imp; [exact (T _ _ (HP Task fR fL Hf x y))|].
    apply pco_imp; [exact (T _ _ (Hf y z))|].
    exact (T _ _ (HP Task fR fL Hf x z)).
  Qed.

  Definition src_hep_hp_trans : Prop := ltac:(body_of (fun s : S.statement_hep_hp_trans => s Task)).
  Definition tgt_hep_hp_trans : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_hep_hp_trans Task dT)).
  Theorem hep_hp_trans_correspondence : PropSPropRel src_hep_hp_trans tgt_hep_hp_trans.
  Proof.
    apply pco_forall_fp => fR fL Hf.
    apply pco_imp; [exact (pd_transitive_bool_certificate Task _ _ Hf)|].
    apply pco_forall_id => x. apply pco_forall_id => y. apply pco_forall_id => z.
    apply pco_imp; [exact (T _ _ (Hf x y))|].
    apply pco_imp; [exact (T _ _ (HP Task fR fL Hf y z))|].
    exact (T _ _ (HP Task fR fL Hf x z)).
  Qed.

  Definition src_not_hep_hp_task : Prop := ltac:(body_of (fun s : S.statement_not_hep_hp_task => s Task)).
  Definition tgt_not_hep_hp_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_not_hep_hp_task Task dT)).
  Theorem not_hep_hp_task_correspondence : PropSPropRel src_not_hep_hp_task tgt_not_hep_hp_task.
  Proof.
    apply pco_forall_fp => fR fL Hf.
    apply pco_imp; [exact (pd_total_bool_certificate Task _ _ Hf)|].
    apply pco_forall_id => x. apply pco_forall_id => y.
    exact (pd_bool_eq_correspondence _ _ _ _ (N _ _ (Hf x y)) (HP Task fR fL Hf y x)).
  Qed.

  Definition src_not_hp_hep_task : Prop := ltac:(body_of (fun s : S.statement_not_hp_hep_task => s Task)).
  Definition tgt_not_hp_hep_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_not_hp_hep_task Task dT)).
  Theorem not_hp_hep_task_correspondence : PropSPropRel src_not_hp_hep_task tgt_not_hp_hep_task.
  Proof.
    apply pco_forall_fp => fR fL Hf.
    apply pco_imp; [exact (pd_total_bool_certificate Task _ _ Hf)|].
    apply pco_forall_id => x. apply pco_forall_id => y.
    exact (pd_bool_eq_correspondence _ _ _ _ (N _ _ (HP Task fR fL Hf x y)) (Hf y x)).
  Qed.

  Definition src_nhp_ep_nhep_task : Prop := ltac:(body_of (fun s : S.statement_nhp_ep_nhep_task => s Task)).
  Definition tgt_nhp_ep_nhep_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_nhp_ep_nhep_task Task dT)).
  Theorem nhp_ep_nhep_task_correspondence : PropSPropRel src_nhp_ep_nhep_task tgt_nhp_ep_nhep_task.
  Proof.
    apply pco_forall_fp => fR fL Hf.
    apply pco_imp; [exact (pd_total_bool_certificate Task _ _ Hf)|].
    apply pco_forall_id => x. apply pco_forall_id => y.
    exact (pd_bool_eq_correspondence _ _ _ _ (N _ _ (HP Task fR fL Hf x y))
      (pd_bool_or_related _ _ _ _ (N _ _ (Hf x y)) (EP Task fR fL Hf x y))).
  Qed.

  Definition src_respects_sequential_tasks : Prop :=
    ltac:(body_of (fun s : S.statement_respects_sequential_tasks => s Task Job)).
  Definition tgt_respects_sequential_tasks : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_respects_sequential_tasks Task dT Job dJ)).
  Theorem respects_sequential_tasks_correspondence :
    PropSPropRel src_respects_sequential_tasks tgt_respects_sequential_tasks.
  Proof.
    apply fpc_forall_jt => jtR jtL Hjt. apply fpc_forall_ja => jaR jaL Hja.
    apply pco_forall_fp => fR fL Hf.
    apply pco_imp; [exact (pd_reflexive_task_priorities_certificate Task fR fL Hf)|].
    unfold prosa.model.priority.definitions.policy_respects_sequential_tasks.
    cbn [I.Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks].
    apply pco_forall_id => j1. apply pco_forall_id => j2.
    apply pco_imp; [exact (T _ _ (pd_eq_observation_transport Task _ _ _ _ (Hjt j1) (Hjt j2)))|].
    apply pco_imp; [exact (sub_nat_le_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
    exact (T _ _ (FP_to_JLFP_correspondence Task Job jtR jtL Hjt fR fL Hf j1 j2)).
  Qed.

  Definition src_hep_job_implies_hep_task : Prop :=
    ltac:(body_of (fun s : S.statement_hep_job_implies_hep_task => s Task Job)).
  Definition tgt_hep_job_implies_hep_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_hep_job_implies_hep_task Task dT Job dJ)).
  Theorem hep_job_implies_hep_task_correspondence :
    PropSPropRel src_hep_job_implies_hep_task tgt_hep_job_implies_hep_task.
  Proof.
    apply fpc_forall_jt => jtR jtL Hjt. apply pco_forall_jlfp => pR pL Hp.
    apply pco_forall_fp => fR fL Hf.
    apply pco_imp; [exact (JLFP_FP_compatible_correspondence Task Job jtR jtL Hjt fR fL Hf pR pL Hp)|].
    apply pco_forall_id => j1. apply pco_forall_id => j2.
    apply pco_imp; [exact (T _ _ (Hp j1 j2))|].
    exact (T _ _ (apc_hep_task_related Task Job jtR jtL Hjt fR fL Hf j1 j2)).
  Qed.

  Definition src_hp_task_implies_hep_job : Prop :=
    ltac:(body_of (fun s : S.statement_hp_task_implies_hep_job => s Task Job)).
  Definition tgt_hp_task_implies_hep_job : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Classes_hp_task_implies_hep_job Task dT Job dJ)).
  Theorem hp_task_implies_hep_job_correspondence :
    PropSPropRel src_hp_task_implies_hep_job tgt_hp_task_implies_hep_job.
  Proof.
    apply fpc_forall_jt => jtR jtL Hjt. apply pco_forall_jlfp => pR pL Hp.
    apply pco_forall_fp => fR fL Hf.
    apply pco_imp; [exact (JLFP_FP_compatible_correspondence Task Job jtR jtL Hjt fR fL Hf pR pL Hp)|].
    apply pco_forall_id => j1. apply pco_forall_id => j2.
    apply pco_imp; [exact (T _ _ (apc_hp_task_related Task Job jtR jtL Hjt fR fL Hf j1 j2))|].
    exact (T _ _ (Hp j1 j2)).
  Qed.
End Statements.
