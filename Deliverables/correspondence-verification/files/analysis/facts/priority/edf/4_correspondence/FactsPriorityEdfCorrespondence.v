From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsPriorityEdfSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.priority.classes
  model.priority.edf model.task.absolute_deadline model.task.sequentiality
  analysis.definitions.work_bearing_readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPriorityEdf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers.

Module I := ImportedFactsPriorityEdf.
Module S := FactsPriorityEdfSemanticSource.FactsPriorityEdfSemanticSource.

(** Statement correspondences for [analysis/facts/priority/edf.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (the job and task types, the deadline, arrival,
    cost, job-task and task-deadline classes); target side: the imported Lean
    theorem types.  Inputs: [job_deadline] and [task_deadline] pointwise by
    [SubNatRel], [job_arrival] by [ArJobArrivalRel], [job_cost] by the
    accepted [SvcJobCostRel], [job_task] by [Lean.eq].  The EDF policy is
    related pointwise on Booleans through the deadline comparison (over the
    task-derived deadlines as in the accepted blocking-bound certificate);
    [same_task] through the job-task equality.  In the last statement the
    processor model, the arrival sequence, the schedule, the readiness
    instance (at the statement's schedule pair) and the preemption model are
    covered in both directions by the accepted preemption-facts covers; work
    bearing readiness is replayed as in the accepted priority-sequential
    certificate, and [sequential_tasks] over the processor-model pair
    observations.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fpe_logic_eq_to_lean_eq {A : Type} (x y : A) : Logic.eq x y -> Lean.eq x y.
Proof. intros []. exact (@Lean.eq_refl _ _). Qed.

Lemma fpe_lean_transport {A : Type} (P : A -> SProp) (x y : A) : Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma fpe_decide_eq_related (T : eqType) (x y : T) :
  ArBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (ar_decidable_eq T x y)).
Proof.
  apply fpe_logic_eq_to_lean_eq.
  unfold ar_decidable_eq. case: eqP => H; reflexivity.
Qed.

Lemma fpe_exists_identity (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (H x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (H x) Hx).
Qed.

Section JobDeadline.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable jdR : prosa.behavior.job.JobDeadline Job.
  Variable jdL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
  Hypothesis Hjd : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_deadline Job jdR j) (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ jdL j).

  Definition src_hep_job_deadline : Prop :=
    ltac:(body_of (fun s : S.statement_hep_job_deadline => s Job jdR)).
  Definition tgt_hep_job_deadline : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Edf_hep_job_deadline Job dJ jdL)).

  Theorem hep_job_deadline_correspondence : PropSPropRel src_hep_job_deadline tgt_hep_job_deadline.
  Proof.
    unfold src_hep_job_deadline, tgt_hep_job_deadline.
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_identity_correspondence => j'.
    have H := svc_decide_le_related _ _ _ _ (Hjd j) (Hjd j').
    exact (ar_bool_eq_correspondence _ _ _ _ H H).
  Qed.
End JobDeadline.

Section TaskDeadline.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable tdR : prosa.model.task.concept.TaskDeadline Task.
  Variable tdL : I.Prosa_Model_Task_Concept_TaskDeadline Task dT.
  Hypothesis Htd : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR tsk)
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL tsk).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

  Let DLR := @prosa.model.task.absolute_deadline.job_deadline_from_task_deadline Job Task tdR jaR jtR.
  Let DLL := I.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task dJ dT tdL jaL jtL.

  Lemma fpe_task_deadline_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (fpe_lean_transport (fun v => SubNatRel
      (@prosa.model.task.concept.task_deadline Task tdR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL v)) _ _ (Hjt j) (Htd _)).
  Qed.

  Lemma fpe_deadline_related (j : Job) :
    SubNatRel (@prosa.behavior.job.job_deadline Job DLR j) (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ DLL j).
  Proof. exact (svc_target_add_related _ _ _ _ (Hja j) (fpe_task_deadline_of_job_related j)). Qed.

  Lemma fpe_edf_rel :
    FpreJLFPRel Job (@prosa.model.priority.edf.EDF Job DLR) (I.Prosa_Model_Priority_Edf_EDF Job dJ DLL).
  Proof.
    intros x y. exact (svc_decide_le_related _ _ _ _ (fpe_deadline_related x) (fpe_deadline_related y)).
  Qed.

  Lemma fpe_same_task_related (j1 j2 : Job) :
    ArBoolRel (@prosa.model.task.concept.same_task Job Task jtR j1 j2)
      (I.Prosa_Model_Task_Concept_same_task Job dJ Task dT jtL j1 j2).
  Proof.
    unfold prosa.model.task.concept.same_task.
    cbn [I.Prosa_Model_Task_Concept_same_task].
    refine (fpe_lean_transport (fun v => ArBoolRel _
      (I.Decidable_decide (Lean.eq v (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j2))
        (dT v (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j2)))) _ _ (Hjt j1) _).
    refine (fpe_lean_transport (fun v => ArBoolRel _
      (I.Decidable_decide (Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j1) v)
        (dT (@prosa.model.task.concept.job_task Job Task jtR j1) v))) _ _ (Hjt j2) _).
    exact (fpe_decide_eq_related Task _ _).
  Qed.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Definition src_hep_job_task_deadline : Prop :=
    ltac:(body_of (fun s : S.statement_hep_job_task_deadline => s Job jaR Task tdR jtR)).
  Definition tgt_hep_job_task_deadline : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Edf_hep_job_task_deadline
      Job dJ jaL Task dT tdL jtL)).

  Theorem hep_job_task_deadline_correspondence :
    PropSPropRel src_hep_job_task_deadline tgt_hep_job_task_deadline.
  Proof.
    unfold src_hep_job_task_deadline, tgt_hep_job_task_deadline.
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_identity_correspondence => j'.
    exact (ar_bool_eq_correspondence _ _ _ _ (fpe_edf_rel j j')
      (svc_decide_le_related _ _ _ _
        (svc_target_add_related _ _ _ _ (Hja j) (fpe_task_deadline_of_job_related j))
        (svc_target_add_related _ _ _ _ (Hja j') (fpe_task_deadline_of_job_related j')))).
  Qed.

  Definition src_hep_job_arrival_edf : Prop :=
    ltac:(body_of (fun s : S.statement_hep_job_arrival_edf => s Job jaR Task tdR jtR)).
  Definition tgt_hep_job_arrival_edf : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Edf_hep_job_arrival_edf
      Job dJ jaL Task dT tdL jtL)).

  Theorem hep_job_arrival_edf_correspondence :
    PropSPropRel src_hep_job_arrival_edf tgt_hep_job_arrival_edf.
  Proof.
    unfold src_hep_job_arrival_edf, tgt_hep_job_arrival_edf.
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_identity_correspondence => j'.
    imp (ar_bool_truth_correspondence _ _ (fpe_same_task_related j j')).
    exact (ar_bool_eq_correspondence _ _ _ _ (fpe_edf_rel j j')
      (svc_decide_le_related _ _ _ _ (Hja j) (Hja j'))).
  Qed.

  Definition src_EDF_respects_sequential_tasks : Prop :=
    ltac:(body_of (fun s : S.statement_EDF_respects_sequential_tasks => s Job jaR Task tdR jtR)).
  Definition tgt_EDF_respects_sequential_tasks : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Edf_EDF_respects_sequential_tasks
      Job dJ jaL Task dT tdL jtL)).

  Theorem EDF_respects_sequential_tasks_correspondence :
    PropSPropRel src_EDF_respects_sequential_tasks tgt_EDF_respects_sequential_tasks.
  Proof.
    unfold src_EDF_respects_sequential_tasks, tgt_EDF_respects_sequential_tasks.
    unfold prosa.model.priority.definitions.policy_respects_sequential_tasks.
    cbn [I.Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    imp (ar_bool_truth_correspondence _ _ (fpe_same_task_related j1 j2)).
    imp (sub_nat_le_correspondence _ _ _ _ (Hja j1) (Hja j2)).
    exact (ar_bool_truth_correspondence _ _ (fpe_edf_rel j1 j2)).
  Qed.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Definition src_EDF_implies_sequential_tasks : Prop :=
    ltac:(body_of (fun s : S.statement_EDF_implies_sequential_tasks => s Task tdR Job jtR jaR costR)).
  Definition tgt_EDF_implies_sequential_tasks : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Edf_EDF_implies_sequential_tasks
      Job dJ Task dT tdL jtL jaL costL)).

  Theorem EDF_implies_sequential_tasks_correspondence :
    PropSPropRel src_EDF_implies_sequential_tasks tgt_EDF_implies_sequential_tasks.
  Proof.
    unfold src_EDF_implies_sequential_tasks, tgt_EDF_implies_sequential_tasks.
    have Hp := fpe_edf_rel.
    apply (isj_cover_pstate Job). intros PR PL X.
    imp (isj_psr_uniprocessor_related Job PR PL X).
    apply (fpre_forall_arr Job). intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs). intros jrR jrL Hjr.
    apply ar_imp_correspondence.
    { unfold prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness.
      cbn [I.Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      imp (ar_bool_truth_correspondence _ _
        (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs j tR tL Ht)).
      apply fpe_exists_identity. intro jhp.
      apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL jhp Harr)|].
      apply ar_and_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hjr jhp tR tL Ht))|].
      exact (ar_bool_truth_correspondence _ _ (Hp jhp j)). }
    imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr).
    apply fpre_forall_jp. intros jpR jpL Hjp.
    imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp).
    imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr
      jrR jrL Hjr jpR jpL Hjp _ _ Hp).
    unfold prosa.model.task.sequentiality.sequential_tasks.
    cbn [I.Prosa_Model_Task_Sequentiality_sequential_tasks].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply ar_forall_nat_correspondence => tR tL Ht.
    imp (arrives_in_correspondence_certificate Job arrR arrL j1 Harr).
    imp (arrives_in_correspondence_certificate Job arrR arrL j2 Harr).
    imp (ar_bool_truth_correspondence _ _ (fpe_same_task_related j1 j2)).
    imp (sub_nat_lt_correspondence _ _ _ _ (Hja j1) (Hja j2)).
    imp (ar_bool_truth_correspondence _ _ (fpre_scheduled_at_related Job PR PL X sR sL Hs j2 tR tL Ht)).
    exact (ar_bool_truth_correspondence _ _
      (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs j1 tR tL Ht)).
  Qed.
End TaskDeadline.
