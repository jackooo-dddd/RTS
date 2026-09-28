From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From mathcomp Require Import ssralg ssrnum ssrint.
From prosa Require Import FactsPriorityGelSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes model.task.sequentiality analysis.definitions.work_bearing_readiness
  util.int model.priority.gel.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPriorityGel ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityGelHelpers.

Module I := ImportedFactsPriorityGel.
Module S := FactsPriorityGelSemanticSource.FactsPriorityGelSemanticSource.
Module PDS := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.

(** Statement correspondences for [analysis/facts/priority/gel.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types, the job-task, priority-point
    and arrival classes); target side: the imported Lean theorem types.
    Inputs: [job_task] by [Lean.eq], task priority points by the accepted
    [GelPriorityPointRel] (the constructor-wise [Int] relation [GelIntRel]),
    [job_arrival] pointwise.  Inputs quantified inside a statement are
    covered in both directions: job costs (pointwise), arrival sequences
    ([fpre_forall_arr]), processor models (the accepted [isj_cover_pstate]),
    schedules through the processor-model relation ([fpre_forall_sched]),
    the readiness instance on the statement's schedule pair
    ([fpre_forall_jr]), [JobPreemptable] instances ([fpre_forall_jp]), jobs
    and instants.

    [GEL] and the priority point are the accepted GEL certificate
    ([GEL_correspondence], [job_priority_point_correspondence]); the integer
    order and the addition of a natural number to an integer are its accepted
    [gel_le_related] and [gel_add_related].  The two order statements on a
    difference are rewritten on both sides: on the source side by the
    MathComp lemmas [lerBrDr] and [subr_ge0], on the target side by the two
    kernel-checked Lean equations exported with the artifact.  Preemption
    models, schedule validity, the JLFP policy at preemption points and the
    scheduled/completion observations are the accepted preemption-facts
    helpers; work-bearing readiness and sequential tasks are related by
    unfolding.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fgel_exists_identity (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (H x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (H x) Hx).
Qed.

Section Gel.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable ppR : prosa.model.priority.gel.PriorityPoint Task.
  Variable ppL : I.Prosa_Model_Priority_Gel_PriorityPoint Task dT.
  Hypothesis Hpp : GelPriorityPointRel Task ppR ppL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).

  Let GR := @prosa.model.priority.gel.GEL Job Task ppR jaR jtR.
  Let GL := I.Prosa_Model_Priority_Gel_GEL Job dJ Task dT ppL jaL jtL.

  Lemma fgel_hep_related (x y : Job) :
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job GR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ GL x y).
  Proof. exact (GEL_correspondence Job Task ppR ppL Hpp jaR jaL Hja jtR jtL Hjt x y). Qed.

  Lemma fgel_jpp_related (j : Job) :
    GelIntRel ((@prosa.behavior.job.job_arrival Job jaR j)%:R
        + @prosa.model.priority.gel.task_priority_point Task ppR (@prosa.model.task.concept.job_task Job Task jtR j))%R
      (I.Prosa_Model_Priority_Gel_job_priority_point Job dJ Task dT jtL ppL jaL j).
  Proof. exact (job_priority_point_correspondence Job Task ppR ppL Hpp jaR jaL Hja jtR jtL Hjt j). Qed.

  Lemma fgel_pp_related (j : Job) :
    GelIntRel (@prosa.model.priority.gel.task_priority_point Task ppR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task dT ppL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (sub_imported_eq_trans _ _ _ (Hpp _)
      (sub_imported_eq_congr (I.Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task dT ppL) _ _ (Hjt j))).
  Qed.

  Lemma fgel_same_task_related (x y : Job) :
    ArBoolRel (@prosa.model.task.concept.same_task Job Task jtR x y)
      (I.Prosa_Model_Task_Concept_same_task Job dJ Task dT jtL x y).
  Proof.
    unfold prosa.model.task.concept.same_task. cbn [I.Prosa_Model_Task_Concept_same_task].
    exact (pd_eq_observation_transport Task _ _ _ _ (Hjt x) (Hjt y)).
  Qed.

  (** *** hep_job_priority_point *)

  Definition src_hep_job_priority_point : Prop :=
    ltac:(body_of (fun s : S.statement_hep_job_priority_point => s Task Job jtR ppR jaR)).
  Definition tgt_hep_job_priority_point : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Gel_hep_job_priority_point Task dT Job dJ jtL ppL jaL)).

  Theorem hep_job_priority_point_correspondence :
    PropSPropRel src_hep_job_priority_point tgt_hep_job_priority_point.
  Proof.
    unfold src_hep_job_priority_point, tgt_hep_job_priority_point.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j'.
    exact (ar_bool_eq_correspondence _ _ _ _ (fgel_hep_related j j')
      (gel_le_related _ _ _ _ (fgel_jpp_related j) (fgel_jpp_related j'))).
  Qed.

  (** *** hep_job_arrival_gel *)

  Definition src_hep_job_arrival_gel : Prop :=
    ltac:(body_of (fun s : S.statement_hep_job_arrival_gel => s Task Job jtR ppR jaR)).
  Definition tgt_hep_job_arrival_gel : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Gel_hep_job_arrival_gel Task dT Job dJ jtL ppL jaL)).

  Theorem hep_job_arrival_gel_correspondence :
    PropSPropRel src_hep_job_arrival_gel tgt_hep_job_arrival_gel.
  Proof.
    unfold src_hep_job_arrival_gel, tgt_hep_job_arrival_gel.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (fgel_same_task_related j j'))|].
    exact (ar_bool_eq_correspondence _ _ _ _ (fgel_hep_related j j') (svc_decide_le_related _ _ _ _ (Hja j) (Hja j'))).
  Qed.

  (** *** hep_job_arrives_before *)

  Definition src_hep_job_arrives_before : Prop :=
    ltac:(body_of (fun s : S.statement_hep_job_arrives_before => s Task Job jtR ppR jaR)).
  Definition tgt_hep_job_arrives_before : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Gel_hep_job_arrives_before Task dT Job dJ jtL ppL jaL)).

  Theorem hep_job_arrives_before_correspondence :
    PropSPropRel src_hep_job_arrives_before tgt_hep_job_arrives_before.
  Proof.
    unfold src_hep_job_arrives_before, tgt_hep_job_arrives_before.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (fgel_hep_related j' j))|].
    apply ar_bool_truth_correspondence. unfold ArBoolRel.
    rewrite lerBrDr.
    refine (sub_imported_eq_trans _ _ _
      (gel_le_related _ _ _ _ (fgel_jpp_related j') (fgel_jpp_related j)) _).
    exact (sub_imported_eq_sym _ _
      (I.Prosa_Validation_FactsPriorityGelInterface_production_int_le_sub_iff _ _ _)).
  Qed.

  (** *** hep_job_arrives_after_zero *)

  Definition src_hep_job_arrives_after_zero : Prop :=
    ltac:(body_of (fun s : S.statement_hep_job_arrives_after_zero => s Task Job jtR ppR jaR)).
  Definition tgt_hep_job_arrives_after_zero : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Gel_hep_job_arrives_after_zero Task dT Job dJ jtL ppL jaL)).

  Theorem hep_job_arrives_after_zero_correspondence :
    PropSPropRel src_hep_job_arrives_after_zero tgt_hep_job_arrives_after_zero.
  Proof.
    unfold src_hep_job_arrives_after_zero, tgt_hep_job_arrives_after_zero.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (fgel_hep_related j' j))|].
    apply ar_bool_truth_correspondence. unfold ArBoolRel.
    rewrite subr_ge0.
    refine (sub_imported_eq_trans _ _ _
      (gel_le_related _ _ _ _ (fgel_pp_related j') (fgel_jpp_related j)) _).
    exact (sub_imported_eq_sym _ _
      (I.Prosa_Validation_FactsPriorityGelInterface_production_int_zero_le_sub_iff _ _)).
  Qed.

  (** *** GEL_respects_sequential_tasks *)

  Definition src_GEL_respects_sequential_tasks : Prop :=
    ltac:(body_of (fun s : S.statement_GEL_respects_sequential_tasks => s Task Job jtR ppR jaR)).
  Definition tgt_GEL_respects_sequential_tasks : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Gel_GEL_respects_sequential_tasks Task dT Job dJ jtL ppL jaL)).

  Theorem GEL_respects_sequential_tasks_correspondence :
    PropSPropRel src_GEL_respects_sequential_tasks tgt_GEL_respects_sequential_tasks.
  Proof.
    unfold src_GEL_respects_sequential_tasks, tgt_GEL_respects_sequential_tasks.
    unfold prosa.model.priority.definitions.policy_respects_sequential_tasks.
    cbn [I.Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (fgel_same_task_related j1 j2))|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
    exact (ar_bool_truth_correspondence _ _ (fgel_hep_related j1 j2)).
  Qed.

  (** *** GEL_implies_sequential_tasks *)

  Lemma fgel_forall_job_cost (PR : prosa.behavior.job.JobCost Job -> Prop)
      (PL : I.Prosa_Behavior_Job_JobCost Job dJ -> SProp) :
    (forall cR cL, SvcJobCostRel Job cR cL -> PropSPropRel (PR cR) (PL cL)) ->
    PropSPropRel (forall c, PR c) (forall c, PL c).
  Proof.
    exact (isj_forall_cover_sprop _ _ (SvcJobCostRel Job) (svc_import_job_cost Job) (svc_export_job_cost Job)
      (svc_job_cost_import Job) (svc_job_cost_export Job) PR PL).
  Qed.

  Section Pair.
    Variable costR : prosa.behavior.job.JobCost Job.
    Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
    Hypothesis Hcost : SvcJobCostRel Job costR costL.
    Variable PR : prosa.behavior.schedule.ProcessorState Job.
    Variable PL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
    Variable X : IsjPSRel Job PR PL.
    Variable sR : @prosa.behavior.schedule.schedule Job PR.
    Variable sL : I.Prosa_Behavior_Schedule_schedule Job dJ PL.
    Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Let Hsa := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.

    Lemma fgel_sequential_tasks_rel :
      PropSPropRel (@prosa.model.task.sequentiality.sequential_tasks Job Task jtR jaR costR PR arrR sR)
        (I.Prosa_Model_Task_Sequentiality_sequential_tasks Job dJ Task dT jtL jaL costL PL arrL sL).
    Proof.
      unfold prosa.model.task.sequentiality.sequential_tasks.
      cbn [I.Prosa_Model_Task_Sequentiality_sequential_tasks].
      apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j1 Harr)|].
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j2 Harr)|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (fgel_same_task_related j1 j2))|].
      apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j2 _ _ Ht))|].
      exact (ar_bool_truth_correspondence _ _
        (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs j1 tR tL Ht)).
    Qed.

    Section Ready.
      Variable jrR : @prosa.behavior.ready.JobReady Job PR costR jaR.
      Variable jrL : I.Prosa_Behavior_Ready_JobReady Job dJ PL costL jaL.
      Hypothesis Hjr : FpreJrAt Job jaR jaL costR costL PR PL sR sL jrR jrL.

      Lemma fgel_work_bearing_rel :
        PropSPropRel
          (@prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness
            Job jaR costR PR jrR arrR sR GR)
          (I.Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness
            Job dJ jaL costL PL jrL arrL sL GL).
      Proof.
        unfold prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness.
        cbn [I.Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
        apply ar_imp_correspondence;
          [exact (ar_bool_truth_correspondence _ _
            (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs j tR tL Ht))|].
        apply fgel_exists_identity. intro jhp.
        apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL jhp Harr)|].
        apply ar_and_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hjr jhp tR tL Ht))|].
        exact (ar_bool_truth_correspondence _ _ (fgel_hep_related jhp j)).
      Qed.
    End Ready.
  End Pair.

  Definition src_GEL_implies_sequential_tasks : Prop :=
    ltac:(body_of (fun s : S.statement_GEL_implies_sequential_tasks => s Task Job jtR ppR jaR)).
  Definition tgt_GEL_implies_sequential_tasks : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Gel_GEL_implies_sequential_tasks Task dT Job dJ jtL ppL jaL)).

  Theorem GEL_implies_sequential_tasks_correspondence :
    PropSPropRel src_GEL_implies_sequential_tasks tgt_GEL_implies_sequential_tasks.
  Proof.
    unfold src_GEL_implies_sequential_tasks, tgt_GEL_implies_sequential_tasks.
    apply fgel_forall_job_cost. intros costR costL Hcost.
    apply fpre_forall_arr. intros arrR arrL Harr.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply (isj_cover_pstate Job). intros PR PL X.
    apply ar_imp_correspondence; [exact (isj_psr_uniprocessor_related Job PR PL X)|].
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs). intros jrR jrL Hjr.
    apply ar_imp_correspondence;
      [exact (fgel_work_bearing_rel costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr)|].
    apply ar_imp_correspondence;
      [exact (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr)|].
    apply (fpre_forall_jp Job). intros jpR jpL Hjp.
    apply ar_imp_correspondence;
      [exact (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp)|].
    apply ar_imp_correspondence;
      [exact (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr
        jpR jpL Hjp GR GL fgel_hep_related)|].
    exact (fgel_sequential_tasks_rel costR costL Hcost PR PL X sR sL Hs arrR arrL Harr).
  Qed.

End Gel.
