From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import BlockingBoundFpFactsSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes model.job.properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBlockingBoundFpFacts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers
  TaskPreemptionParametersCorrespondence BusyIntervalPiHelpers.

Module I := ImportedBlockingBoundFpFacts.
Module S := BlockingBoundFpFactsSemanticSource.BlockingBoundFpFactsSemanticSource.
Module TPS := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module BBF := BlockingBoundFpSemanticSource.BlockingBoundFpSemanticSource.

(** Statement correspondence for [analysis/facts/blocking_bound/fp.v].

    Source side: the extracted statement specialised at its leading inputs
    (task and job types, the task-level maximum nonpreemptive segment, the
    job-task and cost classes); target side: the imported Lean theorem type.
    Inputs: [job_cost] by the accepted [SvcJobCostRel], [job_task] by
    [Lean.eq], [TaskMaxNonpreemptiveSegment] by the accepted
    [TppMaxSegmentRel].  Inputs quantified inside the statement are covered in
    both directions: processor models, schedules and [JobPreemptable]
    instances by the accepted conversions of the busy-interval family, FP
    policies pointwise on Booleans ([bbfp_forall_fp]), arrival sequences
    ([fpre_forall_arr]), task sets ([bbfp_forall_list]), tasks and jobs
    (identity) and instants.  The JLFP policy induced by an FP policy (the
    canonical [FP_to_JLFP] conversion on both sides) is related through the
    task relation ([bbfp_fp_jlfp_rel]); the FP blocking bound is related by
    replaying the accepted blocking-bound certificate through the
    kernel-checked [bigMaxListCond] equations; the maximum lower-priority
    nonpreemptive segment is the accepted [pi] definition certificate.  No
    source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma bbfp_forall_list (T : Type) (PRl : seq T -> Prop) (PLl : I.List T -> SProp) :
  (forall xsR xsL, ArListRel xsR xsL -> PropSPropRel (PRl xsR) (PLl xsL)) ->
  PropSPropRel (forall xs, PRl xs) (forall xs, PLl xs).
Proof.
  apply (isj_forall_cover_sprop _ _ ArListRel ar_list_to_imported ar_list_to_rocq).
  - intro xs. exact (@Lean.eq_refl _ _).
  - intro xs. exact (ar_list_target_roundtrip xs).
Qed.

Section FpCover.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.

  Definition BbfpFPRel (fR : prosa.model.priority.definitions.FP_policy Task)
      (fL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT) : SProp :=
    forall x y : Task, ArBoolRel (@prosa.model.priority.definitions.hep_task Task fR x y)
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL x y).

  Lemma bbfp_forall_fp (PRf : prosa.model.priority.definitions.FP_policy Task -> Prop)
      (PLf : I.Prosa_Model_Priority_Definitions_FP_policy Task dT -> SProp) :
    (forall fR fL, BbfpFPRel fR fL -> PropSPropRel (PRf fR) (PLf fL)) ->
    PropSPropRel (forall f, PRf f) (forall f, PLf f).
  Proof.
    apply (isj_forall_cover_sprop _ _ BbfpFPRel
      (fun fR => I.Prosa_Model_Priority_Definitions_FP_policy_mk Task dT
        (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_task Task fR x y)))
      (fun fL => ((fun x y => ar_bool_to_rocq
        (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL x y))
        : prosa.model.priority.definitions.FP_policy Task))).
    - intros fR x y. exact (@Lean.eq_refl _ _).
    - intros fL x y. exact (ar_bool_target_roundtrip _).
  Qed.
End FpCover.

Section BlockingFp.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.

  Variable mR : TPS.TaskMaxNonpreemptiveSegment Task.
  Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
  Hypothesis Hm : TppMaxSegmentRel Task mR mL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Lemma bbfp_fp_jlfp_rel fR fL (Hf : BbfpFPRel Task fR fL) :
    FpreJLFPRel Job (@FP_to_JLFP Job Task jtR fR)
      (I.Prosa_Model_Priority_Coercion_FP_to_JLFP Job dJ Task dT jtL fL).
  Proof.
    intros x y.
    refine (isj_lean_transport (fun v => ArBoolRel
      (@prosa.model.priority.definitions.hep_task Task fR
        (@prosa.model.task.concept.job_task Job Task jtR x) (@prosa.model.task.concept.job_task Job Task jtR y))
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL v
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))) _ _ (Hjt x) _).
    refine (isj_lean_transport (fun v => ArBoolRel
      (@prosa.model.priority.definitions.hep_task Task fR
        (@prosa.model.task.concept.job_task Job Task jtR x) (@prosa.model.task.concept.job_task Job Task jtR y))
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL
        (@prosa.model.task.concept.job_task Job Task jtR x) v)) _ _ (Hjt y) _).
    exact (Hf _ _).
  Qed.

  Lemma bbfp_blocking_bound_related fR fL (Hf : BbfpFPRel Task fR fL) tsR tsL (Hts : ArListRel tsR tsL)
      (tsk : Task) :
    SubNatRel (@BBF.blocking_bound Task mR fR tsR tsk)
      (I.Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound Task dT mL fL tsL tsk).
  Proof.
    unfold BBF.blocking_bound.
    cbn [I.Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound].
    apply bpi_bigmax_related; [| |exact Hts].
    - intro o. exact (svc_bool_not_related _ _ (Hf o tsk)).
    - intro o. exact (svc_target_sub_related _ _ _ _ (Hm o) (sub_nat_rel_canonical 1)).
  Qed.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Definition src_nonpreemptive_segments_bounded_by_blocking : Prop :=
    ltac:(body_of (fun s : S.statement_nonpreemptive_segments_bounded_by_blocking => s Task mR Job jtR costR)).
  Definition tgt_nonpreemptive_segments_bounded_by_blocking : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BlockingBound_Fp_nonpreemptive_segments_bounded_by_blocking
      Job dJ Task dT mL jtL costL)).

  Theorem nonpreemptive_segments_bounded_by_blocking_correspondence :
    PropSPropRel src_nonpreemptive_segments_bounded_by_blocking tgt_nonpreemptive_segments_bounded_by_blocking.
  Proof.
    unfold src_nonpreemptive_segments_bounded_by_blocking, tgt_nonpreemptive_segments_bounded_by_blocking.
    apply (isj_cover_pstate Job). intros PR PL X.
    apply (bbfp_forall_fp Task). intros fR fL Hf.
    apply (fpre_forall_arr Job). intros arrR arrL Harr.
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    apply fpre_forall_jp. intros jpR jpL Hjp.
    imp (ar_and_correspondence _ _ _ _
      (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp)
      (model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt costR costL Hcost
        mR mL Hm jpR jpL Hjp arrR arrL Harr)).
    apply bbfp_forall_list. intros tsR tsL Hts.
    apply ar_imp_correspondence.
    { unfold prosa.model.task.concept.all_jobs_from_taskset.
      cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
      apply ar_forall_identity_correspondence. intro j.
      imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      exact (ar_bool_truth_correspondence _ _ (isj_lean_transport
        (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j \in tsR)
          (ar_target_decide_mem Task v tsL)) _ _ (Hjt j)
        (ar_decide_mem_related Task (@prosa.model.task.concept.job_task Job Task jtR j) _ _ Hts))). }
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_identity_correspondence. intro j.
    imp (ar_bool_truth_correspondence _ _ (pi_job_of_task_related Task Job jtR jtL Hjt tsk j)).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (sub_nat_le_correspondence _ _ _ _
      (max_lp_nonpreemptive_segment_correspondence Job costR costL Hcost arrR arrL Harr _ _
        (bbfp_fp_jlfp_rel fR fL Hf) jpR jpL Hjp j _ _ Ht)
      (bbfp_blocking_bound_related fR fL Hf tsR tsL Hts tsk)).
  Qed.
End BlockingFp.
