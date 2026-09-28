From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import BlockingBoundEdfFactsSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes model.job.properties
  model.priority.edf model.task.absolute_deadline model.task.arrival.curves.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBlockingBoundEdfFacts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers
  TaskPreemptionParametersCorrespondence BusyIntervalPiHelpers CurvesCorrespondence
  BlockingBoundEdfCorrespondence.

Module I := ImportedBlockingBoundEdfFacts.
Module S := BlockingBoundEdfFactsSemanticSource.BlockingBoundEdfFactsSemanticSource.
Module TPS := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module BBE := BlockingBoundEdfSemanticSource.BlockingBoundEdfSemanticSource.

(** Statement correspondence for [analysis/facts/blocking_bound/edf.v].

    Source side: the extracted statement specialised at its leading inputs
    (task and job types, task cost, maximum arrivals, task deadlines,
    task-level maximum nonpreemptive segment, the job-task, cost and arrival
    classes); target side: the imported Lean theorem type.  Inputs: task
    costs, maximum arrivals and task deadlines pointwise by [SubNatRel],
    [TaskMaxNonpreemptiveSegment] by the accepted [TppMaxSegmentRel],
    [job_task] by [Lean.eq], [job_cost] by the accepted [SvcJobCostRel],
    [job_arrival] by [ArJobArrivalRel].  Inputs quantified inside the
    statement are covered in both directions: processor models, schedules,
    arrival sequences and [JobPreemptable] instances by the accepted
    conversions of the busy-interval family, task sets
    ([bbe_forall_list]), tasks and jobs (identity) and instants.  The EDF
    policy over task-deadline-derived absolute deadlines is related through
    the deadline relation ([bbe_edf_rel]); the EDF blocking bound is the
    accepted blocking-bound certificate; arrival-curve conformance is the
    accepted arrival-curve certificate; the maximum lower-priority
    nonpreemptive segment is the accepted [pi] definition certificate.  No
    source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma bbe_forall_list (T : Type) (PRl : seq T -> Prop) (PLl : I.List T -> SProp) :
  (forall xsR xsL, ArListRel xsR xsL -> PropSPropRel (PRl xsR) (PLl xsL)) ->
  PropSPropRel (forall xs, PRl xs) (forall xs, PLl xs).
Proof.
  apply (isj_forall_cover_sprop _ _ ArListRel ar_list_to_imported ar_list_to_rocq).
  - intro xs. exact (@Lean.eq_refl _ _).
  - intro xs. exact (ar_list_target_roundtrip xs).
Qed.

Section BlockingEdf.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.

  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : forall (tsk : Task) (nR : nat) (nL : Lean.Nat), SubNatRel nR nL ->
    SubNatRel (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk nR)
      (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk nL).
  Variable tdR : prosa.model.task.concept.TaskDeadline Task.
  Variable tdL : I.Prosa_Model_Task_Concept_TaskDeadline Task dT.
  Hypothesis Htd : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR tsk)
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL tsk).
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
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

  Let DLR := @prosa.model.task.absolute_deadline.job_deadline_from_task_deadline Job Task tdR jaR jtR.
  Let DLL := I.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task dJ dT tdL jaL jtL.

  Lemma bbe_task_deadline_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (isj_lean_transport (fun v => SubNatRel
      (@prosa.model.task.concept.task_deadline Task tdR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL v)) _ _ (Hjt j) (Htd _)).
  Qed.

  Lemma bbe_deadline_related (j : Job) :
    SubNatRel (@prosa.behavior.job.job_deadline Job DLR j) (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ DLL j).
  Proof.
    exact (svc_target_add_related _ _ _ _ (Hja j) (bbe_task_deadline_of_job_related j)).
  Qed.

  Lemma bbe_edf_rel :
    FpreJLFPRel Job (@prosa.model.priority.edf.EDF Job DLR) (I.Prosa_Model_Priority_Edf_EDF Job dJ DLL).
  Proof.
    intros x y.
    exact (svc_decide_le_related _ _ _ _ (bbe_deadline_related x) (bbe_deadline_related y)).
  Qed.

  Lemma bbe_task_cost_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (isj_lean_transport (fun v => SubNatRel
      (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)).
  Qed.

  Lemma bbe_valid_job_costs_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) :
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
  Proof.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs, prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs I.Prosa_Model_Task_Concept_valid_job_cost].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (ar_bool_truth_correspondence _ _ (svc_decide_le_related _ _ _ _ (Hcost j) (bbe_task_cost_of_job_related j))).
  Qed.

  Lemma bbe_taskset_respects_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) tsR tsL (Hts : ArListRel tsR tsL) :
    PropSPropRel (@prosa.model.task.arrival.curves.taskset_respects_max_arrivals Task Job jtR arrR maR tsR)
      (I.Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task dT Job dJ jtL arrL maL tsL).
  Proof.
    unfold prosa.model.task.arrival.curves.taskset_respects_max_arrivals.
    cbn [I.Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    exact (respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsk _ _ (Hma tsk)).
  Qed.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Definition src_nonpreemptive_segments_bounded_by_blocking : Prop :=
    ltac:(body_of (fun s : S.statement_nonpreemptive_segments_bounded_by_blocking =>
      s Task tcR maR tdR mR Job jtR costR jaR)).
  Definition tgt_nonpreemptive_segments_bounded_by_blocking : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BlockingBound_Edf_nonpreemptive_segments_bounded_by_blocking
      Job dJ Task dT tcL maL tdL mL jtL costL jaL)).

  Theorem nonpreemptive_segments_bounded_by_blocking_correspondence :
    PropSPropRel src_nonpreemptive_segments_bounded_by_blocking tgt_nonpreemptive_segments_bounded_by_blocking.
  Proof.
    unfold src_nonpreemptive_segments_bounded_by_blocking, tgt_nonpreemptive_segments_bounded_by_blocking.
    apply (isj_cover_pstate Job). intros PR PL X.
    apply (fpre_forall_arr Job). intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    imp (bbe_valid_job_costs_rel arrR arrL Harr).
    apply fpre_forall_jp. intros jpR jpL Hjp.
    imp (ar_and_correspondence _ _ _ _
      (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp)
      (model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt costR costL Hcost
        mR mL Hm jpR jpL Hjp arrR arrL Harr)).
    apply bbe_forall_list. intros tsR tsL Hts.
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
    imp (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    imp (bbe_taskset_respects_rel arrR arrL Harr tsR tsL Hts).
    apply ar_forall_identity_correspondence. intro j.
    imp (ar_bool_truth_correspondence _ _ (pi_job_of_task_related Task Job jtR jtL Hjt tsk j)).
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
      arrR arrL Harr _ _ bbe_edf_rel j _ _ _ _ Ht1 Ht2).
    exact (sub_nat_le_correspondence _ _ _ _
      (max_lp_nonpreemptive_segment_correspondence Job costR costL Hcost arrR arrL Harr _ _ bbe_edf_rel
        jpR jpL Hjp j _ _ Ht1)
      (blocking_bound_correspondence Task tcR tcL Htc maR maL Hma tdR tdL Htd mR mL Hm tsR tsL Hts tsk _ _
        (svc_target_sub_related _ _ _ _ (Hja j) Ht1))).
  Qed.
End BlockingEdf.
