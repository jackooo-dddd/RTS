From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsReadinessInterferenceSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsReadinessInterference ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations
  JitterSvcJobOperations PreemptionParameterCorrespondence ServiceInversionPredCorrespondence
  AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations AbstractDefinitionsArrivalOperations
  AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations
  AbstractDefinitionsOperations AbstractDefinitionsSums AbstractDefinitionsLogical ServiceIntervalOperations
  ServiceScheduleOperations AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations
  AbstractDefinitionsBusyIntervalHelpers AbstractDefinitionsBusyInterval PriorityBaseAdapter
  ReadinessInterferenceCorrespondence ReadinessAwareCorrespondence ArrivalsCorrespondence InterferenceCorrespondence.

Module I := ImportedFactsReadinessInterference.
Module S := FactsReadinessInterferenceSemanticSource.FactsReadinessInterferenceSemanticSource.
Module JS := FoundationCertificates.JitterSvcScheduleOperations.
Module SS := FoundationCertificates.ServiceScheduleOperations.

(** Statement certificates for [analysis/facts/readiness_interference.v]: for
    related processor states and schedules (the accepted two-sided Service
    relations of both certificate generations over the same state pair),
    job-arrival, job-cost and readiness instances and arrival sequences (the
    accepted relations, each with two-way totals), each extracted source
    statement (the authoritative elaborated type, specialised at these
    inputs) and the imported Lean theorem type are related; the JLFP policy
    quantified inside the first statement is covered in both directions by the
    accepted import/export maps; jobs are an identity carrier and instants are
    related by [SubNatRel].  The readiness, interference and readiness-aware
    service-inversion predicates go through the accepted correspondences. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section FactsReadinessInterference.
  Context (Job : eqType).
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable Rs : SS.SvcProcessorStateRel Job PStateR PStateL.
  Variable Rj : JS.SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis HschedS : SS.SvcScheduleRel Job PStateR PStateL Rs schedR schedL.
  Hypothesis HschedJ : JS.SvcScheduleRel Job PStateR PStateL Rj schedR schedL.
  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Harrival : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job arrivalR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ arrivalL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).
  Variable readyR : @prosa.behavior.ready.JobReady Job PStateR costR arrivalR.
  Variable readyL : I.Prosa_Behavior_Ready_JobReady Job dJ PStateL costL arrivalL.
  Hypothesis Hready : forall j tR tL, SubNatRel tR tL ->
    ArBoolRel (@prosa.behavior.ready.job_ready Job PStateR costR arrivalR readyR schedR j tR)
      (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PStateL costL arrivalL readyL schedL j tL).
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma fri_scheduled_related (j : Job) tR tL : SubNatRel tR tL ->
    ArBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL).
  Proof. intro Ht. exact (JS.svc_scheduled_in_related Job PStateR PStateL Rj j _ _ (HschedJ tR tL Ht)). Qed.

  Lemma fri_valid_schedule_related :
    PropSPropRel (@prosa.behavior.ready.valid_schedule Job arrivalR PStateR schedR costR readyR arrR)
      (I.Prosa_Behavior_Ready_valid_schedule Job dJ arrivalL PStateL schedL costL readyL arrL).
  Proof.
    unfold prosa.behavior.ready.valid_schedule, prosa.behavior.ready.jobs_must_be_ready_to_execute,
      prosa.behavior.ready.jobs_come_from_arrival_sequence.
    cbn [I.Prosa_Behavior_Ready_valid_schedule I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute
      I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence].
    apply ar_and_correspondence.
    - apply ar_forall_identity_correspondence; intro j.
      apply ar_forall_nat_correspondence; intros tR tL Ht.
      apply ar_imp_correspondence.
      + exact (ar_bool_truth_correspondence _ _ (fri_scheduled_related j tR tL Ht)).
      + exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    - apply ar_forall_identity_correspondence; intro j.
      apply ar_forall_nat_correspondence; intros tR tL Ht.
      apply ar_imp_correspondence.
      + exact (ar_bool_truth_correspondence _ _ (fri_scheduled_related j tR tL Ht)).
      + exact (ar_bool_truth_correspondence _ _ (Hready j tR tL Ht)).
  Qed.

  Lemma fri_forall_jlfp (PR : prosa.model.priority.definitions.JLFP_policy Job -> Prop)
      (PL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ -> SProp) :
    (forall pR pL, PdJLFPRel Job pR pL -> PropSPropRel (PR pR) (PL pL)) ->
    PropSPropRel (forall pR, PR pR) (forall pL, PL pL).
  Proof.
    intro H. apply prop_sprop_rel_intro.
    - intros HR pL. exact (prop_to_sprop _ _ (H _ _ (pd_jlfp_export_certificate Job pL)) (HR (pd_export_jlfp Job pL))).
    - intro HL. apply strictly_inhabits. intro pR.
      exact (sprop_to_prop _ _ (H _ _ (pd_jlfp_import_certificate Job pR)) (HL (pd_import_jlfp Job pR))).
  Qed.

  Section Policy.
    Variable jlfpR : prosa.model.priority.definitions.JLFP_policy Job.
    Variable jlfpL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
    Hypothesis Hjlfp : PdJLFPRel Job jlfpR jlfpL.

    Lemma fri_some_hep_job_ready_related (j : Job) tR tL : SubNatRel tR tL ->
      ArBoolRel (@prosa.analysis.definitions.readiness_interference.some_hep_job_ready Job arrivalR costR PStateR
          readyR arrR schedR jlfpR j tR)
        (I.Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready Job dJ arrivalL costL PStateL
          readyL arrL schedL jlfpL j tL).
    Proof.
      exact (some_hep_job_ready_correspondence Job PStateR PStateL schedR schedL arrivalR arrivalL costR costL
        readyR readyL Hready arrR arrL Harr jlfpR jlfpL Hjlfp j tR tL).
    Qed.
  End Policy.

  Definition src_no_hep_ready_implies_no_another_hep_interference : Prop :=
    ltac:(body_of (fun s : S.statement_no_hep_ready_implies_no_another_hep_interference =>
      s Job arrivalR costR PStateR readyR arrR schedR)).
  Definition tgt_no_hep_ready_implies_no_another_hep_interference : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_ReadinessInterference_no_hep_ready_implies_no_another_hep_interference
      Job dJ arrivalL costL PStateL readyL arrL schedL)).
  Theorem no_hep_ready_implies_no_another_hep_interference_correspondence :
    PropSPropRel src_no_hep_ready_implies_no_another_hep_interference
      tgt_no_hep_ready_implies_no_another_hep_interference.
  Proof.
    unfold src_no_hep_ready_implies_no_another_hep_interference, tgt_no_hep_ready_implies_no_another_hep_interference.
    apply ar_imp_correspondence; [exact fri_valid_schedule_related|].
    apply fri_forall_jlfp; intros pR pL Hp.
    apply ar_forall_identity_correspondence; intro j.
    apply ar_forall_nat_correspondence; intros tR tL Ht.
    apply ar_imp_correspondence.
    - exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (fri_some_hep_job_ready_related pR pL Hp j tR tL Ht))).
    - exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (another_hep_job_interference_correspondence Job PStateR PStateL Rj schedR schedL HschedJ
          arrR arrL Harr pR pL Hp j tR tL Ht))).
  Qed.

  Section Policy2.
    Variable jlfpR : prosa.model.priority.definitions.JLFP_policy Job.
    Variable jlfpL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
    Hypothesis Hjlfp : PdJLFPRel Job jlfpR jlfpL.

    Definition src_no_hep_ready_implies_no_service_inversion : Prop :=
      ltac:(body_of (fun s : S.statement_no_hep_ready_implies_no_service_inversion =>
        s Job arrivalR costR PStateR readyR arrR schedR jlfpR)).
    Definition tgt_no_hep_ready_implies_no_service_inversion : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_ReadinessInterference_no_hep_ready_implies_no_service_inversion
        Job dJ arrivalL costL PStateL readyL arrL schedL jlfpL)).
    Theorem no_hep_ready_implies_no_service_inversion_correspondence :
      PropSPropRel src_no_hep_ready_implies_no_service_inversion tgt_no_hep_ready_implies_no_service_inversion.
    Proof.
      unfold src_no_hep_ready_implies_no_service_inversion, tgt_no_hep_ready_implies_no_service_inversion.
      apply ar_forall_identity_correspondence; intro j.
      apply ar_forall_nat_correspondence; intros tR tL Ht.
      apply ar_imp_correspondence.
      - exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
          (fri_some_hep_job_ready_related jlfpR jlfpL Hjlfp j tR tL Ht))).
      - exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
          (ReadinessAwareCorrespondence.service_inversion_correspondence Job PStateR PStateL Rj schedR schedL
            HschedJ arrivalR arrivalL costR costL readyR readyL Hready arrR arrL Harr jlfpR jlfpL Hjlfp j tR tL Ht))).
    Qed.
  End Policy2.
End FactsReadinessInterference.
