From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import BoundedBiAuxSemanticSource.
From prosa Require Import analysis.abstract.definitions model.job.properties
  model.processor.platform_properties model.processor.supply
  model.aggregate.workload model.aggregate.service_of_jobs.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBoundedBiAux ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  WorkloadCorrespondence
  AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations
  AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations
  AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums
  AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations
  AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations
  AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers IdealAbstractRtaHelpers.
From FoundationCertificates Require
  SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations
  SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskPreemptionParametersCorrespondence SequentialityCorrespondence
  IbfTaskHelpers IbfSupplyTaskCorrespondence ServiceInversionPredCorrespondence
  InterferenceCorrespondence ServiceOfJobsCorrespondence.
From FoundationCertificates Require Import IbfTaskFullHelpers RsIwHelpers.

Module I := ImportedBoundedBiAux.
Module S := BoundedBiAuxSemanticSource.BoundedBiAuxSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module SUP := FoundationCertificates.SupplyScheduleOperations.
Module SOJ := FoundationCertificates.ServiceOfJobsCorrespondence.

(** Statement correspondences for
    [analysis/abstract/restricted_supply/bounded_bi/aux.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (job type, [job_arrival], [job_cost], a leading
    processor state); target side: the imported Lean theorem types.  Inputs:
    [job_arrival] and [job_cost] pointwise; the processor state by the
    accepted two-sided [SvcProcessorStateRel] together with the pointwise
    [supply_on] relation, from which the accepted restricted-supply family
    relations are built.  JLFP policies (pointwise on Booleans), arrival
    sequences, schedules, readiness instances (on the statement's schedule
    pair), jobs and instants are covered in both directions by the accepted
    covers of the restricted-supply instantiation certificate (helper-only
    copy [RsIwHelpers]).

    The source's two section-local instances re-expose the accepted
    restricted-supply instantiation; they are related to the accepted Lean
    definitions by the accepted [rsi_interference_rel]/[rsi_workload_rel]
    (the local instances unfold to them).  The processor-model hypotheses,
    schedule validity, the classical busy-interval prefix, abstract work
    conservation, the cumulative interfering workload, the hep workload and
    service, the job workload and [job_cost_positive] are the accepted
    certificates re-instantiated at this artifact.  No source or target
    theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section BoundedBiAux.
  Context (Job : eqType).
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SSO.SvcProcessorStateRel Job PStateR PStateL.
  Hypothesis Hsupply_on : forall sR sL cR,
    SSO.svc_ps_state_rel Job PStateR PStateL R sR sL ->
    SubNatRel (@prosa.behavior.schedule.supply_on Job PStateR sR cR)
      (SUP.supply_target_supply_on Job PStateL sL (SSO.svc_ps_core_to_target Job PStateR PStateL R cR)).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).

  Local Ltac imp H := apply ad_imp_correspondence; [exact H|].

  Let UNI := ibt_uni Job PStateR PStateL R.
  Let USUP := rsi_unit_supply_rel Job PStateR PStateL R Hsupply_on.
  Let CONS := rsi_fully_consuming_rel Job PStateR PStateL R Hsupply_on.

  Lemma bbaux_cost_positive_related (j : Job) :
    PropSPropRel (is_true (@prosa.model.job.properties.job_cost_positive Job costR j))
      (Lean.eq (I.Prosa_Model_Job_Properties_job_cost_positive Job dJ costL j) I.Bool_true).
  Proof. exact (ar_bool_truth_correspondence _ _ (arta_cost_positive_related Job costR costL Hcost j)). Qed.

  Lemma bbaux_succ_related (aR : nat) (aL : Lean.Nat) (Ha : SubNatRel aR aL) :
    SubNatRel aR.+1 (svc_target_add aL (sub_nat_to_imported 1)).
  Proof.
    have H := svc_target_add_related _ _ _ _ Ha (sub_nat_rel_canonical 1).
    rewrite addn1 in H. exact H.
  Qed.

  (** *** busy_interval_prefix_exists *)

  Definition src_busy_interval_prefix_exists : Prop :=
    ltac:(body_of (fun s : S.statement_busy_interval_prefix_exists => s Job jaR costR PStateR)).
  Definition tgt_busy_interval_prefix_exists : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_RestrictedSupply_BoundedBi_Auxiliary_busy_interval_prefix_exists
      Job dJ jaL costL PStateL)).
  Theorem busy_interval_prefix_exists_correspondence :
    PropSPropRel src_busy_interval_prefix_exists tgt_busy_interval_prefix_exists.
  Proof.
    unfold src_busy_interval_prefix_exists, tgt_busy_interval_prefix_exists.
    imp UNI. imp USUP. imp CONS.
    apply (rsi_forall_jlfp Job). intros pR pL Hp.
    imp (rsi_reflexive_rel Job pR pL Hp).
    apply (rsi_forall_arr Job). intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply (rsi_forall_sched Job PStateR PStateL R). intros sR sL Hs.
    apply (rsi_forall_jr Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs). intros jrR jrL Hjr.
    imp (rsi_valid_schedule_rel Job PStateR PStateL R jaR jaL costR costL sR sL Hs arrR arrL Harr jrR jrL Hjr).
    apply ad_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (bbaux_cost_positive_related j).
    apply ad_exists_nat_correspondence. intros t1R t1L Ht1.
    apply ar_and_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht1 (Hja j))|].
    exact (rsi_busy_interval_prefix_related Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs
      arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 (bbaux_succ_related _ _ (Hja j))).
  Qed.

  (** *** service_lt_workload_in_busy *)

  Definition src_service_lt_workload_in_busy : Prop :=
    ltac:(body_of (fun s : S.statement_service_lt_workload_in_busy => s Job jaR costR PStateR)).
  Definition tgt_service_lt_workload_in_busy : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_RestrictedSupply_BoundedBi_Auxiliary_service_lt_workload_in_busy
      Job dJ jaL costL PStateL)).
  Theorem service_lt_workload_in_busy_correspondence :
    PropSPropRel src_service_lt_workload_in_busy tgt_service_lt_workload_in_busy.
  Proof.
    unfold src_service_lt_workload_in_busy, tgt_service_lt_workload_in_busy.
    imp USUP.
    apply (rsi_forall_jlfp Job). intros pR pL Hp.
    apply (rsi_forall_arr Job). intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply (rsi_forall_sched Job PStateR PStateL R). intros sR sL Hs.
    apply (rsi_forall_jr Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs). intros jrR jrL Hjr.
    imp (rsi_valid_schedule_rel Job PStateR PStateL R jaR jaL costR costL sR sL Hs arrR arrL Harr jrR jrL Hjr).
    apply ad_forall_identity_correspondence. intro j.
    imp (bbaux_cost_positive_related j).
    apply ad_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ad_forall_nat_correspondence. intros t2R t2L Ht2.
    imp (rsi_busy_interval_prefix_related Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs
      arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2).
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_lt_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _ Ht Ht2))).
    exact (sub_nat_lt_correspondence _ _ _ _
      (SOJ.service_of_hep_jobs_correspondence Job PStateR PStateL (rsi_jsvc Job PStateR PStateL R) sR sL
        (rsi_hs_jsvc Job PStateR PStateL R sR sL Hs) pR pL Hp arrR arrL Harr j _ _ _ _ Ht1 Ht)
      (workload_of_hep_jobs_correspondence Job costR costL Hcost arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht)).
  Qed.

  (** *** workload_exceeds_interval *)

  Definition src_workload_exceeds_interval : Prop :=
    ltac:(body_of (fun s : S.statement_workload_exceeds_interval => s Job jaR costR PStateR)).
  Definition tgt_workload_exceeds_interval : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_RestrictedSupply_BoundedBi_Auxiliary_workload_exceeds_interval
      Job dJ jaL costL PStateL)).
  Theorem workload_exceeds_interval_correspondence :
    PropSPropRel src_workload_exceeds_interval tgt_workload_exceeds_interval.
  Proof.
    unfold src_workload_exceeds_interval, tgt_workload_exceeds_interval.
    imp UNI. imp USUP. imp CONS.
    apply (rsi_forall_jlfp Job). intros pR pL Hp.
    imp (rsi_reflexive_rel Job pR pL Hp).
    apply (rsi_forall_arr Job). intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply (rsi_forall_sched Job PStateR PStateL R). intros sR sL Hs.
    apply (rsi_forall_jr Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs). intros jrR jrL Hjr.
    imp (rsi_valid_schedule_rel Job PStateR PStateL R jaR jaL costR costL sR sL Hs arrR arrL Harr jrR jrL Hjr).
    have HI := rsi_interference_rel Job PStateR PStateL R Hsupply_on sR sL Hs arrR arrL Harr pR pL Hp.
    have HW := rsi_workload_rel Job PStateR PStateL R Hsupply_on costR costL Hcost sR sL Hs arrR arrL Harr pR pL Hp.
    imp (ad_work_conserving_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
      _ _ HI _ _ HW arrR arrL Harr).
    apply ad_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (bbaux_cost_positive_related j).
    apply ad_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ad_forall_nat_correspondence. intros t2R t2L Ht2.
    imp (rsi_busy_interval_prefix_related Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs
      arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2).
    apply ad_forall_nat_correspondence. intros dR dL Hd.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd).
    have Hend := svc_target_add_related _ _ _ _ Ht1 Hd.
    imp (sub_nat_lt_correspondence _ _ _ _ Hend Ht2).
    exact (sub_nat_lt_correspondence _ _ _ _ Hd
      (svc_target_add_related _ _ _ _
        (workload_of_job_correspondence Job costR costL Hcost arrR arrL Harr j _ _ _ _ Ht1 Hend)
        (cumulative_interfering_workload_correspondence Job _ _ HW j _ _ _ _ Ht1 Hend))).
  Qed.
End BoundedBiAux.
