From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import LowerBoundOnServiceSemanticSource.
From prosa Require Import analysis.abstract.definitions model.job.properties
  model.processor.platform_properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedLowerBoundOnService ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  WorkloadCorrespondence
  AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations
  AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations
  AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums
  AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations
  AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations
  AbstractDefinitionsBusyIntervalHelpers.

Module I := ImportedLowerBoundOnService.
Module S := LowerBoundOnServiceSemanticSource.LowerBoundOnServiceSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.

(** Statement correspondences for [analysis/abstract/lower_bound_on_service.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.
    Inputs: processor states by the accepted two-sided [SvcProcessorStateRel]
    of the abstract-definitions family and schedules through it;
    [job_arrival] and [job_cost] pointwise by [SubNatRel]; [JobTask] by the
    accepted [AdJobTaskRel]; arrival sequences by the accepted
    [ArArrivalSequenceRel] (the abstract family's [AdArrivalSequenceRel] is
    the same relation, obtained by conversion); [Interference] and
    [InterferingWorkload] by the accepted abstract relations; jobs identity,
    instants and durations by [SubNatRel].  The inner binders (jobs,
    instants, durations) are covered by the accepted identity and natural
    number combinators.  The abstract busy-interval notions and
    [work_conserving] are related by the accepted abstract-definitions
    certificates, service and interference by the accepted service and
    abstract-sum certificates.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma lbs_add_related (aR : nat) (aL : Lean.Nat) (bR : nat) (bL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Section LowerBoundOnService.
  Context (Task Job : eqType).
  Let dT := ad_decidable_eq Task.
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SSO.SvcProcessorStateRel Job PStateR PStateL.

  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : AdJobTaskRel Job Task jtR jtL.
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

  Lemma lbs_cost_positive_related (j : Job) :
    SvcBoolRel (@prosa.model.job.properties.job_cost_positive Job costR j)
      (I.Prosa_Model_Job_Properties_job_cost_positive Job dJ costL j).
  Proof.
    unfold prosa.model.job.properties.job_cost_positive.
    exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost j)).
  Qed.

  Lemma lbs_unit_service_rel :
    PropSPropRel (@prosa.model.processor.platform_properties.unit_service_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.unit_service_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model].
    apply ad_forall_identity_correspondence. intro j.
    apply prop_sprop_rel_intro.
    - intros HR sL.
      have Hs := SSO.svc_ps_state_rel_surjective Job PStateR PStateL R sL.
      exact (prop_to_sprop _ _ (sub_nat_le_correspondence _ _ _ _
        (SSO.svc_service_in_related Job PStateR PStateL R j _ _ Hs) (sub_nat_rel_canonical 1)) (HR _)).
    - intro HL. apply strictly_inhabits. intro sR.
      have Hs := SSO.svc_ps_state_rel_canonical Job PStateR PStateL R sR.
      exact (sprop_to_prop _ _ (sub_nat_le_correspondence _ _ _ _
        (SSO.svc_service_in_related Job PStateR PStateL R j _ _ Hs) (sub_nat_rel_canonical 1)) (HL _)).
  Qed.

  Variable interR : prosa.analysis.abstract.definitions.Interference Job.
  Variable interL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ.
  Hypothesis Hinter : AdInterferenceRel Job interR interL.
  Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
  Variable workloadL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ.
  Hypothesis Hworkload : AdInterferingWorkloadRel Job workloadR workloadL.
  Variable sR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable sL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let BIP j t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :=
    ad_busy_interval_prefix_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
      interR interL Hinter workloadR workloadL Hworkload j t1R t2R t1L t2L H1 H2.
  Let BI j t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :=
    ad_busy_interval_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
      interR interL Hinter workloadR workloadL Hworkload j t1R t2R t1L t2L H1 H2.

  Lemma lbs_arr_ad : AdArrivalSequenceRel Job arrR arrL.
  Proof. exact Harr. Qed.

  Let WC := ad_work_conserving_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
    interR interL Hinter workloadR workloadL Hworkload arrR arrL lbs_arr_ad.

  (** *** interference_is_complement_to_schedule *)

  Definition src_interference_is_complement_to_schedule (tsk : Task) : Prop :=
    ltac:(body_of (fun s : S.statement_interference_is_complement_to_schedule =>
      s Task Job jtR jaR costR PStateR arrR sR tsk interR workloadR)).
  Definition tgt_interference_is_complement_to_schedule (tsk : Task) : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_LowerBoundOnService_interference_is_complement_to_schedule
      Task dT Job dJ jtL jaL costL PStateL arrL sL tsk interL workloadL)).

  Theorem interference_is_complement_to_schedule_correspondence (tsk : Task) :
    PropSPropRel (src_interference_is_complement_to_schedule tsk)
      (tgt_interference_is_complement_to_schedule tsk).
  Proof.
    unfold src_interference_is_complement_to_schedule, tgt_interference_is_complement_to_schedule.
    apply ad_imp_correspondence; [exact WC|].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j lbs_arr_ad)|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (lbs_cost_positive_related j))|].
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    apply ad_imp_correspondence; [exact (BIP j _ _ _ _ H1 H2)|].
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_forall_nat_correspondence. intros dR dL Hd.
    have Hend := lbs_add_related _ _ _ _ Ht Hd.
    apply ad_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 Ht)|].
    apply ad_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hend H2)|].
    exact (sub_nat_le_correspondence _ _ _ _ Hd
      (lbs_add_related _ _ _ _ (ad_service_during_related Job PStateR PStateL R sR sL Hs j _ _ _ _ Ht Hend)
        (cumulative_interference_correspondence Job interR interL j _ _ _ _ Hinter Ht Hend))).
  Qed.

  (** *** service_and_interference_bounded *)

  Definition src_service_and_interference_bounded (tsk : Task) : Prop :=
    ltac:(body_of (fun s : S.statement_service_and_interference_bounded =>
      s Task Job jtR jaR costR PStateR arrR sR tsk interR workloadR)).
  Definition tgt_service_and_interference_bounded (tsk : Task) : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_LowerBoundOnService_service_and_interference_bounded
      Task dT Job dJ jtL jaL costL PStateL arrL sL tsk interL workloadL)).

  Theorem service_and_interference_bounded_correspondence (tsk : Task) :
    PropSPropRel (src_service_and_interference_bounded tsk)
      (tgt_service_and_interference_bounded tsk).
  Proof.
    unfold src_service_and_interference_bounded, tgt_service_and_interference_bounded.
    apply ad_imp_correspondence; [exact WC|].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j lbs_arr_ad)|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (lbs_cost_positive_related j))|].
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    apply ad_imp_correspondence; [exact (BIP j _ _ _ _ H1 H2)|].
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_forall_nat_correspondence. intros dR dL Hd.
    have Hend := lbs_add_related _ _ _ _ Ht Hd.
    apply ad_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 Ht)|].
    apply ad_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hend H2)|].
    apply ad_imp_correspondence; [exact lbs_unit_service_rel|].
    exact (sub_nat_le_correspondence _ _ _ _
      (lbs_add_related _ _ _ _ (ad_service_during_related Job PStateR PStateL R sR sL Hs j _ _ _ _ Ht Hend)
        (cumulative_interference_correspondence Job interR interL j _ _ _ _ Hinter Ht Hend)) Hd).
  Qed.

  (** *** j_receives_enough_service *)

  Definition src_j_receives_enough_service (tsk : Task) : Prop :=
    ltac:(body_of (fun s : S.statement_j_receives_enough_service =>
      s Task Job jtR jaR costR PStateR arrR sR tsk interR workloadR)).
  Definition tgt_j_receives_enough_service (tsk : Task) : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_LowerBoundOnService_j_receives_enough_service
      Task dT Job dJ jtL jaL costL PStateL arrL sL tsk interL workloadL)).

  Theorem j_receives_enough_service_correspondence (tsk : Task) :
    PropSPropRel (src_j_receives_enough_service tsk) (tgt_j_receives_enough_service tsk).
  Proof.
    unfold src_j_receives_enough_service, tgt_j_receives_enough_service.
    apply ad_imp_correspondence; [exact WC|].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j lbs_arr_ad)|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (lbs_cost_positive_related j))|].
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    apply ad_imp_correspondence; [exact (BI j _ _ _ _ H1 H2)|].
    apply ad_forall_nat_correspondence. intros pR pL Hp.
    apply ad_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hp (Hcost j))|].
    apply ad_forall_nat_correspondence. intros dR dL Hd.
    have Hend := lbs_add_related _ _ _ _ H1 Hd.
    apply ad_imp_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _
        (lbs_add_related _ _ _ _ Hp (cumulative_interference_correspondence Job interR interL j _ _ _ _ Hinter H1 Hend))
        Hd)|].
    exact (sub_nat_le_correspondence _ _ _ _ Hp
      (ad_service_related Job PStateR PStateL R sR sL Hs j _ _ Hend)).
  Qed.
End LowerBoundOnService.
