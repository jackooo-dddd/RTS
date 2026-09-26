From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import PrioAwareSemanticSource.
From prosa Require Import model.processor.ideal model.schedule.work_conserving
  implementation.definitions.generic_scheduler.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPrioAware ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  IdealUniSchedulerCorrespondence PreemptionAwareHelpers.

Module I := ImportedPrioAware.
Module S := PrioAwareSemanticSource.PrioAwareSemanticSource.
Module U := IdealUniSchedulerSemanticSource.IdealUniSchedulerSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module RS := ReadinessSemanticSource.ReadinessSemanticSource.
Module LP := ScheduleLimitedPreemptiveSemanticSource.ScheduleLimitedPreemptiveSemanticSource.
Module PD := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.

(** Statement correspondences for [implementation/facts/ideal_uni/prio_aware.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.  The
    processor model is fixed to the ideal uniprocessor on both sides, with the
    relations and covers of the accepted preemption-aware certificate
    (re-bound here as [PreemptionAwareHelpers]): states by the
    constructor-preserving Option map, schedules pointwise, [job_cost] by
    [SvcJobCostRel], [job_arrival] by [ArJobArrivalRel], arrival sequences by
    [ArArrivalSequenceRel], readiness models by [job_ready] on related
    schedules and instants (covered among nonclairvoyant models), preemption
    models pointwise.  JLDP policies are related pointwise on Booleans and
    covered in both directions by explicit conversions.  The priority-aware
    scheduler and [choose_highest_prio_job] are related by the accepted
    scheduler certificate.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section PrioAware.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.

  (** *** JLDP-policy covers *)

  Definition PrJldpRel (hpR : prosa.model.priority.definitions.JLDP_policy Job)
      (hpL : I.Prosa_Model_Priority_Definitions_JLDP_policy Job dJ) : SProp :=
    forall tR tL, SubNatRel tR tL -> forall x y : Job,
      SvcBoolRel (@prosa.model.priority.definitions.hep_job_at Job hpR tR x y)
        (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job dJ hpL tL x y).

  Definition pr_jldp_to_target (hpR : prosa.model.priority.definitions.JLDP_policy Job) :
      I.Prosa_Model_Priority_Definitions_JLDP_policy Job dJ :=
    I.Prosa_Model_Priority_Definitions_JLDP_policy_mk Job dJ
      (fun tL x y => svc_bool_to_imported
        (@prosa.model.priority.definitions.hep_job_at Job hpR (sub_nat_to_rocq tL) x y)).

  Definition pr_jldp_to_source (hpL : I.Prosa_Model_Priority_Definitions_JLDP_policy Job dJ) :
      prosa.model.priority.definitions.JLDP_policy Job :=
    ((fun tR x y => svc_bool_to_rocq
      (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job dJ hpL (sub_nat_to_imported tR) x y))
      : prosa.model.priority.definitions.JLDP_policy Job).

  Lemma pr_jldp_to_target_rel hpR : PrJldpRel hpR (pr_jldp_to_target hpR).
  Proof.
    intros tR tL Ht x y.
    change (Lean.eq (svc_bool_to_imported (@prosa.model.priority.definitions.hep_job_at Job hpR tR x y))
      (svc_bool_to_imported (@prosa.model.priority.definitions.hep_job_at Job hpR (sub_nat_to_rocq tL) x y))).
    rewrite (id_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma pr_jldp_to_source_rel hpL : PrJldpRel (pr_jldp_to_source hpL) hpL.
  Proof.
    intros tR tL Ht x y.
    refine (sub_imported_eq_trans _ _ _ (svc_bool_target_roundtrip _) _).
    destruct Ht. exact (@Lean.eq_refl _ _).
  Qed.

  Lemma pr_forall_jldp (QA : prosa.model.priority.definitions.JLDP_policy Job -> Prop)
      (QB : I.Prosa_Model_Priority_Definitions_JLDP_policy Job dJ -> SProp) :
    (forall hpR hpL, PrJldpRel hpR hpL -> PropSPropRel (QA hpR) (QB hpL)) ->
    PropSPropRel (forall hp, QA hp) (forall hp, QB hp).
  Proof.
    exact (pa_forall_cover _ _ PrJldpRel pr_jldp_to_target pr_jldp_to_source
      pr_jldp_to_target_rel pr_jldp_to_source_rel QA QB).
  Qed.

  (** *** Job parameters and the arrival sequence *)

  Variable jcR : prosa.behavior.job.JobCost Job.
  Variable jcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hjc : SvcJobCostRel Job jcR jcL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let RMR := @prosa.behavior.ready.JobReady Job PSR jcR jaR.
  Let RML := I.Prosa_Behavior_Ready_JobReady_inst4 Job dJ PSL jcL jaL.

  Lemma pr_uni_related (rmR : RMR) (rmL : RML) (Hrm : PaReadyRel Job jcR jcL jaR jaL rmR rmL)
      jpR jpL (Hjp : PpJobPreemptableRel Job jpR jpL) hpR hpL (Hhp : PrJldpRel hpR hpL) :
    IdScheduleRel Job (@U.uni_schedule Job jcR jaR arrR rmR jpR hpR)
      (I.Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule Job dJ jcL jaL arrL rmL jpL hpL).
  Proof.
    exact (uni_schedule_correspondence Job jcR jcL jaR jaL rmR rmL Hrm jpR jpL Hjp arrR arrL Harr
      hpR hpL Hhp).
  Qed.

  Lemma pr_choose_related hpR hpL (Hhp : PrJldpRel hpR hpL) :
    PaChooseRel Job (@U.choose_highest_prio_job Job hpR)
      (I.Prosa_Implementation_Definitions_IdealUniScheduler_choose_highest_prio_job Job dJ hpL).
  Proof.
    intros tR tL Ht xsR xsL Hxs.
    exact (choose_highest_prio_job_correspondence Job hpR hpL Hhp tR tL xsR xsL Ht Hxs).
  Qed.

  (** ** Statement correspondences *)

  (** *** uni_schedule_work_conserving *)

  Definition src_uni_schedule_work_conserving : Prop :=
    ltac:(body_of (fun s : S.statement_uni_schedule_work_conserving => s Job jcR jaR arrR)).
  Definition tgt_uni_schedule_work_conserving : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_IdealUni_PrioAware_uni_schedule_work_conserving
      Job dJ jcL jaL arrL)).

  Theorem uni_schedule_work_conserving_correspondence :
    PropSPropRel src_uni_schedule_work_conserving tgt_uni_schedule_work_conserving.
  Proof.
    unfold src_uni_schedule_work_conserving, tgt_uni_schedule_work_conserving.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply (pa_forall_nonclair_ready Job jcR jcL Hjc jaR jaL Hja). intros rmR rmL Hrm.
    apply pa_forall_preemptable. intros jpR jpL Hjp.
    apply pr_forall_jldp. intros hpR hpL Hhp.
    have HU := pr_uni_related _ _ Hrm _ _ Hjp _ _ Hhp.
    unfold prosa.model.schedule.work_conserving.work_conserving.
    cbn [I.Prosa_Model_Schedule_WorkConserving_work_conserving_inst4].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _
        (iu_backlogged_related Job jcR jcL jaR jaL rmR rmL Hrm _ _ HU tR tL Ht j))|].
    apply pa_exists_identity_correspondence. intro j'.
    exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job _ _ HU j' tR tL Ht)).
  Qed.

  (** *** uni_schedule_valid *)

  Definition src_uni_schedule_valid rmR : Prop :=
    ltac:(body_of (fun s : S.statement_uni_schedule_valid => s Job jcR jaR arrR rmR)).
  Definition tgt_uni_schedule_valid rmL : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_IdealUni_PrioAware_uni_schedule_valid
      Job dJ jcL jaL arrL rmL)).

  Theorem uni_schedule_valid_correspondence rmR rmL (Hrm : PaReadyRel Job jcR jcL jaR jaL rmR rmL) :
    PropSPropRel (src_uni_schedule_valid rmR) (tgt_uni_schedule_valid rmL).
  Proof.
    unfold src_uni_schedule_valid, tgt_uni_schedule_valid.
    apply ar_imp_correspondence; [exact (pa_nonclair_rel Job jcR jcL jaR jaL rmR rmL Hrm)|].
    apply pa_forall_preemptable. intros jpR jpL Hjp.
    apply pr_forall_jldp. intros hpR hpL Hhp.
    have HU := pr_uni_related _ _ Hrm _ _ Hjp _ _ Hhp.
    unfold prosa.behavior.ready.valid_schedule.
    cbn [I.Prosa_Behavior_Ready_valid_schedule_inst4].
    exact (ar_and_correspondence _ _ _ _ (pa_jobs_come_from_rel Job arrR arrL Harr _ _ HU)
      (pa_must_be_ready_rel Job jcR jcL jaR jaL rmR rmL Hrm _ _ HU)).
  Qed.

  (** *** schedule_respects_preemption_model *)

  Definition src_schedule_respects_preemption_model rmR : Prop :=
    ltac:(body_of (fun s : S.statement_schedule_respects_preemption_model => s Job jcR jaR arrR rmR)).
  Definition tgt_schedule_respects_preemption_model rmL : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_IdealUni_PrioAware_schedule_respects_preemption_model
      Job dJ jcL jaL arrL rmL)).

  Theorem schedule_respects_preemption_model_correspondence rmR rmL
      (Hrm : PaReadyRel Job jcR jcL jaR jaL rmR rmL) :
    PropSPropRel (src_schedule_respects_preemption_model rmR) (tgt_schedule_respects_preemption_model rmL).
  Proof.
    unfold src_schedule_respects_preemption_model, tgt_schedule_respects_preemption_model.
    apply ar_imp_correspondence; [exact (pa_nonclair_rel Job jcR jcL jaR jaL rmR rmL Hrm)|].
    apply pa_forall_preemptable. intros jpR jpL Hjp.
    apply pr_forall_jldp. intros hpR hpL Hhp.
    have HU := pr_uni_related _ _ Hrm _ _ Hjp _ _ Hhp.
    apply ar_imp_correspondence.
    { unfold RS.valid_nonpreemptive_readiness.
      cbn [I.Prosa_Analysis_Definitions_Readiness_valid_nonpreemptive_readiness_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _
          (Hjp j _ _ (iu_service_related Job _ _ HU j tR tL Ht))))|].
      exact (svc_bool_truth_correspondence _ _ (Hrm _ _ HU j _ _ Ht)). }
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      exact (ar_bool_truth_correspondence _ _
        (job_cannot_become_nonpreemptive_before_execution_correspondence Job jpR jpL Hjp j)). }
    unfold LP.schedule_respects_preemption_model.
    cbn [I.Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model_inst4].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (Hjp j _ _ (iu_service_related Job _ _ HU j tR tL Ht))))|].
    exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job _ _ HU j tR tL Ht)).
  Qed.

  (** *** scheduled_job_is_supremum *)

  Definition src_scheduled_job_is_supremum : Prop :=
    ltac:(body_of (fun s : S.statement_scheduled_job_is_supremum => s Job jcR jaR arrR)).
  Definition tgt_scheduled_job_is_supremum : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_IdealUni_PrioAware_scheduled_job_is_supremum
      Job dJ jcL jaL arrL)).

  Theorem scheduled_job_is_supremum_correspondence :
    PropSPropRel src_scheduled_job_is_supremum tgt_scheduled_job_is_supremum.
  Proof.
    unfold src_scheduled_job_is_supremum, tgt_scheduled_job_is_supremum.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply (pa_forall_nonclair_ready Job jcR jcL Hjc jaR jaL Hja). intros rmR rmL Hrm.
    apply pa_forall_preemptable. intros jpR jpL Hjp.
    apply pr_forall_jldp. intros hpR hpL Hhp.
    have HU := pr_uni_related _ _ Hrm _ _ Hjp _ _ Hhp.
    have Hcj := pr_choose_related _ _ Hhp.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job _ _ HU j tR tL Ht))|].
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _
        (pa_preemption_time_related Job arrR arrL Harr jpR jpL Hjp _ _ HU tR tL Ht))|].
    refine (id_opt_eq_correspondence _ _ _ _ (Hcj tR tL Ht _ _
      (iu_jobs_backlogged_at_related Job jcR jcL jaR jaL rmR rmL Hrm arrR arrL Harr _ _ _ tR tL Ht))
      (@Lean.eq_refl _ _)).
    destruct Ht. destruct tR as [|t'].
    - exact (iu_empty_related Job).
    - exact (iu_sut_canonical Job _ _
        (pa_alloc_related Job jcR jcL jaR jaL arrR arrL Harr rmR rmL Hrm jpR jpL Hjp _ _ Hcj) t').
  Qed.

  (** *** schedule_respects_policy *)

  Definition src_schedule_respects_policy : Prop :=
    ltac:(body_of (fun s : S.statement_schedule_respects_policy => s Job jcR jaR arrR)).
  Definition tgt_schedule_respects_policy : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_IdealUni_PrioAware_schedule_respects_policy
      Job dJ jcL jaL arrL)).

  Theorem schedule_respects_policy_correspondence :
    PropSPropRel src_schedule_respects_policy tgt_schedule_respects_policy.
  Proof.
    unfold src_schedule_respects_policy, tgt_schedule_respects_policy.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply (pa_forall_nonclair_ready Job jcR jcL Hjc jaR jaL Hja). intros rmR rmL Hrm.
    apply pa_forall_preemptable. intros jpR jpL Hjp.
    apply pr_forall_jldp. intros hpR hpL Hhp.
    have HU := pr_uni_related _ _ Hrm _ _ Hjp _ _ Hhp.
    apply ar_imp_correspondence.
    { unfold prosa.model.priority.definitions.reflexive_priorities, ssrbool.reflexive.
      cbn [I.Prosa_Model_Priority_Definitions_reflexive_priorities].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_identity_correspondence. intro x.
      exact (svc_bool_truth_correspondence _ _ (Hhp _ _ Ht x x)). }
    apply ar_imp_correspondence.
    { unfold prosa.model.priority.definitions.total_priorities, ssrbool.total.
      cbn [I.Prosa_Model_Priority_Definitions_total_priorities].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_identity_correspondence. intro x.
      apply ar_forall_identity_correspondence. intro y.
      exact (svc_bool_truth_correspondence _ _ (pp_bool_or_related _ _ _ _ (Hhp _ _ Ht x y) (Hhp _ _ Ht y x))). }
    apply ar_imp_correspondence.
    { unfold prosa.model.priority.definitions.transitive_priorities, ssrbool.transitive.
      cbn [I.Prosa_Model_Priority_Definitions_transitive_priorities].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_identity_correspondence. intro y.
      apply ar_forall_identity_correspondence. intro x.
      apply ar_forall_identity_correspondence. intro z.
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (Hhp _ _ Ht x y))|].
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (Hhp _ _ Ht y z))|].
      exact (svc_bool_truth_correspondence _ _ (Hhp _ _ Ht x z)). }
    unfold PD.respects_JLDP_policy_at_preemption_point.
    cbn [I.Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point_inst4].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j_hp.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _
        (pa_preemption_time_related Job arrR arrL Harr jpR jpL Hjp _ _ HU tR tL Ht))|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _
        (iu_backlogged_related Job jcR jcL jaR jaL rmR rmL Hrm _ _ HU tR tL Ht j))|].
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job _ _ HU j_hp tR tL Ht))|].
    exact (svc_bool_truth_correspondence _ _ (Hhp _ _ Ht j_hp j)).
  Qed.
End PrioAware.
