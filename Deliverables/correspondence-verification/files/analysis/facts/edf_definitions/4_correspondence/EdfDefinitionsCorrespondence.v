From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import EdfDefinitionsSemanticSource.
From prosa Require Import model.processor.ideal model.schedule.edf model.priority.edf
  model.readiness.basic model.preemption.fully_preemptive.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedEdfDefinitions ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  IdealUniSchedulerCorrespondence EdfDefinitionsHelpers.

Module I := ImportedEdfDefinitions.
Module S := EdfDefinitionsSemanticSource.EdfDefinitionsSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module PD := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.
Module SC := SchedulabilitySemanticSource.SchedulabilitySemanticSource.

(** Statement correspondences for [analysis/facts/edf_definitions.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.  The
    processor model is fixed to the ideal uniprocessor on both sides, with
    the relations and covers of the accepted preemption-aware certificate
    (re-bound here as [PreemptionAwareHelpers]): states by the
    constructor-preserving Option map and schedules pointwise (covered in
    both directions); [job_cost] by [SvcJobCostRel], [job_arrival] by
    [ArJobArrivalRel], [job_deadline] pointwise by [SubNatRel], arrival
    sequences by [ArArrivalSequenceRel].  The readiness and preemption models
    are the source's local basic ([pending]) and fully preemptive instances on
    both sides: the former is related through the accepted [pending]
    relation, the latter is the constant [true] on both sides; the EDF policy
    is the deadline comparison on both sides.  No source or target theorem is
    used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section EdfDefinitions.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.
  Let SchedR := @prosa.behavior.schedule.schedule Job PSR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.

  Variable jcR : prosa.behavior.job.JobCost Job.
  Variable jcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hjc : SvcJobCostRel Job jcR jcL.
  Variable jdR : prosa.behavior.job.JobDeadline Job.
  Variable jdL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
  Hypothesis Hjd : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_deadline Job jdR j)
      (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ jdL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  (** *** The local readiness and preemption instances *)

  Let RMR := @prosa.model.readiness.basic.basic_ready_instance Job PSR jaR jcR.
  Let RML := I.Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job dJ PSL jaL jcL.

  Lemma edfd_ready_related : PaReadyRel Job jcR jcL jaR jaL RMR RML.
  Proof.
    intros sR sL Hs j tR tL Ht.
    exact (pa_pending_related Job jcR jcL Hjc jaR jaL Hja sR sL Hs j tR tL Ht).
  Qed.

  Let JPR := @prosa.model.preemption.fully_preemptive.fully_preemptive_job_model Job.
  Let JPL := I.Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job dJ.

  Lemma edfd_preemptable_related : PpJobPreemptableRel Job JPR JPL.
  Proof. intros j nR nL Hn. exact (@Lean.eq_refl _ _). Qed.

  (** *** Definitions on related schedules *)

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : IdScheduleRel Job sR sL.

    Lemma edfd_jobs_must_arrive_rel :
      PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PSR sR)
        (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job dJ jaL PSL sL).
    Proof.
      unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job sR sL Hs j tR tL Ht))|].
      exact (ar_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
    Qed.

    Lemma edfd_completed_jobs_dont_execute_rel :
      PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PSR sR jcR)
        (I.Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job dJ PSL sL jcL).
    Proof.
      unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job sR sL Hs j tR tL Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _ (iu_service_related Job sR sL Hs j tR tL Ht) (Hjc j)).
    Qed.

    Lemma edfd_deadlines_met_rel :
      PropSPropRel (@SC.all_deadlines_of_arrivals_met Job jcR jdR PSR arrR sR)
        (I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job dJ jcL jdL PSL arrL sL).
    Proof.
      unfold SC.all_deadlines_of_arrivals_met.
      cbn [I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      unfold prosa.behavior.service.job_meets_deadline, prosa.behavior.service.completed_by.
      exact (svc_bool_truth_correspondence _ _
        (svc_decide_le_related _ _ _ _ (Hjc j) (iu_service_related Job sR sL Hs j _ _ (Hjd j)))).
    Qed.

    Lemma edfd_EDF_schedule_rel :
      PropSPropRel (@prosa.model.schedule.edf.EDF_schedule Job jdR jaR PSR sR)
        (I.Prosa_Model_Schedule_Edf_EDF_schedule_inst4 Job dJ jdL jaL PSL sL).
    Proof.
      unfold prosa.model.schedule.edf.EDF_schedule, prosa.model.schedule.edf.EDF_at.
      cbn [I.Prosa_Model_Schedule_Edf_EDF_schedule_inst4 I.Prosa_Model_Schedule_Edf_EDF_at_inst4].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job sR sL Hs j tR tL Ht))|].
      apply ar_forall_nat_correspondence. intros t'R t'L Ht'.
      apply ar_forall_identity_correspondence. intro j'.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Ht')|].
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job sR sL Hs j' t'R t'L Ht'))|].
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ (Hja j') Ht)|].
      exact (sub_nat_le_correspondence _ _ _ _ (Hjd j) (Hjd j')).
    Qed.

    Lemma edfd_respects_rel :
      PropSPropRel
        (@PD.respects_JLFP_policy_at_preemption_point Job jaR jcR PSR JPR RMR arrR sR
          (@prosa.model.priority.edf.EDF Job jdR))
        (I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job dJ jaL jcL PSL
          JPL RML arrL sL (I.Prosa_Model_Priority_Edf_EDF Job dJ jdL)).
    Proof.
      unfold PD.respects_JLFP_policy_at_preemption_point, PD.respects_JLDP_policy_at_preemption_point.
      cbn [I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4
        I.Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_identity_correspondence. intro j_hp.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _
          (pa_preemption_time_related Job arrR arrL Harr JPR JPL edfd_preemptable_related sR sL Hs tR tL Ht))|].
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (iu_backlogged_related Job jcR jcL jaR jaL RMR RML edfd_ready_related sR sL Hs tR tL Ht j))|].
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job sR sL Hs j_hp tR tL Ht))|].
      exact (svc_bool_truth_correspondence _ _ (svc_decide_le_related _ _ _ _ (Hjd j_hp) (Hjd j))).
    Qed.
  End Sched.

  (** ** Statement correspondences *)

  (** *** EDF_schedule_implies_respects_policy_at_preemption_point *)

  Definition src_EDF_schedule_implies_respects_policy_at_preemption_point sR : Prop :=
    ltac:(body_of (fun s : S.statement_EDF_schedule_implies_respects_policy_at_preemption_point =>
      s Job jcR jdR jaR arrR sR)).
  Definition tgt_EDF_schedule_implies_respects_policy_at_preemption_point sL : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_EdfDefinitions_EDF_schedule_implies_respects_policy_at_preemption_point
        Job dJ jcL jdL jaL arrL sL)).

  Theorem EDF_schedule_implies_respects_policy_at_preemption_point_correspondence sR sL
      (Hs : IdScheduleRel Job sR sL) :
    PropSPropRel (src_EDF_schedule_implies_respects_policy_at_preemption_point sR)
      (tgt_EDF_schedule_implies_respects_policy_at_preemption_point sL).
  Proof.
    unfold src_EDF_schedule_implies_respects_policy_at_preemption_point,
      tgt_EDF_schedule_implies_respects_policy_at_preemption_point.
    apply ar_imp_correspondence; [exact (edfd_deadlines_met_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (edfd_EDF_schedule_rel _ _ Hs)|].
    exact (edfd_respects_rel _ _ Hs).
  Qed.

  (** *** respects_policy_at_preemption_point_implies_EDF_schedule *)

  Definition src_respects_policy_at_preemption_point_implies_EDF_schedule : Prop :=
    ltac:(body_of (fun s : S.statement_respects_policy_at_preemption_point_implies_EDF_schedule =>
      s Job jcR jdR jaR arrR)).
  Definition tgt_respects_policy_at_preemption_point_implies_EDF_schedule : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_EdfDefinitions_respects_policy_at_preemption_point_implies_EDF_schedule
        Job dJ jcL jdL jaL arrL)).

  Theorem respects_policy_at_preemption_point_implies_EDF_schedule_correspondence :
    PropSPropRel src_respects_policy_at_preemption_point_implies_EDF_schedule
      tgt_respects_policy_at_preemption_point_implies_EDF_schedule.
  Proof.
    unfold src_respects_policy_at_preemption_point_implies_EDF_schedule,
      tgt_respects_policy_at_preemption_point_implies_EDF_schedule.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (edfd_jobs_must_arrive_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (edfd_completed_jobs_dont_execute_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (pa_jobs_come_from_rel Job arrR arrL Harr _ _ Hs)|].
    apply ar_imp_correspondence; [exact (edfd_respects_rel _ _ Hs)|].
    exact (edfd_EDF_schedule_rel _ _ Hs).
  Qed.

  (** *** EDF_schedule_equiv *)

  Definition src_EDF_schedule_equiv : Prop :=
    ltac:(body_of (fun s : S.statement_EDF_schedule_equiv => s Job jcR jdR jaR arrR)).
  Definition tgt_EDF_schedule_equiv : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_EdfDefinitions_EDF_schedule_equiv Job dJ jcL jdL jaL arrL)).

  Theorem EDF_schedule_equiv_correspondence : PropSPropRel src_EDF_schedule_equiv tgt_EDF_schedule_equiv.
  Proof.
    unfold src_EDF_schedule_equiv, tgt_EDF_schedule_equiv.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (edfd_jobs_must_arrive_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (edfd_completed_jobs_dont_execute_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (pa_jobs_come_from_rel Job arrR arrL Harr _ _ Hs)|].
    apply ar_imp_correspondence; [exact (edfd_deadlines_met_rel _ _ Hs)|].
    exact (pp_iff_correspondence _ _ _ _ (edfd_EDF_schedule_rel _ _ Hs) (edfd_respects_rel _ _ Hs)).
  Qed.
End EdfDefinitions.
