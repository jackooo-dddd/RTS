From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import OptimalityEdfSemanticSource.
From prosa Require Import model.processor.ideal model.schedule.edf model.priority.edf model.readiness.basic
  model.preemption.fully_preemptive model.schedule.work_conserving.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedOptimalityEdf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  IdealUniSchedulerCorrespondence EdfDefinitionsHelpers EdfTransCorrespondence FactsEdfOptCorrespondence.

Module I := ImportedOptimalityEdf.
Module S := OptimalityEdfSemanticSource.OptimalityEdfSemanticSource.
Module PD := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.

(** Statement correspondences for [results/optimality/edf.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (the instances and, where present, the arrival
    sequence); target side: the imported Lean theorem types.  The processor
    model is fixed to the ideal uniprocessor on both sides, with the accepted
    relations and covers of the edf-definitions and edf-opt certificates
    (states by the constructor-preserving Option map, schedules pointwise and
    covered in both directions, also under existentials); [job_cost] by
    [SvcJobCostRel], [job_deadline] pointwise by [SubNatRel], [job_arrival] by
    [ArJobArrivalRel], arrival sequences by [ArArrivalSequenceRel].  The
    readiness and preemption models are the source's local basic ([pending])
    and fully preemptive instances on both sides; the EDF policy is the
    deadline comparison on both sides.  Work conservation and policy
    compliance at preemption points are related here by unfolding, as in the
    accepted edf-definitions certificate.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section OptimalityEdf.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.
  Let SchedR := @prosa.behavior.schedule.schedule Job PSR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.

  Variable jcR : prosa.behavior.job.JobCost Job.
  Variable jcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hjc : SvcJobCostRel Job jcR jcL.
  Variable dlR : prosa.behavior.job.JobDeadline Job.
  Variable dlL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
  Hypothesis Hdl : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
      (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let RMR := @prosa.model.readiness.basic.basic_ready_instance Job PSR jaR jcR.
  Let RML := I.Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job dJ PSL jaL jcL.

  Lemma oed_ready_related : PaReadyRel Job jcR jcL jaR jaL RMR RML.
  Proof.
    intros sR sL Hs j tR tL Ht.
    exact (pa_pending_related Job jcR jcL Hjc jaR jaL Hja sR sL Hs j tR tL Ht).
  Qed.

  Let JPR := @prosa.model.preemption.fully_preemptive.fully_preemptive_job_model Job.
  Let JPL := I.Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job dJ.

  Lemma oed_preemptable_related : PpJobPreemptableRel Job JPR JPL.
  Proof. intros j nR nL Hn. exact (@Lean.eq_refl _ _). Qed.

  (** *** Existentials over schedules *)

  Lemma oed_exists_sched (PR : SchedR -> Prop) (PL : SchedL -> SProp) :
    (forall sR sL, IdScheduleRel Job sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (exists s, PR s) (I.Exists SchedL PL).
  Proof.
    intro H. apply prop_sprop_rel_intro.
    - intros [s Hs]. exact (I.Exists_intro SchedL PL (pa_sched_to_target Job s)
        (prop_to_sprop _ _ (H _ _ (pa_sched_to_target_rel Job s)) Hs)).
    - intros [s Hs]. apply strictly_inhabits. exists (pa_sched_to_source Job s).
      exact (sprop_to_prop _ _ (H _ _ (pa_sched_to_source_rel Job s)) Hs).
  Qed.

  (** *** Observations on related schedules *)

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : IdScheduleRel Job sR sL.

    Lemma oed_sched_at (j : Job) (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
      PropSPropRel (is_true (@prosa.behavior.service.scheduled_at Job PSR sR j tR))
        (Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL sL j tL) I.Bool_true).
    Proof. exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job sR sL Hs j tR tL Ht)). Qed.

    Lemma oed_wc_rel :
      PropSPropRel (@prosa.model.schedule.work_conserving.work_conserving Job jaR jcR PSR RMR arrR sR)
        (I.Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job dJ jaL jcL PSL RML arrL sL).
    Proof.
      unfold prosa.model.schedule.work_conserving.work_conserving.
      cbn [I.Prosa_Model_Schedule_WorkConserving_work_conserving_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _
          (iu_backlogged_related Job jcR jcL jaR jaL RMR RML oed_ready_related sR sL Hs tR tL Ht j))|].
      apply pa_exists_identity_correspondence. intro j'.
      exact (oed_sched_at j' tR tL Ht).
    Qed.

    Lemma oed_respects_rel :
      PropSPropRel
        (@PD.respects_JLFP_policy_at_preemption_point Job jaR jcR PSR JPR RMR arrR sR
          (@prosa.model.priority.edf.EDF Job dlR))
        (I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job dJ jaL jcL PSL
          JPL RML arrL sL (I.Prosa_Model_Priority_Edf_EDF Job dJ dlL)).
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
          (pa_preemption_time_related Job arrR arrL Harr JPR JPL oed_preemptable_related sR sL Hs tR tL Ht))|].
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (iu_backlogged_related Job jcR jcL jaR jaL RMR RML oed_ready_related sR sL Hs tR tL Ht j))|].
      apply ar_imp_correspondence; [exact (oed_sched_at j_hp tR tL Ht)|].
      exact (svc_bool_truth_correspondence _ _ (svc_decide_le_related _ _ _ _ (Hdl j_hp) (Hdl j))).
    Qed.
  End Sched.

  Let VAL sR sL (Hs : IdScheduleRel Job sR sL) :=
    feo_valid_rel Job jcR jcL Hjc jaR jaL Hja sR sL Hs arrR arrL Harr.
  Let DOA sR sL (Hs : IdScheduleRel Job sR sL) :=
    feo_doa_rel Job jcR jcL Hjc dlR dlL Hdl sR sL Hs arrR arrL Harr.
  Let EDFS sR sL (Hs : IdScheduleRel Job sR sL) :=
    feo_EDF_schedule_rel Job dlR dlL Hdl jaR jaL Hja sR sL Hs.

  (** The premise shared by the three optimality theorems. *)
  Lemma oed_premise :
    PropSPropRel
      (exists any_sched : SchedR,
        @prosa.behavior.ready.valid_schedule Job jaR PSR any_sched jcR RMR arrR /\
        @SchedulabilitySemanticSource.SchedulabilitySemanticSource.all_deadlines_of_arrivals_met
          Job jcR dlR PSR arrR any_sched)
      (I.Exists SchedL (fun any_sched =>
        And (I.Prosa_Behavior_Ready_valid_schedule_inst4 Job dJ jaL PSL any_sched jcL RML arrL)
          (I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job dJ jcL dlL PSL arrL
            any_sched))).
  Proof.
    apply oed_exists_sched. intros sR sL Hs.
    exact (ar_and_correspondence _ _ _ _ (VAL _ _ Hs) (DOA _ _ Hs)).
  Qed.

  (** ** Statement correspondences *)

  Definition src_EDF_optimality : Prop :=
    ltac:(body_of (fun s : S.statement_EDF_optimality => s Job jcR dlR jaR arrR)).
  Definition tgt_EDF_optimality : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Optimality_Edf_EDF_optimality Job dJ jcL dlL jaL arrL)).

  Theorem EDF_optimality_correspondence : PropSPropRel src_EDF_optimality tgt_EDF_optimality.
  Proof.
    unfold src_EDF_optimality, tgt_EDF_optimality.
    apply ar_imp_correspondence; [exact oed_premise|].
    apply oed_exists_sched. intros sR sL Hs.
    apply ar_and_correspondence; [exact (VAL _ _ Hs)|].
    exact (ar_and_correspondence _ _ _ _ (DOA _ _ Hs) (EDFS _ _ Hs)).
  Qed.

  Definition src_EDF_WC_optimality : Prop :=
    ltac:(body_of (fun s : S.statement_EDF_WC_optimality => s Job jcR dlR jaR arrR)).
  Definition tgt_EDF_WC_optimality : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Optimality_Edf_EDF_WC_optimality Job dJ jcL dlL jaL arrL)).

  Theorem EDF_WC_optimality_correspondence : PropSPropRel src_EDF_WC_optimality tgt_EDF_WC_optimality.
  Proof.
    unfold src_EDF_WC_optimality, tgt_EDF_WC_optimality.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ar_imp_correspondence; [exact oed_premise|].
    apply oed_exists_sched. intros sR sL Hs.
    apply ar_and_correspondence; [exact (VAL _ _ Hs)|].
    apply ar_and_correspondence; [exact (DOA _ _ Hs)|].
    exact (ar_and_correspondence _ _ _ _ (oed_wc_rel _ _ Hs) (EDFS _ _ Hs)).
  Qed.

  Definition src_EDF_priority_compliant_WC_optimality : Prop :=
    ltac:(body_of (fun s : S.statement_EDF_priority_compliant_WC_optimality => s Job jcR dlR jaR arrR)).
  Definition tgt_EDF_priority_compliant_WC_optimality : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Results_Optimality_Edf_EDF_priority_compliant_WC_optimality Job dJ jcL dlL jaL arrL)).

  Theorem EDF_priority_compliant_WC_optimality_correspondence :
    PropSPropRel src_EDF_priority_compliant_WC_optimality tgt_EDF_priority_compliant_WC_optimality.
  Proof.
    unfold src_EDF_priority_compliant_WC_optimality, tgt_EDF_priority_compliant_WC_optimality.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ar_imp_correspondence; [exact oed_premise|].
    apply oed_exists_sched. intros sR sL Hs.
    apply ar_and_correspondence; [exact (VAL _ _ Hs)|].
    apply ar_and_correspondence; [exact (DOA _ _ Hs)|].
    exact (ar_and_correspondence _ _ _ _ (oed_wc_rel _ _ Hs) (oed_respects_rel _ _ Hs)).
  Qed.

  Definition src_weak_EDF_optimality : Prop :=
    ltac:(body_of (fun s : S.statement_weak_EDF_optimality => s Job jcR dlR jaR)).
  Definition tgt_weak_EDF_optimality : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Optimality_Edf_weak_EDF_optimality Job dJ jcL dlL jaL)).

  Theorem weak_EDF_optimality_correspondence : PropSPropRel src_weak_EDF_optimality tgt_weak_EDF_optimality.
  Proof.
    unfold src_weak_EDF_optimality, tgt_weak_EDF_optimality.
    apply pa_forall_sched. intros aR aL Ha.
    apply (feo_wf Job jcR jcL Hjc dlR dlL Hdl jaR jaL Hja _ _ Ha).
    apply oed_exists_sched. intros sR sL Hs.
    apply ar_and_correspondence; [exact (feo_must_rel Job jaR jaL Hja _ _ Hs)|].
    apply ar_and_correspondence; [exact (feo_cde_rel Job jcR jcL Hjc _ _ Hs)|].
    apply ar_and_correspondence; [exact (feo_dm_rel Job jcR jcL Hjc dlR dlL Hdl _ _ Hs)|].
    apply ar_and_correspondence; [exact (EDFS _ _ Hs)|].
    apply ar_forall_identity_correspondence. intro j.
    apply pp_iff_correspondence.
    - apply ar_exists_nat_correspondence. intros tR tL Ht. exact (oed_sched_at _ _ Ha j tR tL Ht).
    - apply ar_exists_nat_correspondence. intros tR tL Ht. exact (oed_sched_at _ _ Hs j tR tL Ht).
  Qed.
End OptimalityEdf.
