From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import BusyIntervalServiceInversionSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.processor.supply
  model.schedule.scheduled model.priority.classes model.job.properties
  analysis.definitions.work_bearing_readiness analysis.definitions.service.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBusyIntervalServiceInversion ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers
  TaskPreemptionParametersCorrespondence BusyIntervalPiHelpers ServiceInversionPredCorrespondence.

Module I := ImportedBusyIntervalServiceInversion.
Module S := BusyIntervalServiceInversionSemanticSource.BusyIntervalServiceInversionSemanticSource.
Module SIP := ServiceInversionPredSemanticSource.ServiceInversionPredSemanticSource.
Module SIB := ServiceInversionBusyPrefixSemanticSource.ServiceInversionBusyPrefixSemanticSource.
Module TPS := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module PPS := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module PIS := PriorityInversionSemanticSource.PriorityInversionSemanticSource.

(** Statement correspondence for [analysis/facts/busy_interval/service_inversion.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types, the task-level maximum
    nonpreemptive segment, the job-task, arrival and cost classes); target
    side: the imported Lean theorem types.  Inputs: [job_arrival] by
    [ArJobArrivalRel], [job_cost] by the accepted [SvcJobCostRel], [job_task]
    by [Lean.eq], [TaskMaxNonpreemptiveSegment] by the accepted
    [TppMaxSegmentRel].  Inputs quantified inside a statement are covered in
    both directions by the accepted conversions: processor models
    ([isj_cover_pstate]), arrival sequences ([fpre_forall_arr]), schedules
    through the processor-model relation ([fpre_forall_sched]), JLFP policies
    ([fpre_forall_jlfp]), [JobPreemptable] instances ([fpre_forall_jp]), the
    readiness instance on the statement's schedule pair ([fpre_forall_jr]),
    blocking-bound functions ([ex_forall_fun]), jobs and tasks (identity) and
    instants; JLDP policies are covered here pointwise on Booleans at related
    instants ([bsi_forall_jldp]), in the same way as the accepted JLFP cover.
    Service inversion and its cumulative sum are replayed from the accepted
    service-inversion definition certificate over the pair observations (its
    [List.any] and bool-to-nat lemmas reused; the interval sum through the
    accepted [svc_interval_sum_related] against the kernel-guarded projection
    exported with the artifact); supply is related through the processor-model
    relation's [supply_in] component; busy prefixes, priority inversion and
    its cumulative sum are the accepted busy-interval-existence helpers;
    preemption models, schedule validity, work-bearing readiness and the
    JLFP-at-preemption-point policy are the accepted preemption-facts and
    existence helpers; the maximum lower-priority nonpreemptive segment is the
    accepted [pi] definition certificate.  No source or target theorem is
    used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section ServiceInversion.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  (** ** JLDP policies quantified inside a statement *)

  Definition BsiJLDPRel (pR : prosa.model.priority.definitions.JLDP_policy Job)
      (pL : I.Prosa_Model_Priority_Definitions_JLDP_policy Job dJ) : SProp :=
    forall tR tL, SubNatRel tR tL -> forall x y : Job,
      ArBoolRel (@prosa.model.priority.definitions.hep_job_at Job pR tR x y)
        (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job dJ pL tL x y).

  Lemma bsi_forall_jldp (PR : prosa.model.priority.definitions.JLDP_policy Job -> Prop)
      (PL : I.Prosa_Model_Priority_Definitions_JLDP_policy Job dJ -> SProp) :
    (forall pR pL, BsiJLDPRel pR pL -> PropSPropRel (PR pR) (PL pL)) ->
    PropSPropRel (forall p, PR p) (forall p, PL p).
  Proof.
    apply (isj_forall_cover_sprop _ _ BsiJLDPRel
      (fun pR => I.Prosa_Model_Priority_Definitions_JLDP_policy_mk Job dJ
        (fun tL x y => ar_bool_to_imported
          (@prosa.model.priority.definitions.hep_job_at Job pR (sub_nat_to_rocq tL) x y)))
      (fun pL => ((fun t x y => ar_bool_to_rocq
        (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job dJ pL (sub_nat_to_imported t) x y))
        : prosa.model.priority.definitions.JLDP_policy Job))).
    - intros pR tR tL Ht x y. rewrite -(isj_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
    - intros pL tR tL Ht x y.
      exact (isj_lean_transport
        (fun v => ArBoolRel (ar_bool_to_rocq (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at
            Job dJ pL (sub_nat_to_imported tR) x y))
          (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job dJ pL v x y))
        _ _ Ht (ar_bool_target_roundtrip _)).
  Qed.

  Lemma bsi_reflexive_priorities_rel pR pL (Hp : BsiJLDPRel pR pL) :
    PropSPropRel (@prosa.model.priority.definitions.reflexive_priorities Job pR)
      (I.Prosa_Model_Priority_Definitions_reflexive_priorities Job dJ pL).
  Proof.
    unfold prosa.model.priority.definitions.reflexive_priorities, reflexive.
    cbn [I.Prosa_Model_Priority_Definitions_reflexive_priorities].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j.
    exact (ar_bool_truth_correspondence _ _ (Hp tR tL Ht j j)).
  Qed.

  (** The JLDP view of a JLFP policy (the source and target coercions reduce
      to the JLFP relation). *)
  Lemma bsi_jlfp_to_jldp_rel pR pL (Hp : FpreJLFPRel Job pR pL) :
    BsiJLDPRel (@prosa.model.priority.coercion.JLFP_to_JLDP Job pR)
      (I.Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job dJ pL).
  Proof. intros tR tL Ht x y. exact (Hp x y). Qed.

  (** ** Observations of a fixed processor-model pair *)

  Section Pair.
    Variable PR : prosa.behavior.schedule.ProcessorState Job.
    Variable PL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
    Variable X : IsjPSRel Job PR PL.

    Lemma bsi_unit_supply_related :
      PropSPropRel (@prosa.model.processor.platform_properties.unit_supply_proc_model Job PR)
        (I.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job dJ PL).
    Proof.
      unfold prosa.model.processor.platform_properties.unit_supply_proc_model.
      cbn [I.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model].
      apply (isj_forall_cover_sprop _ _
        (fun sR sL => Lean.eq (isj_st_to Job PR PL X sR) sL) (isj_st_to Job PR PL X)
        (isj_st_from Job PR PL X) (fun _ => @Lean.eq_refl _ _) (isj_st_rt_target Job PR PL X)).
      intros sR sL Hs.
      exact (sub_nat_le_correspondence _ _ _ _ (isj_lean_transport
        (fun sL => SubNatRel (@prosa.behavior.schedule.supply_in Job PR sR)
           (I.Prosa_Behavior_Schedule_ProcessorState_supply_in Job dJ PL sL))
        _ _ Hs (isj_sup_in_rel Job PR PL X sR)) (sub_nat_rel_canonical 1)).
    Qed.

    Section Sched.
      Variable sR : @prosa.behavior.schedule.schedule Job PR.
      Variable sL : I.Prosa_Behavior_Schedule_schedule Job dJ PL.
      Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.

      Let Hse := isj_psr_service_at_related Job PR PL X sR sL Hs.

      Lemma bsi_supply_at_related (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        SubNatRel (@prosa.model.processor.supply.supply_at Job PR sR tR)
          (I.Prosa_Model_Processor_Supply_supply_at Job dJ PL sL tL).
      Proof.
        intro Ht. unfold prosa.model.processor.supply.supply_at.
        cbn [I.Prosa_Model_Processor_Supply_supply_at].
        exact (isj_lean_transport
          (fun sLv => SubNatRel (@prosa.behavior.schedule.supply_in Job PR (sR tR))
             (I.Prosa_Behavior_Schedule_ProcessorState_supply_in Job dJ PL sLv))
          _ _ (Hs tR tL Ht) (isj_sup_in_rel Job PR PL X (sR tR))).
      Qed.

      Lemma bsi_has_supply_related (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        ArBoolRel (@prosa.model.processor.supply.has_supply Job PR sR tR)
          (I.Prosa_Model_Processor_Supply_has_supply Job dJ PL sL tL).
      Proof.
        intro Ht. unfold prosa.model.processor.supply.has_supply.
        cbn [I.Prosa_Model_Processor_Supply_has_supply].
        exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (bsi_supply_at_related tR tL Ht)).
      Qed.

      Lemma bsi_is_blackout_related (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        ArBoolRel (@prosa.model.processor.supply.is_blackout Job PR sR tR)
          (I.Prosa_Model_Processor_Supply_is_blackout Job dJ PL sL tL).
      Proof.
        intro Ht. unfold prosa.model.processor.supply.is_blackout.
        cbn [I.Prosa_Model_Processor_Supply_is_blackout].
        exact (svc_bool_not_related _ _ (bsi_has_supply_related tR tL Ht)).
      Qed.

      Lemma bsi_receives_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        ArBoolRel (@prosa.behavior.service.receives_service_at Job PR sR j tR)
          (I.Prosa_Behavior_Service_receives_service_at Job dJ PL sL j tL).
      Proof.
        intro Ht. unfold prosa.behavior.service.receives_service_at.
        cbn [I.Prosa_Behavior_Service_receives_service_at].
        exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hse j tR tL Ht)).
      Qed.

      Section Arr.
        Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
        Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
        Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

        Lemma bsi_served_jobs_at_related (tR : nat) (tL : Lean.Nat) :
          SubNatRel tR tL ->
          ArListRel (@prosa.analysis.definitions.service.served_jobs_at Job PR arrR sR tR)
            (I.Prosa_Analysis_Definitions_Service_served_jobs_at Job dJ PL arrL sL tL).
        Proof.
          intro Ht. unfold prosa.analysis.definitions.service.served_jobs_at.
          cbn [I.Prosa_Analysis_Definitions_Service_served_jobs_at].
          apply ar_filter_related.
          - intro j. exact (bsi_receives_service_at_related j tR tL Ht).
          - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr tR tL Ht).
        Qed.

        Section Policy.
          Variable pR : prosa.model.priority.definitions.JLDP_policy Job.
          Variable pL : I.Prosa_Model_Priority_Definitions_JLDP_policy Job dJ.
          Hypothesis Hp : BsiJLDPRel pR pL.

          (** Replayed from the accepted service-inversion definition
              certificate over the pair observations. *)
          Lemma bsi_service_inversion_related (j : Job) (tR : nat) (tL : Lean.Nat) :
            SubNatRel tR tL ->
            ArBoolRel (@SIP.service_inversion Job PR arrR sR pR j tR)
              (I.Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion
                Job dJ PL arrL sL pL j tL).
          Proof.
            intro Ht. unfold SIP.service_inversion.
            cbn [I.Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion].
            have Hsv := bsi_served_jobs_at_related tR tL Ht.
            apply ar_bool_and_related.
            - exact (svc_bool_not_related _ _ (ar_decide_mem_related Job j _ _ Hsv)).
            - apply sip_has_related; [|exact Hsv].
              intro jlp. exact (svc_bool_not_related _ _ (Hp tR tL Ht jlp j)).
          Qed.

          Lemma bsi_cumulative_service_inversion_related (j : Job) t1R t1L t2R t2L :
            SubNatRel t1R t1L -> SubNatRel t2R t2L ->
            SubNatRel (@SIP.cumulative_service_inversion Job PR arrR sR pR j t1R t2R)
              (I.Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion
                Job dJ PL arrL sL pL j t1L t2L).
          Proof.
            intros H1 H2. unfold SIP.cumulative_service_inversion.
            have Hsum := svc_interval_sum_related t1R t2R t1L t2L
              (fun t => nat_of_bool (@SIP.service_inversion Job PR arrR sR pR j t))
              (fun t => I.Bool_toNat
                (I.Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion
                  Job dJ PL arrL sL pL j t))
              H1 H2
              (fun a b Hab => sip_bool_to_nat_related _ _ (bsi_service_inversion_related j a b Hab)).
            change (SubNatRel
              (\sum_(t1R <= t < t2R) nat_of_bool (@SIP.service_inversion Job PR arrR sR pR j t))
              (I.Prosa_Validation_ServiceInversionPredInterface_cumulativeServiceInversionProjection
                Job dJ PL arrL sL pL j t1L t2L)) in Hsum.
            exact Hsum.
          Qed.
        End Policy.
      End Arr.
    End Sched.

    Lemma bsi_fully_consuming_related :
      PropSPropRel (@prosa.model.processor.platform_properties.fully_consuming_proc_model Job PR)
        (I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job dJ PL).
    Proof.
      unfold prosa.model.processor.platform_properties.fully_consuming_proc_model.
      cbn [I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model].
      apply ar_forall_identity_correspondence. intro j.
      apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (fpre_scheduled_at_related Job PR PL X sR sL Hs j _ _ Ht))|].
      exact (sub_nat_eq_correspondence _ _ _ _ (isj_psr_service_at_related Job PR PL X sR sL Hs j _ _ Ht)
        (bsi_supply_at_related sR sL Hs _ _ Ht)).
    Qed.
  End Pair.

  (** ** Statements without arrival or cost inputs *)

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].
  Local Ltac M_ps := apply (isj_cover_pstate Job); intros PR PL X.
  Local Ltac M_arr := apply (fpre_forall_arr Job); intros arrR arrL Harr.
  Local Ltac M_jldp := apply bsi_forall_jldp; intros pR pL Hp.
  Local Ltac M_jlfp := apply fpre_forall_jlfp; intros pR pL Hp.
  Local Ltac M_jp := apply fpre_forall_jp; intros jpR jpL Hjp.
  Local Ltac M_id x := apply ar_forall_identity_correspondence; intro x.
  Local Ltac M_nat a b H := apply ar_forall_nat_correspondence; intros a b H.

  Definition src_blackout_implies_no_service_inversion : Prop :=
    ltac:(body_of (fun s : S.statement_blackout_implies_no_service_inversion => s Job)).
  Definition tgt_blackout_implies_no_service_inversion : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_ServiceInversion_blackout_implies_no_service_inversion Job dJ)).

  Theorem blackout_implies_no_service_inversion_correspondence :
    PropSPropRel src_blackout_implies_no_service_inversion tgt_blackout_implies_no_service_inversion.
  Proof.
    unfold src_blackout_implies_no_service_inversion, tgt_blackout_implies_no_service_inversion.
    M_ps. M_arr. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). M_jldp. M_id j. M_nat tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (bsi_is_blackout_related PR PL X sR sL Hs tR tL Ht)).
    exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
      (bsi_service_inversion_related PR PL X sR sL Hs arrR arrL Harr pR pL Hp j tR tL Ht))).
  Qed.

  Definition src_service_inversion_cat : Prop :=
    ltac:(body_of (fun s : S.statement_service_inversion_cat => s Job)).
  Definition tgt_service_inversion_cat : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_ServiceInversion_service_inversion_cat Job dJ)).

  Theorem service_inversion_cat_correspondence :
    PropSPropRel src_service_inversion_cat tgt_service_inversion_cat.
  Proof.
    unfold src_service_inversion_cat, tgt_service_inversion_cat.
    M_ps. M_arr. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). M_jldp. M_id j.
    M_nat t1R t1L Ht1. M_nat t2R t2L Ht2. M_nat tR tL Ht.
    imp (sub_nat_le_correspondence _ _ _ _ Ht1 Ht).
    imp (sub_nat_le_correspondence _ _ _ _ Ht Ht2).
    have C := bsi_cumulative_service_inversion_related PR PL X sR sL Hs arrR arrL Harr pR pL Hp j.
    exact (sub_nat_eq_correspondence _ _ _ _ (C _ _ _ _ Ht1 Ht2)
      (svc_target_add_related _ _ _ _ (C _ _ _ _ Ht1 Ht) (C _ _ _ _ Ht Ht2))).
  Qed.

  Definition src_service_inversion_widen : Prop :=
    ltac:(body_of (fun s : S.statement_service_inversion_widen => s Job)).
  Definition tgt_service_inversion_widen : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_ServiceInversion_service_inversion_widen
      Job dJ)).

  Theorem service_inversion_widen_correspondence :
    PropSPropRel src_service_inversion_widen tgt_service_inversion_widen.
  Proof.
    unfold src_service_inversion_widen, tgt_service_inversion_widen.
    M_ps. M_arr. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). M_jldp. M_id j.
    M_nat alR alL Hal. M_nat arR arL Har. M_nat blR blL Hbl. M_nat brR brL Hbr.
    imp (sub_nat_le_correspondence _ _ _ _ Hbl Hal).
    imp (sub_nat_le_correspondence _ _ _ _ Har Hbr).
    have C := bsi_cumulative_service_inversion_related PR PL X sR sL Hs arrR arrL Harr pR pL Hp j.
    exact (sub_nat_le_correspondence _ _ _ _ (C _ _ _ _ Hal Har) (C _ _ _ _ Hbl Hbr)).
  Qed.

  Definition src_receives_service_implies_no_service_inversion : Prop :=
    ltac:(body_of (fun s : S.statement_receives_service_implies_no_service_inversion => s Job)).
  Definition tgt_receives_service_implies_no_service_inversion : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_ServiceInversion_receives_service_implies_no_service_inversion
        Job dJ)).

  Theorem receives_service_implies_no_service_inversion_correspondence :
    PropSPropRel src_receives_service_implies_no_service_inversion
      tgt_receives_service_implies_no_service_inversion.
  Proof.
    unfold src_receives_service_implies_no_service_inversion,
      tgt_receives_service_implies_no_service_inversion.
    M_ps. imp (isj_psr_uniprocessor_related Job PR PL X).
    M_arr. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). M_jldp. imp
      (bsi_reflexive_priorities_rel pR pL Hp).
    M_id j. M_nat tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (bsi_receives_service_at_related PR PL X sR sL Hs j tR tL Ht)).
    exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
      (bsi_service_inversion_related PR PL X sR sL Hs arrR arrL Harr pR pL Hp j tR tL Ht))).
  Qed.

  (** ** Statements with an arrival input *)

  Section Arrival.
    Variable jaR : prosa.behavior.job.JobArrival Job.
    Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
    Hypothesis Hja : ArJobArrivalRel Job jaR jaL.


    Definition src_idle_implies_no_service_inversion : Prop :=
      ltac:(body_of (fun s : S.statement_idle_implies_no_service_inversion => s Job jaR)).
    Definition tgt_idle_implies_no_service_inversion : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_BusyInterval_ServiceInversion_idle_implies_no_service_inversion Job dJ jaL)).

    Theorem idle_implies_no_service_inversion_correspondence :
      PropSPropRel src_idle_implies_no_service_inversion tgt_idle_implies_no_service_inversion.
    Proof.
      unfold src_idle_implies_no_service_inversion, tgt_idle_implies_no_service_inversion.
      M_ps. M_arr. imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja
        Harr). (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). (imp (fpre_come_from_rel Job PR
        PL X sR sL Hs arrR arrL Harr); imp (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs)).
        M_jldp. M_id j. M_nat tR tL Ht.
      imp (ar_bool_truth_correspondence _ _ (fpre_is_idle_related Job PR PL X sR sL Hs arrR arrL Harr _
        _ Ht)).
      exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (bsi_service_inversion_related PR PL X sR sL Hs arrR arrL Harr pR pL Hp j tR tL Ht))).
    Qed.

    Definition src_service_inversion_supply_sched : Prop :=
      ltac:(body_of (fun s : S.statement_service_inversion_supply_sched => s Job jaR)).
    Definition tgt_service_inversion_supply_sched : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_BusyInterval_ServiceInversion_service_inversion_supply_sched Job dJ jaL)).

    Theorem service_inversion_supply_sched_correspondence :
      PropSPropRel src_service_inversion_supply_sched tgt_service_inversion_supply_sched.
    Proof.
      unfold src_service_inversion_supply_sched, tgt_service_inversion_supply_sched.
      M_ps. imp (isj_psr_uniprocessor_related Job PR PL X). imp (bsi_fully_consuming_related PR PL X).
      M_arr. imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
        (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). (imp (fpre_come_from_rel Job PR PL X
        sR sL Hs arrR arrL Harr); imp (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs)). M_jldp.
        imp (bsi_reflexive_priorities_rel pR pL Hp).
      M_nat tR tL Ht.
      imp (ar_bool_truth_correspondence _ _ (bsi_has_supply_related PR PL X sR sL Hs tR tL Ht)).
      M_id j. M_id j'.
      imp (ar_bool_truth_correspondence _ _ (fpre_scheduled_at_related Job PR PL X sR sL Hs j _ _ Ht)).
      exact (ar_bool_eq_correspondence _ _ _ _
        (bsi_service_inversion_related PR PL X sR sL Hs arrR arrL Harr pR pL Hp j' tR tL Ht)
        (svc_bool_not_related _ _ (Hp tR tL Ht j j'))).
    Qed.

    Definition src_service_inv_implies_priority_inv : Prop :=
      ltac:(body_of (fun s : S.statement_service_inv_implies_priority_inv => s Job jaR)).
    Definition tgt_service_inv_implies_priority_inv : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_BusyInterval_ServiceInversion_service_inv_implies_priority_inv Job dJ jaL)).

    Theorem service_inv_implies_priority_inv_correspondence :
      PropSPropRel src_service_inv_implies_priority_inv tgt_service_inv_implies_priority_inv.
    Proof.
      unfold src_service_inv_implies_priority_inv, tgt_service_inv_implies_priority_inv.
      M_ps. imp (isj_psr_uniprocessor_related Job PR PL X).
      M_arr. imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
        (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). (imp (fpre_come_from_rel Job PR PL X
        sR sL Hs arrR arrL Harr); imp (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs)). M_jlfp.
        imp (fpre_reflexive_rel Job pR pL Hp).
      M_id j. M_nat tR tL Ht.
      imp (ar_bool_truth_correspondence _ _ (bsi_service_inversion_related PR PL X sR sL Hs arrR arrL Harr
        _ _ (bsi_jlfp_to_jldp_rel pR pL Hp) j tR tL Ht)).
      exact (ar_bool_truth_correspondence _ _
        (ex_priority_inversion_related Job PR PL X sR sL Hs arrR arrL Harr pR pL Hp j tR tL Ht)).
    Qed.

    Definition src_cumul_service_inv_le_cumul_priority_inv : Prop :=
      ltac:(body_of (fun s : S.statement_cumul_service_inv_le_cumul_priority_inv => s Job jaR)).
    Definition tgt_cumul_service_inv_le_cumul_priority_inv : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_BusyInterval_ServiceInversion_cumul_service_inv_le_cumul_priority_inv
          Job dJ jaL)).

    Theorem cumul_service_inv_le_cumul_priority_inv_correspondence :
      PropSPropRel src_cumul_service_inv_le_cumul_priority_inv tgt_cumul_service_inv_le_cumul_priority_inv.
    Proof.
      unfold src_cumul_service_inv_le_cumul_priority_inv, tgt_cumul_service_inv_le_cumul_priority_inv.
      M_ps. imp (isj_psr_uniprocessor_related Job PR PL X).
      M_arr. imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
        (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). (imp (fpre_come_from_rel Job PR PL X
        sR sL Hs arrR arrL Harr); imp (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs)). M_jlfp.
        imp (fpre_reflexive_rel Job pR pL Hp).
      M_id j. M_nat t1R t1L Ht1. M_nat t2R t2L Ht2.
      exact (sub_nat_le_correspondence _ _ _ _
        (bsi_cumulative_service_inversion_related PR PL X sR sL Hs arrR arrL Harr
          _ _ (bsi_jlfp_to_jldp_rel pR pL Hp) j _ _ _ _ Ht1 Ht2)
        (ex_cumulative_priority_inversion_related Job PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _
          Ht1 Ht2)).
    Qed.

    (** ** Statements over busy-interval prefixes *)

    Variable costR : prosa.behavior.job.JobCost Job.
    Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
    Hypothesis Hcost : SvcJobCostRel Job costR costL.

    (** The common preamble: processor model, policy, arrival sequence,
        schedule, readiness and preemption model. *)

    Definition src_cumulative_service_inversion_from_one_job : Prop :=
      ltac:(body_of (fun s : S.statement_cumulative_service_inversion_from_one_job => s Job jaR costR)).
    Definition tgt_cumulative_service_inversion_from_one_job : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_BusyInterval_ServiceInversion_cumulative_service_inversion_from_one_job
          Job dJ jaL costL)).

    Theorem cumulative_service_inversion_from_one_job_correspondence :
      PropSPropRel src_cumulative_service_inversion_from_one_job
        tgt_cumulative_service_inversion_from_one_job.
    Proof.
      unfold src_cumulative_service_inversion_from_one_job, tgt_cumulative_service_inversion_from_one_job.
      (M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); imp (bsi_unit_supply_related PR PL X)).
        M_jlfp. imp (fpre_reflexive_rel Job pR pL Hp). imp (hap_transitive_rel Job pR pL Hp).
      (M_arr; imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr);
        (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs); apply (fpre_forall_jr Job jaR jaL Hja
        costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr; imp (ex_work_bearing_related Job jaR
        jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp
        (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr);
        M_jp; imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
        jpR jpL Hjp)). imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL
        Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp).
      M_id j. imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j)).
      (M_nat t1R t1L Ht1; M_nat t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR
        costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)).
      M_nat tR tL Ht. imp (sub_nat_le_correspondence _ _ _ _ Ht Ht2).
      have C := bsi_cumulative_service_inversion_related PR PL X sR sL Hs arrR arrL Harr
        _ _ (bsi_jlfp_to_jldp_rel pR pL Hp) j _ _ _ _ Ht1 Ht.
      imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) C).
      apply ex_exists_identity. intro jlp.
      apply ar_and_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (Hja jlp) Ht1)|].
      apply ar_and_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hp jlp j)))|].
      exact (sub_nat_eq_correspondence _ _ _ _ C
        (isj_service_during_related Job PR PL sR sL (isj_psr_service_at_related Job PR PL X sR sL Hs)
          jlp _ _ _ _ Ht1 Ht)).
    Qed.

    Section Task.
      Context (Task : eqType).
      Let dT := ar_decidable_eq Task.
      Variable mR : TPS.TaskMaxNonpreemptiveSegment Task.
      Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
      Hypothesis Hm : TppMaxSegmentRel Task mR mL.
      Variable jtR : prosa.model.task.concept.JobTask Job Task.
      Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
      Hypothesis Hjt : forall j : Job,
        Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
          (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).


      Definition src_lp_job_bounded_service : Prop :=
        ltac:(body_of (fun s : S.statement_lp_job_bounded_service => s Task mR Job jtR jaR costR)).
      Definition tgt_lp_job_bounded_service : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_ServiceInversion_lp_job_bounded_service
          Job dJ Task dT mL jtL jaL costL)).

      Theorem lp_job_bounded_service_correspondence :
        PropSPropRel src_lp_job_bounded_service tgt_lp_job_bounded_service.
      Proof.
        unfold src_lp_job_bounded_service, tgt_lp_job_bounded_service.
        (M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); imp (bsi_unit_supply_related PR PL X)).
          M_jlfp. imp (hap_transitive_rel Job pR pL Hp).
        (M_arr; imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr);
          (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs); apply (fpre_forall_jr Job jaR jaL
          Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr; imp (ex_work_bearing_related Job
          jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp
          (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr);
          M_jp; imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL
          Harr jpR jpL Hjp)). imp (ar_and_correspondence _ _ _ _ (fpre_valid_preemption_model_rel Job
          costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp)
          (model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt costR costL
          Hcost mR mL Hm jpR jpL Hjp arrR arrL Harr)). imp (fpre_respects_jlfp_rel Job jaR jaL costR
          costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp). (M_id j; imp
          (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp
          (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j));
          M_id jlp; imp (arrives_in_correspondence_certificate Job arrR arrL jlp Harr); imp
          (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hp jlp j)))).
        (M_nat t1R t1L Ht1; M_nat t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja
          costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)).
        M_nat tR tL Ht. imp (sub_nat_le_correspondence _ _ _ _ Ht Ht2).
        exact (sub_nat_le_correspondence _ _ _ _
          (isj_service_during_related Job PR PL sR sL (isj_psr_service_at_related Job PR PL X sR sL Hs)
            jlp _ _ _ _ Ht1 Ht)
          (svc_target_sub_related _ _ _ _
            (job_max_nonpreemptive_segment_correspondence Job costR costL Hcost jpR jpL Hjp jlp)
            (sub_nat_rel_canonical 1))).
      Qed.

      Definition src_lp_job_bounded_service_max : Prop :=
        ltac:(body_of (fun s : S.statement_lp_job_bounded_service_max => s Task mR Job jtR jaR costR)).
      Definition tgt_lp_job_bounded_service_max : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_ServiceInversion_lp_job_bounded_service_max
          Job dJ Task dT mL jtL jaL costL)).

      Theorem lp_job_bounded_service_max_correspondence :
        PropSPropRel src_lp_job_bounded_service_max tgt_lp_job_bounded_service_max.
      Proof.
        unfold src_lp_job_bounded_service_max, tgt_lp_job_bounded_service_max.
        (M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); imp (bsi_unit_supply_related PR PL X)).
          M_jlfp. imp (hap_transitive_rel Job pR pL Hp).
        (M_arr; imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr);
          (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs); apply (fpre_forall_jr Job jaR jaL
          Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr; imp (ex_work_bearing_related Job
          jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp
          (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr);
          M_jp; imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL
          Harr jpR jpL Hjp)). imp (ar_and_correspondence _ _ _ _ (fpre_valid_preemption_model_rel Job
          costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp)
          (model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt costR costL
          Hcost mR mL Hm jpR jpL Hjp arrR arrL Harr)). imp (fpre_respects_jlfp_rel Job jaR jaL costR
          costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp). (M_id j; imp
          (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp
          (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j));
          M_id jlp; imp (arrives_in_correspondence_certificate Job arrR arrL jlp Harr); imp
          (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hp jlp j)))).
        (M_nat t1R t1L Ht1; M_nat t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja
          costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)).
        M_nat tR tL Ht. imp (sub_nat_le_correspondence _ _ _ _ Ht Ht2).
        exact (sub_nat_le_correspondence _ _ _ _
          (isj_service_during_related Job PR PL sR sL (isj_psr_service_at_related Job PR PL X sR sL Hs)
            jlp _ _ _ _ Ht1 Ht)
          (max_lp_nonpreemptive_segment_correspondence Job costR costL Hcost arrR arrL Harr pR pL Hp
            jpR jpL Hjp j _ _ Ht1)).
      Qed.

      Definition src_service_inversion_is_bounded : Prop :=
        ltac:(body_of (fun s : S.statement_service_inversion_is_bounded => s Task mR Job jtR jaR costR)).
      Definition tgt_service_inversion_is_bounded : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_ServiceInversion_service_inversion_is_bounded
          Job dJ Task dT mL jtL jaL costL)).

      Theorem service_inversion_is_bounded_correspondence :
        PropSPropRel src_service_inversion_is_bounded tgt_service_inversion_is_bounded.
      Proof.
        unfold src_service_inversion_is_bounded, tgt_service_inversion_is_bounded.
        (M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); imp (bsi_unit_supply_related PR PL X)).
          M_jlfp. imp (fpre_reflexive_rel Job pR pL Hp). imp (hap_transitive_rel Job pR pL Hp).
        (M_arr; imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr);
          (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs); apply (fpre_forall_jr Job jaR jaL
          Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr; imp (ex_work_bearing_related Job
          jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp
          (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr);
          M_jp; imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL
          Harr jpR jpL Hjp)). imp (ar_and_correspondence _ _ _ _ (fpre_valid_preemption_model_rel Job
          costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp)
          (model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt costR costL
          Hcost mR mL Hm jpR jpL Hjp arrR arrL Harr)). imp (fpre_respects_jlfp_rel Job jaR jaL costR
          costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp).
        M_id tsk. apply ex_forall_fun. intros BR BL HB.
        apply ar_imp_correspondence.
        { M_id j. M_nat t1R t1L Ht1. M_nat t2R t2L Ht2.
          imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
          imp (ar_bool_truth_correspondence _ _ (pi_job_of_task_related Task Job jtR jtL Hjt tsk j)).
          imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
            arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2).
          exact (sub_nat_le_correspondence _ _ _ _
            (max_lp_nonpreemptive_segment_correspondence Job costR costL Hcost arrR arrL Harr pR pL Hp
              jpR jpL Hjp j _ _ Ht1)
            (HB _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1))). }
        unfold SIB.service_inversion_is_bounded_by, SIP.pred_service_inversion_is_bounded_by,
          SIP.pred_service_inversion_of_job_is_bounded_by.
        cbn [I.Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_is_bounded_by
          I.Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_is_bounded_by
          I.Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_of_job_is_bounded_by].
        M_id j. imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
        imp (ar_bool_truth_correspondence _ _ (pi_job_of_task_related Task Job jtR jtL Hjt tsk j)).
        imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j)).
        (M_nat t1R t1L Ht1; M_nat t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja
          costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)).
        exact (sub_nat_le_correspondence _ _ _ _
          (bsi_cumulative_service_inversion_related PR PL X sR sL Hs arrR arrL Harr
            _ _ (bsi_jlfp_to_jldp_rel pR pL Hp) j _ _ _ _ Ht1 Ht2)
          (HB _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1))).
      Qed.
    End Task.
  End Arrival.
End ServiceInversion.
