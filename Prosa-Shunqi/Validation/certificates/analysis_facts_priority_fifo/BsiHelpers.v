(* Helper-only copy of the accepted certificates/analysis_facts_busy_interval_service_inversion/
   BusyIntervalServiceInversionCorrespondence.v (re-bound to this export), truncated after its helper
   sections (before its statement correspondences, whose target statements are not part of this export),
   without its supply-model helpers (unit supply, supply/has-supply/blackout observations, fully consuming
   models), whose target constants are not part of this export; every other helper definition and proof is
   unchanged. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import BusyIntervalServiceInversionSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.processor.supply
  model.schedule.scheduled model.priority.classes model.job.properties
  analysis.definitions.work_bearing_readiness analysis.definitions.service.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPriorityFifo ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers
  TaskPreemptionParametersCorrespondence BusyIntervalPiHelpers ServiceInversionPredCorrespondence.

Module I := ImportedFactsPriorityFifo.
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


    Section Sched.
      Variable sR : @prosa.behavior.schedule.schedule Job PR.
      Variable sL : I.Prosa_Behavior_Schedule_schedule Job dJ PL.
      Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.

      Let Hse := isj_psr_service_at_related Job PR PL X sR sL Hs.


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

  End Pair.
End ServiceInversion.
