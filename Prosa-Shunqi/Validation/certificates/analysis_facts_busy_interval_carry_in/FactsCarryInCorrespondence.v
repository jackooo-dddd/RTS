From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsCarryInSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.processor.supply
  model.schedule.scheduled model.priority.classes model.schedule.work_conserving model.job.properties
  model.aggregate.service_of_jobs model.aggregate.workload analysis.definitions.carry_in
  analysis.definitions.work_bearing_readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsCarryIn ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers.

Module I := ImportedFactsCarryIn.
Module S := FactsCarryInSemanticSource.FactsCarryInSemanticSource.

(** Statement correspondence for [analysis/facts/busy_interval/carry_in.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (job type, arrival and cost classes, arrival
    sequence); target side: the imported Lean theorem types.  Inputs:
    [job_arrival] by [ArJobArrivalRel], [job_cost] by the accepted
    [SvcJobCostRel], arrival sequences by [ArArrivalSequenceRel].  Inputs
    quantified inside a statement are covered in both directions by the
    accepted conversions: processor models ([isj_cover_pstate]), schedules
    through the processor-model relation ([fpre_forall_sched]), JLFP policies
    ([fpre_forall_jlfp]), the readiness instance on the statement's schedule
    pair ([fpre_forall_jr]), jobs (identity) and instants.  Over related
    schedules, the supply at an instant is related through the supply field
    of the processor-model relation, and blackouts and blackout counts are
    related by replaying the accepted supply certificate (the blackout count
    through its kernel-guarded interval-sum projection); absence of carry-in
    is related by unfolding over the accepted completion relation; the
    fully-consuming property by covering schedules; the busy interval, work
    conservation, work-bearing readiness, unit service and the service of
    sets of jobs are the accepted busy-interval-existence helpers; the total
    workload is the accepted workload certificate.  No source or target
    theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section FactsCarryIn.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Section Pair.
    Variable PR : prosa.behavior.schedule.ProcessorState Job.
    Variable PL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
    Variable X : IsjPSRel Job PR PL.

    Section Sched.
      Variable sR : @prosa.behavior.schedule.schedule Job PR.
      Variable sL : I.Prosa_Behavior_Schedule_schedule Job dJ PL.
      Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.

      Lemma fci_supply_at_related (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        SubNatRel (@prosa.model.processor.supply.supply_at Job PR sR tR)
          (I.Prosa_Model_Processor_Supply_supply_at Job dJ PL sL tL).
      Proof.
        intro Ht. unfold prosa.model.processor.supply.supply_at.
        cbn [I.Prosa_Model_Processor_Supply_supply_at].
        exact (isj_lean_transport
          (fun sL' => SubNatRel (@prosa.behavior.schedule.supply_in Job PR (sR tR))
             (I.Prosa_Behavior_Schedule_ProcessorState_supply_in Job dJ PL sL'))
          _ _ (Hs tR tL Ht) (isj_sup_in_rel Job PR PL X (sR tR))).
      Qed.

      Lemma fci_is_blackout_related (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        SvcBoolRel (@prosa.model.processor.supply.is_blackout Job PR sR tR)
          (I.Prosa_Model_Processor_Supply_is_blackout Job dJ PL sL tL).
      Proof.
        intro Ht. unfold prosa.model.processor.supply.is_blackout, prosa.model.processor.supply.has_supply.
        cbn [I.Prosa_Model_Processor_Supply_is_blackout I.Prosa_Model_Processor_Supply_has_supply].
        exact (svc_bool_not_related _ _ (svc_decide_lt_related _ _ _ _
          (sub_nat_rel_canonical O) (fci_supply_at_related tR tL Ht))).
      Qed.

      Lemma fci_blackout_during_related (t1R t2R : nat) (t1L t2L : Lean.Nat) :
        SubNatRel t1R t1L -> SubNatRel t2R t2L ->
        SubNatRel (@prosa.model.processor.supply.blackout_during Job PR sR t1R t2R)
          (I.Prosa_Model_Processor_Supply_blackout_during Job dJ PL sL t1L t2L).
      Proof.
        intros Ht1 Ht2.
        have Hsum := svc_interval_sum_related t1R t2R t1L t2L
          (fun t => nat_of_bool (@prosa.model.processor.supply.is_blackout Job PR sR t))
          (fun t => I.Bool_toNat (I.Prosa_Model_Processor_Supply_is_blackout Job dJ PL sL t))
          Ht1 Ht2 (fun tR tL Ht => isj_bool_to_nat_related _ _ (fci_is_blackout_related tR tL Ht)).
        change (SubNatRel
          (@prosa.model.processor.supply.blackout_during Job PR sR t1R t2R)
          (I.Prosa_Validation_SupplyInterface_blackoutDuringProjection Job dJ PL sL t1L t2L)) in Hsum.
        exact Hsum.
      Qed.

      Section Arr.
        Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
        Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
        Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

        Lemma fci_no_carry_in_related (tR : nat) (tL : Lean.Nat) :
          SubNatRel tR tL ->
          PropSPropRel (@prosa.analysis.definitions.carry_in.no_carry_in Job jaR costR arrR PR sR tR)
            (I.Prosa_Analysis_Definitions_CarryIn_no_carry_in Job dJ jaL costL arrL PL sL tL).
        Proof.
          intro Ht. unfold prosa.analysis.definitions.carry_in.no_carry_in.
          cbn [I.Prosa_Analysis_Definitions_CarryIn_no_carry_in].
          apply ar_forall_identity_correspondence. intro j_o.
          apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j_o
            Harr)|].
          apply ar_imp_correspondence;
            [exact (ar_bool_truth_correspondence _ _
              (arrived_before_correspondence_certificate Job jaR jaL j_o Hja tR tL Ht))|].
          exact (ar_bool_truth_correspondence _ _
            (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs j_o tR tL Ht)).
        Qed.

        Lemma fci_total_workload_between_related (t1R t2R : nat) (t1L t2L : Lean.Nat) :
          SubNatRel t1R t1L -> SubNatRel t2R t2L ->
          SubNatRel (@prosa.model.aggregate.workload.total_workload_between Job costR arrR t1R t2R)
            (I.Prosa_Model_Aggregate_Workload_total_workload_between Job dJ costL arrL t1L t2L).
        Proof.
          intros Ht1 Ht2.
          exact (total_workload_between_correspondence Job costR costL Hcost arrR arrL Harr _ _ _ _ Ht1 Ht2).
        Qed.
      End Arr.
    End Sched.

    Lemma fci_fully_consuming_related :
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
        (fci_supply_at_related sR sL Hs _ _ Ht)).
    Qed.
  End Pair.

  (** ** Statement correspondences *)

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].
  Local Ltac M_va := imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
  Local Ltac M_ps := apply (isj_cover_pstate Job); intros PR PL X.
  Local Ltac M_jlfp := apply fpre_forall_jlfp; intros pR pL Hp.

  Definition src_no_carry_in_at_zero : Prop :=
    ltac:(body_of (fun s : S.statement_no_carry_in_at_zero => s Job jaR costR arrR)).
  Definition tgt_no_carry_in_at_zero : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_CarryIn_no_carry_in_at_zero Job dJ jaL
      costL arrL)).

  Theorem no_carry_in_at_zero_correspondence :
    PropSPropRel src_no_carry_in_at_zero tgt_no_carry_in_at_zero.
  Proof.
    unfold src_no_carry_in_at_zero, tgt_no_carry_in_at_zero.
    M_ps. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). exact (fci_no_carry_in_related PR PL
      X sR sL Hs arrR arrL Harr _ _ (sub_nat_rel_canonical O)).
  Qed.

  Definition src_pending_job_not_idle : Prop :=
    ltac:(body_of (fun s : S.statement_pending_job_not_idle => s Job jaR costR arrR)).
  Definition tgt_pending_job_not_idle : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_CarryIn_pending_job_not_idle Job dJ jaL
      costL arrL)).

  Theorem pending_job_not_idle_correspondence :
    PropSPropRel src_pending_job_not_idle tgt_pending_job_not_idle.
  Proof.
    unfold src_pending_job_not_idle, tgt_pending_job_not_idle.
    M_va. M_ps. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). imp (fpre_come_from_rel Job PR
      PL X sR sL Hs arrR arrL Harr). imp (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs).
      M_jlfp. (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL
      Hjr). imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
      Harr pR pL Hp jrR jrL Hjr). imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL
      Hs arrR arrL Harr jrR jrL Hjr).
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _
      (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs j _ _ Ht)).
    apply pi_not_correspondence. exact (ar_bool_truth_correspondence _ _ (fpre_is_idle_related Job PR PL
      X sR sL Hs arrR arrL Harr _ _ Ht)).
  Qed.

  Definition src_idle_instant_no_carry_in : Prop :=
    ltac:(body_of (fun s : S.statement_idle_instant_no_carry_in => s Job jaR costR arrR)).
  Definition tgt_idle_instant_no_carry_in : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_CarryIn_idle_instant_no_carry_in
      Job dJ jaL costL arrL)).

  Theorem idle_instant_no_carry_in_correspondence :
    PropSPropRel src_idle_instant_no_carry_in tgt_idle_instant_no_carry_in.
  Proof.
    unfold src_idle_instant_no_carry_in, tgt_idle_instant_no_carry_in.
    M_va. M_ps. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). imp (fpre_come_from_rel Job PR
      PL X sR sL Hs arrR arrL Harr). imp (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs).
      M_jlfp. (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL
      Hjr). imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
      Harr pR pL Hp jrR jrL Hjr). imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL
      Hs arrR arrL Harr jrR jrL Hjr).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (fpre_is_idle_related Job PR
      PL X sR sL Hs arrR arrL Harr _ _ Ht))|].
    exact (fci_no_carry_in_related PR PL X sR sL Hs arrR arrL Harr _ _ Ht).
  Qed.

  Definition src_idle_instant_next_no_carry_in : Prop :=
    ltac:(body_of (fun s : S.statement_idle_instant_next_no_carry_in => s Job jaR costR arrR)).
  Definition tgt_idle_instant_next_no_carry_in : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_CarryIn_idle_instant_next_no_carry_in
      Job dJ jaL costL arrL)).

  Theorem idle_instant_next_no_carry_in_correspondence :
    PropSPropRel src_idle_instant_next_no_carry_in tgt_idle_instant_next_no_carry_in.
  Proof.
    unfold src_idle_instant_next_no_carry_in, tgt_idle_instant_next_no_carry_in.
    M_va. M_ps. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). imp (fpre_come_from_rel Job PR
      PL X sR sL Hs arrR arrL Harr). imp (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs).
      M_jlfp. (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL
      Hjr). imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
      Harr pR pL Hp jrR jrL Hjr). imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL
      Hs arrR arrL Harr jrR jrL Hjr).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (fpre_is_idle_related Job PR
      PL X sR sL Hs arrR arrL Harr _ _ Ht))|].
    exact (fci_no_carry_in_related PR PL X sR sL Hs arrR arrL Harr _ _ (pp_succ_related _ _ Ht)).
  Qed.

  Definition src_total_service_is_bounded_by_Δ : Prop :=
    ltac:(body_of (fun s : S.statement_total_service_is_bounded_by_Δ => s Job jaR arrR)).
  Definition tgt_total_service_is_bounded_by_Δ : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_CarryIn_total_service_is_bounded_by__UU0394_
      Job dJ jaL arrL)).

  Theorem total_service_is_bounded_by_Δ_correspondence :
    PropSPropRel src_total_service_is_bounded_by_Δ tgt_total_service_is_bounded_by_Δ.
  Proof.
    unfold src_total_service_is_bounded_by_Δ, tgt_total_service_is_bounded_by_Δ.
    M_va. M_ps. imp (isj_psr_uniprocessor_related Job PR PL X). (apply (fpre_forall_sched Job PR PL X);
      intros sR sL Hs).
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    imp (ex_unit_service_related Job PR PL X).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply sub_nat_le_correspondence; [exact (svc_target_add_related _ _ _ _ (fci_blackout_during_related
      PR PL X sR sL Hs _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht Hd)) (ex_total_service_related Job
      PR PL X sR sL Hs _ _ (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _
      (sub_nat_rel_canonical O) (svc_target_add_related _ _ _ _ Ht Hd)) _ _ _ _ Ht
      (svc_target_add_related _ _ _ _ Ht Hd)))|exact Hd].
  Qed.

  Definition src_low_total_service_implies_existence_of_time_with_no_carry_in : Prop :=
    ltac:(body_of (fun s : S.statement_low_total_service_implies_existence_of_time_with_no_carry_in =>
      s Job jaR costR arrR)).
  Definition tgt_low_total_service_implies_existence_of_time_with_no_carry_in : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_CarryIn_low_total_service_implies_existence_of_time_with_no_carry_in
      Job dJ jaL costL arrL)).

  Theorem low_total_service_implies_existence_of_time_with_no_carry_in_correspondence :
    PropSPropRel src_low_total_service_implies_existence_of_time_with_no_carry_in
      tgt_low_total_service_implies_existence_of_time_with_no_carry_in.
  Proof.
    unfold src_low_total_service_implies_existence_of_time_with_no_carry_in,
      tgt_low_total_service_implies_existence_of_time_with_no_carry_in.
    M_va. M_ps. imp (isj_psr_uniprocessor_related Job PR PL X). imp (fci_fully_consuming_related PR PL
      X). (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). imp (fpre_come_from_rel Job PR PL X
      sR sL Hs arrR arrL Harr). imp (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs). M_jlfp.
      (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr).
      imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR
      pL Hp jrR jrL Hjr). imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL Hs arrR
      arrL Harr jrR jrL Hjr).
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [apply sub_nat_lt_correspondence; [exact (svc_target_add_related _ _ _
      _ (fci_blackout_during_related PR PL X sR sL Hs _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht Hd))
      (ex_total_service_related Job PR PL X sR sL Hs _ _ (arrivals_between_correspondence_certificate
      Job arrR arrL Harr _ _ _ _ (sub_nat_rel_canonical O) (svc_target_add_related _ _ _ _ Ht Hd)) _ _ _
      _ Ht (svc_target_add_related _ _ _ _ Ht Hd)))|exact Hd]|].
    apply ar_exists_nat_correspondence. intros eR eL He.
    apply ar_and_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ He Hd)|].
    exact (fci_no_carry_in_related PR PL X sR sL Hs arrR arrL Harr _ _ (svc_target_add_related _ _ _ _
      (pp_succ_related _ _ Ht) He)).
  Qed.

  Definition src_completion_of_all_jobs_implies_no_carry_in : Prop :=
    ltac:(body_of (fun s : S.statement_completion_of_all_jobs_implies_no_carry_in => s Job jaR costR arrR)).
  Definition tgt_completion_of_all_jobs_implies_no_carry_in : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_CarryIn_completion_of_all_jobs_implies_no_carry_in
      Job dJ jaL costL arrL)).

  Theorem completion_of_all_jobs_implies_no_carry_in_correspondence :
    PropSPropRel src_completion_of_all_jobs_implies_no_carry_in
      tgt_completion_of_all_jobs_implies_no_carry_in.
  Proof.
    unfold src_completion_of_all_jobs_implies_no_carry_in, tgt_completion_of_all_jobs_implies_no_carry_in.
    M_va. M_ps. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). imp (fpre_must_arrive_rel Job
      jaR jaL Hja PR PL X sR sL Hs). imp (ex_completed_dont_execute_rel Job costR costL Hcost PR PL X sR
      sL Hs).
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    apply ar_imp_correspondence; [(apply ar_forall_nat_correspondence; let tR := fresh "tR" in let tL :=
      fresh "tL" in let Ht := fresh "Ht" in intros tR tL Ht; apply ar_imp_correspondence; [exact
      (fci_no_carry_in_related PR PL X sR sL Hs arrR arrL Harr _ _ Ht)|]; exact
      (sub_nat_le_correspondence _ _ _ _ (svc_target_add_related _ _ _ _ (fci_blackout_during_related PR
      PL X sR sL Hs _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht Hd))
      (fci_total_workload_between_related arrR arrL Harr _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht
      Hd))) Hd))|].
    imp (ex_unit_service_related Job PR PL X).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (fci_no_carry_in_related PR PL X sR sL Hs arrR arrL Harr _ _ Ht)|].
    apply ar_imp_correspondence; [apply sub_nat_eq_correspondence; [exact (svc_target_add_related _ _ _
      _ (fci_blackout_during_related PR PL X sR sL Hs _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht Hd))
      (ex_total_service_related Job PR PL X sR sL Hs _ _ (arrivals_between_correspondence_certificate
      Job arrR arrL Harr _ _ _ _ (sub_nat_rel_canonical O) (svc_target_add_related _ _ _ _ Ht Hd)) _ _ _
      _ Ht (svc_target_add_related _ _ _ _ Ht Hd)))|exact Hd]|].
    exact (fci_no_carry_in_related PR PL X sR sL Hs arrR arrL Harr _ _ (svc_target_add_related _ _ _ _
      Ht Hd)).
  Qed.

  Definition src_processor_is_not_too_busy : Prop :=
    ltac:(body_of (fun s : S.statement_processor_is_not_too_busy => s Job jaR costR arrR)).
  Definition tgt_processor_is_not_too_busy : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_CarryIn_processor_is_not_too_busy
      Job dJ jaL costL arrL)).

  Theorem processor_is_not_too_busy_correspondence :
    PropSPropRel src_processor_is_not_too_busy tgt_processor_is_not_too_busy.
  Proof.
    unfold src_processor_is_not_too_busy, tgt_processor_is_not_too_busy.
    M_va. M_ps. imp (isj_psr_uniprocessor_related Job PR PL X). imp (fci_fully_consuming_related PR PL
      X). (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). imp (fpre_come_from_rel Job PR PL X
      sR sL Hs arrR arrL Harr). imp (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs). imp
      (ex_completed_dont_execute_rel Job costR costL Hcost PR PL X sR sL Hs). M_jlfp. (apply
      (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr). imp
      (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL
      Hp jrR jrL Hjr). imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL Hs arrR
      arrL Harr jrR jrL Hjr).
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd).
    apply ar_imp_correspondence; [(apply ar_forall_nat_correspondence; let tR := fresh "tR" in let tL :=
      fresh "tL" in let Ht := fresh "Ht" in intros tR tL Ht; apply ar_imp_correspondence; [exact
      (fci_no_carry_in_related PR PL X sR sL Hs arrR arrL Harr _ _ Ht)|]; exact
      (sub_nat_le_correspondence _ _ _ _ (svc_target_add_related _ _ _ _ (fci_blackout_during_related PR
      PL X sR sL Hs _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht Hd))
      (fci_total_workload_between_related arrR arrL Harr _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht
      Hd))) Hd))|].
    imp (ex_unit_service_related Job PR PL X).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_exists_nat_correspondence. intros eR eL He.
    apply ar_and_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ He Hd)|].
    exact (fci_no_carry_in_related PR PL X sR sL Hs arrR arrL Harr _ _ (svc_target_add_related _ _ _ _
      Ht He)).
  Qed.

  Definition src_busy_interval_from_total_workload_bound : Prop :=
    ltac:(body_of (fun s : S.statement_busy_interval_from_total_workload_bound => s Job jaR costR arrR)).
  Definition tgt_busy_interval_from_total_workload_bound : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_CarryIn_busy_interval_from_total_workload_bound
      Job dJ jaL costL arrL)).

  Theorem busy_interval_from_total_workload_bound_correspondence :
    PropSPropRel src_busy_interval_from_total_workload_bound tgt_busy_interval_from_total_workload_bound.
  Proof.
    unfold src_busy_interval_from_total_workload_bound, tgt_busy_interval_from_total_workload_bound.
    M_va. M_ps. imp (isj_psr_uniprocessor_related Job PR PL X). imp (fci_fully_consuming_related PR PL
      X). (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). imp (fpre_come_from_rel Job PR PL X
      sR sL Hs arrR arrL Harr). imp (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs). imp
      (ex_completed_dont_execute_rel Job costR costL Hcost PR PL X sR sL Hs). M_jlfp. imp
      (fpre_reflexive_rel Job pR pL Hp). (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL
      X sR sL Hs); intros jrR jrL Hjr). imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost
      PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr). imp (ex_work_conserving_related Job jaR jaL
      costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr).
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd).
    apply ar_imp_correspondence; [(apply ar_forall_nat_correspondence; let tR := fresh "tR" in let tL :=
      fresh "tL" in let Ht := fresh "Ht" in intros tR tL Ht; apply ar_imp_correspondence; [exact
      (fci_no_carry_in_related PR PL X sR sL Hs arrR arrL Harr _ _ Ht)|]; exact
      (sub_nat_le_correspondence _ _ _ _ (svc_target_add_related _ _ _ _ (fci_blackout_during_related PR
      PL X sR sL Hs _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht Hd))
      (fci_total_workload_between_related arrR arrL Harr _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht
      Hd))) Hd))|].
    imp (ex_unit_service_related Job PR PL X).
    apply ar_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j)).
    apply ar_exists_nat_correspondence. intros t1R t1L Ht1.
    apply ar_exists_nat_correspondence. intros t2R t2L Ht2.
    apply ar_and_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
        (ar_decide_le_related _ _ _ _ Ht1 (Hja j)) (ar_decide_lt_related _ _ _ _ (Hja j) Ht2)))|].
    apply ar_and_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _ Ht2 (svc_target_add_related _ _ _ _ Ht1 Hd))|].
    exact (ex_busy_interval_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
      arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2).
  Qed.
End FactsCarryIn.
