From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import BusyIntervalArrivalSemanticSource.
From prosa Require Import behavior.all model.priority.classes model.job.properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBusyIntervalArrival ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers.

Module I := ImportedBusyIntervalArrival.
Module S := BusyIntervalArrivalSemanticSource.BusyIntervalArrivalSemanticSource.

(** Statement correspondence for [analysis/facts/busy_interval/arrival.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (job type, arrival and cost classes); target side:
    the imported Lean theorem types.  Inputs: [job_arrival] by
    [ArJobArrivalRel], [job_cost] by the accepted [SvcJobCostRel].  Inputs
    quantified inside a statement are covered in both directions by the
    accepted conversions: JLFP policies ([fpre_forall_jlfp]), processor models
    ([isj_cover_pstate]), schedules through the processor-model relation
    ([fpre_forall_sched]), arrival sequences ([fpre_forall_arr]), jobs
    (identity) and instants.  Busy intervals and busy-interval prefixes are
    the accepted busy-interval-existence helpers; arrival at an instant is
    the accepted arrival-sequence certificate.  No source or target theorem is
    used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section BusyIntervalArrival.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Definition src_busy_interval_prefix_job_arrival : Prop :=
    ltac:(body_of (fun s : S.statement_busy_interval_prefix_job_arrival => s Job jaR costR)).
  Definition tgt_busy_interval_prefix_job_arrival : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Arrival_busy_interval_prefix_job_arrival
      Job dJ jaL costL)).

  Theorem busy_interval_prefix_job_arrival_correspondence :
    PropSPropRel src_busy_interval_prefix_job_arrival tgt_busy_interval_prefix_job_arrival.
  Proof.
    unfold src_busy_interval_prefix_job_arrival, tgt_busy_interval_prefix_job_arrival.
    apply fpre_forall_jlfp. intros pR pL Hp.
    apply (isj_cover_pstate Job). intros PR PL X.
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    apply (fpre_forall_arr Job). intros arrR arrL Harr.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_imp_correspondence;
      [exact (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
        arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)|].
    exact (sub_nat_le_correspondence _ _ _ _ Ht1 (Hja j)).
  Qed.

  Definition src_busy_interval_job_arrival : Prop :=
    ltac:(body_of (fun s : S.statement_busy_interval_job_arrival => s Job jaR costR)).
  Definition tgt_busy_interval_job_arrival : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Arrival_busy_interval_job_arrival
      Job dJ jaL costL)).

  Theorem busy_interval_job_arrival_correspondence :
    PropSPropRel src_busy_interval_job_arrival tgt_busy_interval_job_arrival.
  Proof.
    unfold src_busy_interval_job_arrival, tgt_busy_interval_job_arrival.
    apply fpre_forall_jlfp. intros pR pL Hp.
    apply (isj_cover_pstate Job). intros PR PL X.
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    apply (fpre_forall_arr Job). intros arrR arrL Harr.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_imp_correspondence;
      [exact (ex_busy_interval_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
        arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)|].
    exact (sub_nat_le_correspondence _ _ _ _ Ht1 (Hja j)).
  Qed.

  Definition src_busy_prefix_starts_when_hep_job_arrives : Prop :=
    ltac:(body_of (fun s : S.statement_busy_prefix_starts_when_hep_job_arrives => s Job jaR costR)).
  Definition tgt_busy_prefix_starts_when_hep_job_arrives : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Arrival_busy_prefix_starts_when_hep_job_arrives
      Job dJ jaL costL)).

  Theorem busy_prefix_starts_when_hep_job_arrives_correspondence :
    PropSPropRel src_busy_prefix_starts_when_hep_job_arrives tgt_busy_prefix_starts_when_hep_job_arrives.
  Proof.
    unfold src_busy_prefix_starts_when_hep_job_arrives, tgt_busy_prefix_starts_when_hep_job_arrives.
    apply fpre_forall_jlfp. intros pR pL Hp.
    apply ar_imp_correspondence; [exact (fpre_reflexive_rel Job pR pL Hp)|].
    apply (isj_cover_pstate Job). intros PR PL X.
    apply (fpre_forall_arr Job). intros arrR arrL Harr.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    apply ar_imp_correspondence; [exact (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j))|].
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_imp_correspondence;
      [exact (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
        arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)|].
    apply ex_exists_identity. intro j_a.
    apply ar_and_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (arrives_at_correspondence_certificate Job arrR arrL j_a Harr _ _ Ht1))|].
    exact (ar_bool_truth_correspondence _ _ (Hp j_a j)).
  Qed.
End BusyIntervalArrival.
