From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import analysis.definitions.carry_in.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedCarryIn ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedCarryIn.

(** Definition certificate for [analysis/definitions/carry_in.v]: for related
    inputs (job arrival, job cost, processor state with the two-sided
    [SvcProcessorStateRel], arrival sequence, schedule, instant) the source
    [no_carry_in] and the compiled Lean [no_carry_in] are related.  The
    service operations are the accepted Service proofs re-instantiated at
    this artifact's identity. *)

Section CarryIn.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Lemma ci_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [I.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma ci_service_during_related (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (I.Prosa_Behavior_Service_service_during Job dJ PStateL schedL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
      (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j t)
      Ht1 Ht2 (fun tR tL Ht => ci_service_at_related j tR tL Ht).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job dJ PStateL schedL j t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Lemma ci_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service.
    cbn [I.Prosa_Behavior_Service_service].
    exact (ci_service_during_related j O tR Lean.Nat_zero tL (sub_nat_rel_canonical O) Ht).
  Qed.

  Lemma ci_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR schedR costR j tR)
      (I.Prosa_Behavior_Service_completed_by Job dJ PStateL schedL costL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.completed_by.
    cbn [I.Prosa_Behavior_Service_completed_by].
    exact (svc_decide_le_related _ _ _ _ (Hcost j) (ci_service_related j tR tL Ht)).
  Qed.

  Theorem no_carry_in_correspondence (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    PropSPropRel
      (@prosa.analysis.definitions.carry_in.no_carry_in Job jaR costR arrR PStateR schedR tR)
      (I.Prosa_Analysis_Definitions_CarryIn_no_carry_in Job dJ jaL costL arrL PStateL schedL tL).
  Proof.
    intro Ht.
    unfold prosa.analysis.definitions.carry_in.no_carry_in.
    cbn [I.Prosa_Analysis_Definitions_CarryIn_no_carry_in].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _
        (arrived_before_correspondence_certificate Job jaR jaL j Hja tR tL Ht))|].
    exact (ar_bool_truth_correspondence _ _ (ci_completed_by_related j tR tL Ht)).
  Qed.
End CarryIn.
