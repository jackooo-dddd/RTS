From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import analysis.definitions.work_bearing_readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedWorkBearingReadiness ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedWorkBearingReadiness.

(** Definition certificate for [analysis/definitions/work_bearing_readiness.v].
    Inputs: job arrival/cost, processor state (two-sided
    [SvcProcessorStateRel]), the JobReady instance related on its operation
    for all related schedules (the accepted [RdyJobReadyRel] design of
    behavior/ready), arrival sequence, schedule, and the JLFP policy
    ([WbJLFPRel], with two-way totals).  The service operations are the
    accepted Service proofs re-instantiated at this artifact's identity. *)

Lemma wb_exists_identity (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (H x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x.
    exact (sprop_to_prop _ _ (H x) Hx).
Qed.

(** JLFP policies: pointwise Boolean relation with two-way totals. *)
Definition WbJLFPRel (Job : eqType)
    (pR : prosa.model.priority.definitions.JLFP_policy Job)
    (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job (ar_decidable_eq Job)) : SProp :=
  forall x y : Job,
    SvcBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job (ar_decidable_eq Job) pL x y).

Lemma JLFP_policy_source_total (Job : eqType) pR :
  WbJLFPRel Job pR
    (I.Prosa_Model_Priority_Definitions_JLFP_policy_mk Job (ar_decidable_eq Job)
      (fun x y => svc_bool_to_imported (@prosa.model.priority.definitions.hep_job Job pR x y))).
Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

Lemma JLFP_policy_target_total (Job : eqType) pL :
  WbJLFPRel Job
    (fun x y => svc_bool_to_rocq
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job (ar_decidable_eq Job) pL x y)) pL.
Proof. intros x y. exact (svc_bool_target_roundtrip _). Qed.

Section WorkBearingReadiness.
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
  Variable readyR : @prosa.behavior.ready.JobReady Job PStateR costR jaR.
  Variable readyL : I.Prosa_Behavior_Ready_JobReady Job dJ PStateL costL jaL.
  Definition WbJobReadyRel : SProp :=
    forall schedR' schedL',
      SvcScheduleRel Job PStateR PStateL R schedR' schedL' ->
    forall (j : Job) (tR : nat) (tL : Lean.Nat),
      SubNatRel tR tL ->
      SvcBoolRel
        (@prosa.behavior.ready.job_ready Job PStateR costR jaR readyR schedR' j tR)
        (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PStateL costL jaL readyL schedL' j tL).
  Hypothesis Hready : WbJobReadyRel.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hp : WbJLFPRel Job pR pL.

  Lemma wb_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [I.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma wb_service_during_related (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (I.Prosa_Behavior_Service_service_during Job dJ PStateL schedL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
      (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j t)
      Ht1 Ht2 (fun tR tL Ht => wb_service_at_related j tR tL Ht).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job dJ PStateL schedL j t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Lemma wb_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service.
    cbn [I.Prosa_Behavior_Service_service].
    exact (wb_service_during_related j O tR Lean.Nat_zero tL (sub_nat_rel_canonical O) Ht).
  Qed.

  Lemma wb_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR schedR costR j tR)
      (I.Prosa_Behavior_Service_completed_by Job dJ PStateL schedL costL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.completed_by.
    cbn [I.Prosa_Behavior_Service_completed_by].
    exact (svc_decide_le_related _ _ _ _ (Hcost j) (wb_service_related j tR tL Ht)).
  Qed.

  Lemma wb_pending_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.pending Job PStateR schedR costR jaR j tR)
      (I.Prosa_Behavior_Service_pending Job dJ PStateL schedL costL jaL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.pending.
    cbn [I.Prosa_Behavior_Service_pending].
    apply svc_bool_and_related.
    - exact (svc_has_arrived_related Job jaR jaL j Hja tR tL Ht).
    - exact (svc_bool_not_related _ _ (wb_completed_by_related j tR tL Ht)).
  Qed.

  Theorem work_bearing_readiness_correspondence :
    PropSPropRel
      (@prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness
        Job jaR costR PStateR readyR arrR schedR pR)
      (I.Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness
        Job dJ jaL costL PStateL readyL arrL schedL pL).
  Proof.
    unfold prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness.
    cbn [I.Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (wb_pending_related j tR tL Ht))|].
    apply wb_exists_identity => j_hp.
    apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j_hp Harr)|].
    apply ar_and_correspondence.
    - exact (svc_bool_truth_correspondence _ _ (Hready schedR schedL Hsched j_hp tR tL Ht)).
    - exact (svc_bool_truth_correspondence _ _ (Hp j_hp j)).
  Qed.
End WorkBearingReadiness.
