(* Re-bound copy of accepted imported/translation_order/abstract_definitions/certificates/AbstractDefinitionsPendingOperations.v for the busy_sbf artifact; only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import behavior.service.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBusySbf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  ServiceBaseAdapter ServiceNatBoolOperations
  ServiceIntervalOperations ServiceScheduleOperations.

(** This is the smallest current-artifact instance of the already certified
    Service operation chain needed by quiet_time.  In particular, it does not
    import unrelated JobDeadline or the target abstract-definitions theorem. *)
Section PendingOperations.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState Job
      (svc_decidable_eq Job).
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedBusySbf.Prosa_Behavior_Schedule_schedule
    Job (svc_decidable_eq Job) PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedBusySbf.Prosa_Behavior_Job_JobCost Job
    (svc_decidable_eq Job).
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (ImportedBusySbf.Prosa_Behavior_Job_JobCost_job_cost Job
        (svc_decidable_eq Job) costL j).

  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : ImportedBusySbf.Prosa_Behavior_Job_JobArrival Job
    (svc_decidable_eq Job).
  Hypothesis Harrival : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job arrivalR j)
      (ImportedBusySbf.Prosa_Behavior_Job_JobArrival_job_arrival Job
        (svc_decidable_eq Job) arrivalL j).

  Lemma ad_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (ImportedBusySbf.Prosa_Behavior_Service_service_at Job
        (svc_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [ImportedBusySbf.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j
      (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma ad_receives_service_at_related (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.receives_service_at
        Job PStateR schedR j tR)
      (ImportedBusySbf.Prosa_Behavior_Service_receives_service_at
        Job (svc_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.receives_service_at.
    cbn [ImportedBusySbf.Prosa_Behavior_Service_receives_service_at].
    apply svc_decide_lt_related.
    - exact (sub_nat_rel_canonical O).
    - exact (ad_service_at_related j tR tL Ht).
  Qed.

  Lemma ad_service_during_related (j : Job)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.behavior.service.service_during Job PStateR
        schedR j t1R t2R)
      (ImportedBusySbf.Prosa_Behavior_Service_service_during Job
        (svc_decidable_eq Job) PStateL schedL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
      (fun t => ImportedBusySbf.Prosa_Behavior_Service_service_at
        Job (svc_decidable_eq Job) PStateL schedL j t)
      Ht1 Ht2 (fun tR tL Ht => ad_service_at_related j tR tL Ht).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (ImportedBusySbf.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job (svc_decidable_eq Job) PStateL schedL j t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Lemma ad_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
      (ImportedBusySbf.Prosa_Behavior_Service_service Job
        (svc_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service.
    cbn [ImportedBusySbf.Prosa_Behavior_Service_service].
    exact (ad_service_during_related j O tR Lean.Nat_zero tL
      (sub_nat_rel_canonical O) Ht).
  Qed.

  Lemma ad_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR
        schedR costR j tR)
      (ImportedBusySbf.Prosa_Behavior_Service_completed_by Job
        (svc_decidable_eq Job) PStateL schedL costL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.completed_by.
    cbn [ImportedBusySbf.Prosa_Behavior_Service_completed_by].
    exact (svc_decide_le_related _ _ _ _ (Hcost j)
      (ad_service_related j tR tL Ht)).
  Qed.

  Lemma ad_pending_earlier_and_at_related (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.pending_earlier_and_at Job PStateR
        schedR costR arrivalR j tR)
      (ImportedBusySbf.Prosa_Behavior_Service_pending_earlier_and_at
        Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.pending_earlier_and_at.
    cbn [ImportedBusySbf.Prosa_Behavior_Service_pending_earlier_and_at].
    apply svc_bool_and_related.
    - apply svc_decide_lt_related; [exact (Harrival j) | exact Ht].
    - exact (svc_bool_not_related _ _
        (ad_completed_by_related j tR tL Ht)).
  Qed.
End PendingOperations.

Print Assumptions ad_pending_earlier_and_at_related.
Print Assumptions ad_receives_service_at_related.
