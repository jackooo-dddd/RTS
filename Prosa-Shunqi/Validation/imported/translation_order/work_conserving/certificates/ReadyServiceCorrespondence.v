(** Mechanically replayed accepted Ready proof for the exact imported artifact.
    source-sha256: 747555c503ac2c0f1eb882a8e5dbe786ade2067626bfd50a44fb19a3c3f1205f
    imported-artifact-sha256: 3952d4e1d2dc45e4d67bb664c9be76820ed73421d0e2483bc4dc66fb4feb7ac8 *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import behavior.service.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedWorkConserving ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ReadyBaseAdapter
  ReadyNatBoolOperations ReadyIntervalOperations
  ReadyScheduleOperations ReadyJobOperations.

(** The twelve v0.6 Service definitions, proved compositionally from the
actual imported Lean bodies and the separately audited operation relations. *)

Section ReadyServiceCorrespondence.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedWorkConserving.Prosa_Behavior_Schedule_ProcessorState Job
      (svc_decidable_eq Job).
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let StateR : Type := @prosa.behavior.schedule.State Job PStateR.
  Let StateL : Type :=
    ImportedWorkConserving.Prosa_Behavior_Schedule_ProcessorState_State Job
      (svc_decidable_eq Job) PStateL.

  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedWorkConserving.Prosa_Behavior_Schedule_schedule Job
    (svc_decidable_eq Job) PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Lemma scheduled_at_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR
        schedR j tR)
      (ImportedWorkConserving.Prosa_Behavior_Service_scheduled_at Job
        (svc_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.scheduled_at.
    cbn [ImportedWorkConserving.Prosa_Behavior_Service_scheduled_at].
    exact (svc_scheduled_in_related Job PStateR PStateL R j
      (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma service_at_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR
        schedR j tR)
      (ImportedWorkConserving.Prosa_Behavior_Service_service_at Job
        (svc_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [ImportedWorkConserving.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j
      (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma receives_service_at_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.receives_service_at Job PStateR
        schedR j tR)
      (ImportedWorkConserving.Prosa_Behavior_Service_receives_service_at Job
        (svc_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.receives_service_at.
    cbn [ImportedWorkConserving.Prosa_Behavior_Service_receives_service_at].
    apply svc_decide_lt_related.
    - exact (sub_nat_rel_canonical O).
    - exact (service_at_correspondence j tR tL Ht).
  Qed.

  Lemma service_during_correspondence (j : Job)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.behavior.service.service_during Job PStateR
        schedR j t1R t2R)
      (ImportedWorkConserving.Prosa_Behavior_Service_service_during Job
        (svc_decidable_eq Job) PStateL schedL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => @prosa.behavior.service.service_at Job PStateR
        schedR j t)
      (fun t => ImportedWorkConserving.Prosa_Behavior_Service_service_at Job
        (svc_decidable_eq Job) PStateL schedL j t)
      Ht1 Ht2 (fun tR tL Ht => service_at_correspondence j tR tL Ht).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR
        schedR j t1R t2R)
      (ImportedWorkConserving.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job (svc_decidable_eq Job) PStateL schedL j t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Lemma service_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
      (ImportedWorkConserving.Prosa_Behavior_Service_service Job
        (svc_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service.
    cbn [ImportedWorkConserving.Prosa_Behavior_Service_service].
    exact (service_during_correspondence j O tR Lean.Nat_zero tL
      (sub_nat_rel_canonical O) Ht).
  Qed.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedWorkConserving.Prosa_Behavior_Job_JobCost Job
    (svc_decidable_eq Job).
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : ImportedWorkConserving.Prosa_Behavior_Job_JobArrival Job
    (svc_decidable_eq Job).
  Hypothesis Harrival : SvcJobArrivalRel Job arrivalR arrivalL.

  Variable deadlineR : prosa.behavior.job.JobDeadline Job.
  Variable deadlineL : ImportedWorkConserving.Prosa_Behavior_Job_JobDeadline Job
    (svc_decidable_eq Job).
  Hypothesis Hdeadline : SvcJobDeadlineRel Job deadlineR deadlineL.

  Lemma completed_by_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR
        schedR costR j tR)
      (ImportedWorkConserving.Prosa_Behavior_Service_completed_by Job
        (svc_decidable_eq Job) PStateL schedL costL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.completed_by.
    cbn [ImportedWorkConserving.Prosa_Behavior_Service_completed_by].
    exact (svc_decide_le_related _ _ _ _ (Hcost j)
      (service_correspondence j tR tL Ht)).
  Qed.

  Lemma completes_at_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.completes_at Job PStateR
        schedR costR j tR)
      (ImportedWorkConserving.Prosa_Behavior_Service_completes_at Job
        (svc_decidable_eq Job) PStateL schedL costL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.completes_at.
    cbn [ImportedWorkConserving.Prosa_Behavior_Service_completes_at].
    apply svc_bool_and_related.
    - apply svc_bool_or_related.
      + apply svc_bool_not_related.
        apply completed_by_correspondence.
        rewrite -subn1.
        exact (svc_target_sub_related tR tL 1 svc_target_one Ht
          (sub_nat_rel_canonical 1)).
      + exact (svc_decide_eq_related tR tL O svc_target_zero Ht
          (sub_nat_rel_canonical O)).
    - exact (completed_by_correspondence j tR tL Ht).
  Qed.

  Lemma job_response_time_bound_correspondence (j : Job)
      (RR : nat) (RL : Lean.Nat) :
    SubNatRel RR RL ->
    SvcBoolRel
      (@prosa.behavior.service.job_response_time_bound Job PStateR
        schedR costR arrivalR j RR)
      (ImportedWorkConserving.Prosa_Behavior_Service_job_response_time_bound Job
        (svc_decidable_eq Job) PStateL schedL costL arrivalL j RL).
  Proof.
    intro HR. unfold prosa.behavior.service.job_response_time_bound.
    cbn [ImportedWorkConserving.Prosa_Behavior_Service_job_response_time_bound].
    apply completed_by_correspondence.
    exact (svc_target_add_related _ _ _ _ (Harrival j) HR).
  Qed.

  Lemma job_meets_deadline_correspondence (j : Job) :
    SvcBoolRel
      (@prosa.behavior.service.job_meets_deadline Job PStateR
        schedR costR deadlineR j)
      (ImportedWorkConserving.Prosa_Behavior_Service_job_meets_deadline Job
        (svc_decidable_eq Job) PStateL schedL costL deadlineL j).
  Proof.
    unfold prosa.behavior.service.job_meets_deadline.
    cbn [ImportedWorkConserving.Prosa_Behavior_Service_job_meets_deadline].
    exact (completed_by_correspondence j _ _ (Hdeadline j)).
  Qed.

  Lemma pending_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.pending Job PStateR
        schedR costR arrivalR j tR)
      (ImportedWorkConserving.Prosa_Behavior_Service_pending Job
        (svc_decidable_eq Job) PStateL schedL costL arrivalL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.pending.
    cbn [ImportedWorkConserving.Prosa_Behavior_Service_pending].
    apply svc_bool_and_related.
    - exact (svc_has_arrived_related Job arrivalR arrivalL j
        Harrival tR tL Ht).
    - exact (svc_bool_not_related _ _
        (completed_by_correspondence j tR tL Ht)).
  Qed.

  Lemma pending_earlier_and_at_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.pending_earlier_and_at Job PStateR
        schedR costR arrivalR j tR)
      (ImportedWorkConserving.Prosa_Behavior_Service_pending_earlier_and_at Job
        (svc_decidable_eq Job) PStateL schedL costL arrivalL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.pending_earlier_and_at.
    cbn [ImportedWorkConserving.Prosa_Behavior_Service_pending_earlier_and_at].
    apply svc_bool_and_related.
    - exact (svc_arrived_before_related Job arrivalR arrivalL j
        Harrival tR tL Ht).
    - exact (svc_bool_not_related _ _
        (completed_by_correspondence j tR tL Ht)).
  Qed.

  Lemma remaining_cost_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.remaining_cost Job PStateR
        schedR costR j tR)
      (ImportedWorkConserving.Prosa_Behavior_Service_remaining_cost Job
        (svc_decidable_eq Job) PStateL schedL costL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.remaining_cost.
    cbn [ImportedWorkConserving.Prosa_Behavior_Service_remaining_cost].
    exact (svc_target_sub_related _ _ _ _ (Hcost j)
      (service_correspondence j tR tL Ht)).
  Qed.

End ReadyServiceCorrespondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN service_correspondence". exact I. Qed.
Print Assumptions scheduled_at_correspondence.
Print Assumptions service_at_correspondence.
Print Assumptions receives_service_at_correspondence.
Print Assumptions service_during_correspondence.
Print Assumptions service_correspondence.
Print Assumptions completed_by_correspondence.
Print Assumptions completes_at_correspondence.
Print Assumptions job_response_time_bound_correspondence.
Print Assumptions job_meets_deadline_correspondence.
Print Assumptions pending_correspondence.
Print Assumptions pending_earlier_and_at_correspondence.
Print Assumptions remaining_cost_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END service_correspondence". exact I. Qed.
