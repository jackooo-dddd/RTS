From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import behavior.ready.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReady ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ReadyBaseAdapter
  ReadyNatBoolOperations ReadyScheduleOperations ReadyJobOperations
  ReadyServiceCorrespondence ReadyArrivalBaseAdapter ReadyArrivalOperations
  ReadyArrivalCorrespondence.

(** Observable correspondence for the v0.6 readiness class.  The operation
    field is related extensionally.  The law field is validated by relating
    its two function types compositionally; neither class-law inhabitant is
    used to manufacture the correspondence proof. *)

Section ReadyCorrespondence.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
      (svc_decidable_eq Job).
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedReady.Prosa_Behavior_Schedule_schedule Job
    (svc_decidable_eq Job) PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedReady.Prosa_Behavior_Job_JobCost Job
    (svc_decidable_eq Job).
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : ImportedReady.Prosa_Behavior_Job_JobArrival Job
    (svc_decidable_eq Job).
  Hypothesis Harrival : SvcJobArrivalRel Job arrivalR arrivalL.

  Variable readyR :
    @prosa.behavior.ready.JobReady Job PStateR costR arrivalR.
  Variable readyL : ImportedReady.Prosa_Behavior_Ready_JobReady Job
    (svc_decidable_eq Job) PStateL costL arrivalL.

  Definition RdyJobReadyRel : SProp :=
    forall schedR' schedL',
      SvcScheduleRel Job PStateR PStateL R schedR' schedL' ->
    forall (j : Job) (tR : nat) (tL : Lean.Nat),
      SubNatRel tR tL ->
      SvcBoolRel
        (@prosa.behavior.ready.job_ready Job PStateR costR arrivalR
          readyR schedR' j tR)
        (ImportedReady.Prosa_Behavior_Ready_JobReady_job_ready Job
          (svc_decidable_eq Job) PStateL costL arrivalL readyL
          schedL' j tL).

  Record RdyJobReadyClassRel : Type := {
    rdy_job_ready_operation_related : RdyJobReadyRel;
    rdy_job_ready_law_type_related :
      forall schedR' schedL',
        SvcScheduleRel Job PStateR PStateL R schedR' schedL' ->
      forall (j : Job) (tR : nat) (tL : Lean.Nat),
        SubNatRel tR tL ->
        PropSPropRel
          (is_true
              (@prosa.behavior.ready.job_ready Job PStateR costR arrivalR
                readyR schedR' j tR) ->
            is_true
              (@prosa.behavior.service.pending Job PStateR schedR'
                costR arrivalR j tR))
          (Lean.eq
              (ImportedReady.Prosa_Behavior_Ready_JobReady_job_ready Job
                (svc_decidable_eq Job) PStateL costL arrivalL readyL
                schedL' j tL)
              ImportedReady.Bool_true ->
            Lean.eq
              (ImportedReady.Prosa_Behavior_Service_pending Job
                (svc_decidable_eq Job) PStateL schedL' costL arrivalL j tL)
              ImportedReady.Bool_true)
  }.

  Lemma job_ready_class_correspondence
      (Hready : RdyJobReadyRel) : RdyJobReadyClassRel.
  Proof.
    constructor; first exact Hready.
    intros schedR' schedL' Hsched' j tR tL Ht.
    apply ar_imp_correspondence.
    - apply svc_bool_truth_correspondence.
      exact (Hready schedR' schedL' Hsched' j tR tL Ht).
    - apply svc_bool_truth_correspondence.
      exact (pending_correspondence Job PStateR PStateL R
        schedR' schedL' Hsched' costR costL Hcost
        arrivalR arrivalL Harrival j tR tL Ht).
  Qed.

  Hypothesis Hready : RdyJobReadyRel.

  Lemma backlogged_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel
      (@prosa.behavior.ready.backlogged Job PStateR costR arrivalR
        readyR schedR j tR)
      (ImportedReady.Prosa_Behavior_Ready_backlogged Job
        (svc_decidable_eq Job) PStateL costL arrivalL readyL
        schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.ready.backlogged.
    cbn [ImportedReady.Prosa_Behavior_Ready_backlogged].
    apply svc_bool_and_related.
    - exact (Hready schedR schedL Hsched j tR tL Ht).
    - apply svc_bool_not_related.
      exact (scheduled_at_correspondence Job PStateR PStateL R
        schedR schedL Hsched j tR tL Ht).
  Qed.

  Lemma jobs_come_from_arrival_sequence_correspondence
      (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job)
      (arrL :
        ImportedReady.Prosa_Behavior_Arrival_sequence_arrival_sequence Job
          (ar_decidable_eq Job))
      (Harr : ArArrivalSequenceRel Job arrR arrL) :
    PropSPropRel
      (@prosa.behavior.ready.jobs_come_from_arrival_sequence
        Job PStateR schedR arrR)
      (ImportedReady.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence
        Job (svc_decidable_eq Job) PStateL schedL arrL).
  Proof.
    cbn [ImportedReady.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence.
    - apply svc_bool_truth_correspondence.
      exact (scheduled_at_correspondence Job PStateR PStateL R
        schedR schedL Hsched j tR tL Ht).
    - exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
  Qed.

  Lemma jobs_must_arrive_to_execute_correspondence :
    PropSPropRel
      (@prosa.behavior.ready.jobs_must_arrive_to_execute
        Job arrivalR PStateR schedR)
      (ImportedReady.Prosa_Behavior_Ready_jobs_must_arrive_to_execute
        Job (svc_decidable_eq Job) arrivalL PStateL schedL).
  Proof.
    cbn [ImportedReady.Prosa_Behavior_Ready_jobs_must_arrive_to_execute].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence.
    - apply svc_bool_truth_correspondence.
      exact (scheduled_at_correspondence Job PStateR PStateL R
        schedR schedL Hsched j tR tL Ht).
    - apply svc_bool_truth_correspondence.
      exact (svc_has_arrived_related Job arrivalR arrivalL j
        Harrival tR tL Ht).
  Qed.

  Lemma jobs_must_be_ready_to_execute_correspondence :
    PropSPropRel
      (@prosa.behavior.ready.jobs_must_be_ready_to_execute
        Job arrivalR PStateR schedR costR readyR)
      (ImportedReady.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute
        Job (svc_decidable_eq Job) arrivalL PStateL schedL costL readyL).
  Proof.
    cbn [ImportedReady.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence.
    - apply svc_bool_truth_correspondence.
      exact (scheduled_at_correspondence Job PStateR PStateL R
        schedR schedL Hsched j tR tL Ht).
    - apply svc_bool_truth_correspondence.
      exact (Hready schedR schedL Hsched j tR tL Ht).
  Qed.

  Lemma completed_jobs_dont_execute_correspondence :
    PropSPropRel
      (@prosa.behavior.ready.completed_jobs_dont_execute
        Job PStateR schedR costR)
      (ImportedReady.Prosa_Behavior_Ready_completed_jobs_dont_execute
        Job (svc_decidable_eq Job) PStateL schedL costL).
  Proof.
    cbn [ImportedReady.Prosa_Behavior_Ready_completed_jobs_dont_execute].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence.
    - apply svc_bool_truth_correspondence.
      exact (scheduled_at_correspondence Job PStateR PStateL R
        schedR schedL Hsched j tR tL Ht).
    - apply svc_target_lt_related.
      + exact (service_correspondence Job PStateR PStateL R
          schedR schedL Hsched j tR tL Ht).
      + exact (Hcost j).
  Qed.

  Lemma valid_schedule_correspondence
      (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job)
      (arrL :
        ImportedReady.Prosa_Behavior_Arrival_sequence_arrival_sequence Job
          (ar_decidable_eq Job))
      (Harr : ArArrivalSequenceRel Job arrR arrL) :
    PropSPropRel
      (@prosa.behavior.ready.valid_schedule Job arrivalR PStateR
        schedR costR readyR arrR)
      (ImportedReady.Prosa_Behavior_Ready_valid_schedule Job
        (svc_decidable_eq Job) arrivalL PStateL schedL costL readyL arrL).
  Proof.
    cbn [ImportedReady.Prosa_Behavior_Ready_valid_schedule].
    apply ar_and_correspondence.
    - exact (jobs_come_from_arrival_sequence_correspondence arrR arrL Harr).
    - exact jobs_must_be_ready_to_execute_correspondence.
  Qed.

End ReadyCorrespondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN ready_correspondence". exact I. Qed.
Print Assumptions job_ready_class_correspondence.
Print Assumptions backlogged_correspondence.
Print Assumptions jobs_come_from_arrival_sequence_correspondence.
Print Assumptions jobs_must_arrive_to_execute_correspondence.
Print Assumptions jobs_must_be_ready_to_execute_correspondence.
Print Assumptions completed_jobs_dont_execute_correspondence.
Print Assumptions valid_schedule_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END ready_correspondence". exact I. Qed.
