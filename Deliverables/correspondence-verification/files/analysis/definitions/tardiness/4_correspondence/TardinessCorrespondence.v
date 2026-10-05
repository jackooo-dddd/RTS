From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import TardinessSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTardiness ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedTardiness.
Module S := TardinessSemanticSource.TardinessSemanticSource.
Module SS := SchedulabilitySemanticSource.SchedulabilitySemanticSource.

(** Definition certificate for [analysis/definitions/tardiness.v].

    Source side: the extracted byte-identical definition block (its
    schedulability import bound to the accepted extracted schedulability
    source); target side: the compiled Lean definition.  Inputs:
    [TaskDeadline] pointwise by [SubNatRel], [job_arrival] by
    [ArJobArrivalRel], [job_cost] by [SvcJobCostRel], [job_task] by
    [Lean.eq], processor states by the accepted two-sided
    [SvcProcessorStateRel], schedules by [SvcScheduleRel], arrival sequences
    by [ArArrivalSequenceRel].  The response-time bound of the accepted
    schedulability certificate is replayed (service, [completed_by],
    [job_of_task]); no source or target proof is used. *)

Lemma trd_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma trd_logic_eq_to_lean_eq {A : Type} (x y : A) :
  Logic.eq x y -> Lean.eq x y.
Proof. intros []. exact (@Lean.eq_refl _ _). Qed.

Lemma trd_decide_eq_related (T : eqType) (x y : T) :
  ArBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (ar_decidable_eq T x y)).
Proof.
  apply trd_logic_eq_to_lean_eq.
  unfold ar_decidable_eq. case: eqP => H; reflexivity.
Qed.

Section Tardiness.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable tdR : prosa.model.task.concept.TaskDeadline Task.
  Variable tdL : I.Prosa_Model_Task_Concept_TaskDeadline Task dT.
  Hypothesis Htd : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR tsk)
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL tsk).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma trd_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [I.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma trd_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service.
    cbn [I.Prosa_Behavior_Service_service].
    have Hsum := svc_interval_sum_related O tR Lean.Nat_zero tL
      (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
      (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j t)
      (sub_nat_rel_canonical O) Ht (fun xR xL Hx => trd_service_at_related j xR xL Hx).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR schedR j O tR)
      (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job dJ PStateL schedL j Lean.Nat_zero tL)) in Hsum.
    exact Hsum.
  Qed.

  Lemma trd_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR schedR costR j tR)
      (I.Prosa_Behavior_Service_completed_by Job dJ PStateL schedL costL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.completed_by.
    cbn [I.Prosa_Behavior_Service_completed_by].
    exact (svc_decide_le_related _ _ _ _ (Hcost j) (trd_service_related j tR tL Ht)).
  Qed.

  Lemma trd_job_of_task_related (tsk : Task) (j : Job) :
    ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof.
    unfold prosa.model.task.concept.job_of_task.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    refine (trd_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
        (I.Decidable_decide (Lean.eq v tsk) (dT v tsk))) _ _ (Hjt j) _).
    exact (trd_decide_eq_related Task _ tsk).
  Qed.

  Lemma trd_task_response_time_bound_related (tsk : Task) (rR : nat) (rL : Lean.Nat) :
    SubNatRel rR rL ->
    PropSPropRel (@SS.task_response_time_bound Task Job jaR costR jtR PStateR arrR schedR tsk rR)
      (I.Prosa_Analysis_Definitions_Schedulability_task_response_time_bound
        Task dT Job dJ jaL costL jtL PStateL arrL schedL tsk rL).
  Proof.
    intro Hr. unfold SS.task_response_time_bound.
    cbn [I.Prosa_Analysis_Definitions_Schedulability_task_response_time_bound].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (trd_job_of_task_related tsk j))|].
    apply svc_bool_truth_correspondence.
    unfold prosa.behavior.service.job_response_time_bound.
    cbn [I.Prosa_Behavior_Service_job_response_time_bound].
    exact (trd_completed_by_related j _ _ (svc_target_add_related _ _ _ _ (Hja j) Hr)).
  Qed.

  Theorem task_tardiness_is_bounded_correspondence (tsk : Task) (bR : nat) (bL : Lean.Nat) :
    SubNatRel bR bL ->
    PropSPropRel (@S.task_tardiness_is_bounded Task tdR Job jaR costR jtR PStateR arrR schedR tsk bR)
      (I.Prosa_Analysis_Definitions_Tardiness_task_tardiness_is_bounded
        Task dT tdL Job dJ jaL costL jtL PStateL arrL schedL tsk bL).
  Proof.
    intro Hb. unfold S.task_tardiness_is_bounded.
    cbn [I.Prosa_Analysis_Definitions_Tardiness_task_tardiness_is_bounded].
    exact (trd_task_response_time_bound_related tsk _ _ (svc_target_add_related _ _ _ _ (Htd tsk) Hb)).
  Qed.
End Tardiness.
