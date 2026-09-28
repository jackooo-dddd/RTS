From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsReadinessSequentialSemanticSource.
From prosa Require Import model.readiness.sequential analysis.definitions.work_bearing_readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsModelSequential ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations SequentialityCorrespondence
  ReadinessCorrespondence.

Module I := ImportedFactsModelSequential.
Module S := FactsReadinessSequentialSemanticSource.FactsReadinessSequentialSemanticSource.

(** Helper copy (definition relations only) of the accepted statement correspondences for
    [analysis/facts/readiness/sequential.v].

    Source side: the extracted statements [S.statement_X] (with the
    source-local readiness instance [S.sequential_readiness_instance], a
    byte-identical helper block) specialised at their leading inputs; target
    side: the imported Lean theorem types and the Lean definition of the
    local instance.  The two sequential readiness models are related by the
    accepted [RdJobReadyRel] ([pending] and [prior_jobs_complete], the latter
    by the accepted [SequentialityCorrespondence]).  Inputs: [job_task] by
    [Lean.eq], [job_arrival] by [ArJobArrivalRel], [job_cost] by
    [SvcJobCostRel], processor states by the accepted two-sided
    [SvcProcessorStateRel], arrival sequences by [ArArrivalSequenceRel];
    schedules and FP policies quantified inside the statements are covered in
    both directions.  [sequential_readiness], [nonclairvoyant_readiness] and
    [sequential_tasks] are closed by the accepted readiness and sequentiality
    certificates.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma frs_exists_identity (T : Type) (P : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (P x) (PL x)) ->
  PropSPropRel (exists x, P x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Section Sequential.
  Context (Job Task : eqType).
  Let dJ := ar_decidable_eq Job.
  Let dT := ar_decidable_eq Task.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
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

  Lemma frs_scheduled_at_related schedR schedL (Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL)
      (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.scheduled_at.
    cbn [I.Prosa_Behavior_Service_scheduled_at].
    exact (svc_scheduled_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma frs_pending_related schedR schedL (Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL)
      (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.pending Job PStateR schedR costR jaR j tR)
      (I.Prosa_Behavior_Service_pending Job dJ PStateL schedL costL jaL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.pending.
    cbn [I.Prosa_Behavior_Service_pending].
    apply ar_bool_and_related.
    - exact (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht).
    - apply svc_bool_not_related.
      unfold prosa.behavior.service.completed_by.
      cbn [I.Prosa_Behavior_Service_completed_by].
      exact (svc_decide_le_related _ _ _ _ (Hcost j)
        (rd_service_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht)).
  Qed.

  Lemma frs_sequential_instance_related :
    RdJobReadyRel Job jaR jaL costR costL PStateR PStateL R
      (@S.sequential_readiness_instance Job Task jtR jaR costR PStateR arrR)
      (I.Prosa_Analysis_Facts_Readiness_Sequential_sequential_readiness_instance
        Job dJ Task dT jtL jaL costL PStateL arrL).
  Proof.
    intros schedR schedL Hsched j tR tL Ht. cbn.
    apply ar_bool_and_related.
    - exact (frs_pending_related schedR schedL Hsched j tR tL Ht).
    - exact (prior_jobs_complete_correspondence Job Task jtR jtL Hjt jaR jaL Hja costR costL Hcost
        PStateR PStateL R arrR arrL Harr schedR schedL Hsched j tR tL Ht).
  Qed.

  Lemma frs_forall_schedule
      (PR : @prosa.behavior.schedule.schedule Job PStateR -> Prop)
      (PL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL -> SProp) :
    (forall schedR schedL, RdScheduleFunRel Job PStateR PStateL R schedR schedL ->
      PropSPropRel (PR schedR) (PL schedL)) ->
    PropSPropRel (forall schedR, PR schedR) (forall schedL, PL schedL).
  Proof.
    exact (rd_forall_cover_sprop _ _ (RdScheduleFunRel Job PStateR PStateL R)
      (rd_schedule_to_target Job PStateR PStateL R) (rd_schedule_to_source Job PStateR PStateL R)
      (rd_schedule_to_target_rel Job PStateR PStateL R) (rd_schedule_to_source_rel Job PStateR PStateL R) PR PL).
  Qed.

End Sequential.
