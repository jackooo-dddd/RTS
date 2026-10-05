From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsPrioritySequentialSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.priority.classes
  analysis.definitions.always_higher_priority analysis.definitions.work_bearing_readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPrioritySequential ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers.

Module I := ImportedFactsPrioritySequential.
Module S := FactsPrioritySequentialSemanticSource.FactsPrioritySequentialSemanticSource.

(** Statement correspondence for [analysis/facts/priority/sequential.v].

    Source side: the extracted statement specialised at its leading inputs
    (job type, arrival and cost classes, arrival sequence); target side: the
    imported Lean theorem type.  Inputs: [job_arrival] by [ArJobArrivalRel],
    [job_cost] by the accepted [SvcJobCostRel], arrival sequences by
    [ArArrivalSequenceRel].  Inputs quantified inside the statement are
    covered in both directions by the accepted preemption-facts conversions:
    the JLFP policy (pointwise on Booleans), the processor model (the accepted
    [isj_cover_pstate]), the schedule (through the processor-model relation),
    the readiness instance (related on the statement's schedule pair, as in
    the accepted preemption-facts certificate: it is used only at that
    schedule), the [JobPreemptable] instance, jobs (identity) and instants.
    Validity of the schedule and of the preemption model and the
    JLFP-at-preemption-point policy are related by the accepted
    preemption-facts helpers; priority transitivity, work-bearing readiness
    and always-higher priority (through the canonical JLFP-to-JLDP coercion
    on both sides) by unfolding.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fps_exists_identity (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (H x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (H x) Hx).
Qed.

Section FactsPrioritySequential.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma fps_transitive_rel pR pL (Hp : FpreJLFPRel Job pR pL) :
    PropSPropRel (@prosa.model.priority.definitions.transitive_job_priorities Job pR)
      (I.Prosa_Model_Priority_Definitions_transitive_job_priorities Job dJ pL).
  Proof.
    unfold prosa.model.priority.definitions.transitive_job_priorities.
    cbn [I.Prosa_Model_Priority_Definitions_transitive_job_priorities].
    apply ar_forall_identity_correspondence. intro y.
    apply ar_forall_identity_correspondence. intro x.
    apply ar_forall_identity_correspondence. intro z.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp x y))|].
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp y z))|].
    exact (ar_bool_truth_correspondence _ _ (Hp x z)).
  Qed.

  Definition src_early_hep_job_is_scheduled : Prop :=
    ltac:(body_of (fun s : S.statement_early_hep_job_is_scheduled => s Job jaR costR arrR)).
  Definition tgt_early_hep_job_is_scheduled : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Sequential_early_hep_job_is_scheduled
      Job dJ jaL costL arrL)).

  Theorem early_hep_job_is_scheduled_correspondence :
    PropSPropRel src_early_hep_job_is_scheduled tgt_early_hep_job_is_scheduled.
  Proof.
    unfold src_early_hep_job_is_scheduled, tgt_early_hep_job_is_scheduled.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply fpre_forall_jlfp. intros pR pL Hp.
    apply ar_imp_correspondence; [exact (fps_transitive_rel pR pL Hp)|].
    apply (isj_cover_pstate Job). intros PR PL X.
    apply ar_imp_correspondence; [exact (isj_psr_uniprocessor_related Job PR PL X)|].
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs). intros jrR jrL Hjr.
    apply ar_imp_correspondence.
    { unfold prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness.
      cbn [I.Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs j tR tL Ht))|].
      apply fps_exists_identity. intro jhp.
      apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL jhp Harr)|].
      apply ar_and_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hjr jhp tR tL Ht))|].
      exact (ar_bool_truth_correspondence _ _ (Hp jhp j)). }
    apply ar_imp_correspondence;
      [exact (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr
        jrR jrL Hjr)|].
    apply fpre_forall_jp. intros jpR jpL Hjp.
    apply ar_imp_correspondence;
      [exact (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs
        arrR arrL Harr jpR jpL Hjp)|].
    apply ar_imp_correspondence;
      [exact (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr
        jrR jrL Hjr jpR jpL Hjp pR pL Hp)|].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j1 Harr)|].
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
    apply ar_imp_correspondence.
    { unfold prosa.analysis.definitions.always_higher_priority.always_higher_priority.
      cbn [I.Prosa_Analysis_Definitions_AlwaysHigherPriority_always_higher_priority].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      exact (ar_bool_truth_correspondence _ _
        (ar_bool_and_related _ _ _ _ (Hp j1 j2) (svc_bool_not_related _ _ (Hp j2 j1)))). }
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (fpre_scheduled_at_related Job PR PL X sR sL Hs j2 tR tL Ht))|].
    exact (ar_bool_truth_correspondence _ _
      (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs j1 tR tL Ht)).
  Qed.
End FactsPrioritySequential.
