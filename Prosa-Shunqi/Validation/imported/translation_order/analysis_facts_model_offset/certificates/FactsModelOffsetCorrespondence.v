From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsModelOffsetSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsModelOffset ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskOffsetCorrespondence.

Module I := ImportedFactsModelOffset.
Module S := FactsModelOffsetSemanticSource.FactsModelOffsetSemanticSource.

(** Statement correspondences for [analysis/facts/model/offset.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types at
    related inputs ([OffRel], [Lean.eq] for [job_task], [ArJobArrivalRel],
    [ArArrivalSequenceRel]).  Jobs and tasks are identity carriers.  Valid
    offsets, task offsets and their maximum are closed by the accepted
    [TaskOffsetCorrespondence], [job_index] by the accepted
    [ArrivalsCorrespondence], [valid_arrival_sequence] by the accepted
    arrival-sequence certificate.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fmo_eq_correspondence (T : Type) (xR xL yR yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL ->
  PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hx) Hy).
  - intro Heq. apply strictly_inhabits.
    exact (imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hx
        (sub_imported_eq_trans _ _ _ Heq (sub_imported_eq_sym _ _ Hy)))).
Qed.

Section Offset.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable oR : TaskOffsetSemanticSource.TaskOffsetSemanticSource.TaskOffset Task.
  Variable oL : I.Prosa_Model_Task_Offset_TaskOffset Task dT.
  Hypothesis Hoff : OffRel Task oR oL.

  Section Max.
    Variable tsk : Task.
    Variable tsR : seq Task.
    Variable tsL : I.List Task.
    Hypothesis Hts : ArListRel tsR tsL.

    Definition src_max_offset_g : Prop :=
      ltac:(body_of (fun s : S.statement_max_offset_g => s Task oR tsk tsR)).
    Definition tgt_max_offset_g : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Offset_max_offset_g Task dT oL tsk tsL)).
    Theorem max_offset_g_correspondence : PropSPropRel src_max_offset_g tgt_max_offset_g.
    Proof.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
      exact (sub_nat_le_correspondence _ _ _ _ (Hoff tsk)
        (max_task_offset_correspondence Task oR oL Hoff tsR tsL Hts)).
    Qed.
  End Max.

  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Definition src_first_job_arrival : Prop :=
    ltac:(body_of (fun s : S.statement_first_job_arrival => s Task oR Job jtR jaR arrR)).
  Definition tgt_first_job_arrival : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Offset_first_job_arrival
      Task dT oL Job dJ jtL jaL arrL)).
  Theorem first_job_arrival_correspondence : PropSPropRel src_first_job_arrival tgt_first_job_arrival.
  Proof.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence;
      [exact (fmo_eq_correspondence Task _ _ tsk tsk (Hjt j) (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence;
      [exact (valid_offset_correspondence Task oR oL Hoff Job jtR jtL Hjt jaR jaL Hja arrR arrL Harr tsk)|].
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (sub_nat_eq_correspondence _ _ _ _
        (job_index_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j)
        (sub_nat_rel_canonical O))|].
    exact (sub_nat_eq_correspondence _ _ _ _ (Hja j) (Hoff tsk)).
  Qed.
End Offset.
