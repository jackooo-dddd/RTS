From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsPeriodicArrivalTimesSemanticSource.
From prosa Require Import model.task.arrivals.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPeriodicArrivalTimes ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskOffsetCorrespondence PeriodicCorrespondence.

Module I := ImportedFactsPeriodicArrivalTimes.
Module S := FactsPeriodicArrivalTimesSemanticSource.FactsPeriodicArrivalTimesSemanticSource.
Module O := TaskOffsetSemanticSource.TaskOffsetSemanticSource.
Module P := PeriodicSemanticSource.PeriodicSemanticSource.

(** Statement correspondences for [analysis/facts/periodic/arrival_times.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types, the task offsets, the periodic
    model, [job_task], [job_arrival] and the arrival sequence); target side:
    the imported Lean theorem types at related inputs (the accepted [OffRel]
    and [PerRel], [Lean.eq] on [job_task], [ArJobArrivalRel],
    [ArArrivalSequenceRel]).  Tasks and jobs are identity carriers, Nats are
    covered in both directions.  Arrival-sequence validity, [valid_offset],
    [valid_period], the periodic task model and [job_index] are closed by the
    accepted arrival-sequence, task-offset, periodic and arrivals
    certificates re-instantiated at this artifact.  No source or target
    theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section ArrivalTimes.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable oR : O.TaskOffset Task.
  Variable oL : I.Prosa_Model_Task_Offset_TaskOffset Task dT.
  Hypothesis Hoff : OffRel Task oR oL.
  Variable pR : P.PeriodicModel Task.
  Variable pL : I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task dT.
  Hypothesis Hp : PerRel Task pR pL.
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

  Let IDX (j : Job) := job_index_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j.
  Let VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.
  Let TASK j tsk := per_eq_correspondence Task _ _ tsk tsk (Hjt j) (@Lean.eq_refl _ _).
  Let ARRIVES j := arrives_in_correspondence_certificate Job arrR arrL j Harr.
  Let AT tsk j nR nL (Hn : SubNatRel nR nL) :=
    sub_nat_eq_correspondence _ _ _ _ (Hja j)
      (sub_add_correspondence _ _ _ _ (Hoff tsk) (sub_mul_correspondence _ _ _ _ Hn (Hp tsk))).

  Ltac fpat_prefix :=
    apply ar_imp_correspondence; [exact VALID|];
    apply ar_forall_identity_correspondence; let tsk := fresh "tsk" in intro tsk;
    apply ar_imp_correspondence;
      [exact (valid_offset_correspondence Task oR oL Hoff Job jtR jtL Hjt jaR jaL Hja arrR arrL Harr tsk)|];
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (valid_period_correspondence Task pR pL Hp tsk))|];
    apply ar_imp_correspondence;
      [exact (respects_periodic_task_model_correspondence Task pR pL Hp Job jtR jtL Hjt jaR jaL Hja
        arrR arrL Harr tsk)|].

  Definition src_periodic_arrival_times : Prop :=
    ltac:(body_of (fun s : S.statement_periodic_arrival_times => s Task oR pR Job jtR jaR arrR)).
  Definition tgt_periodic_arrival_times : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Periodic_ArrivalTimes_periodic_arrival_times
      Task dT oL pL Job dJ jtL jaL arrL)).
  Theorem periodic_arrival_times_correspondence :
    PropSPropRel src_periodic_arrival_times tgt_periodic_arrival_times.
  Proof.
    fpat_prefix.
    apply ar_forall_nat_correspondence. intros nR nL Hn.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (ARRIVES j)|].
    apply ar_imp_correspondence; [exact (TASK j tsk)|].
    apply ar_imp_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ (IDX j) Hn)|].
    exact (AT tsk j _ _ Hn).
  Qed.

  Definition src_job_arrival_times : Prop :=
    ltac:(body_of (fun s : S.statement_job_arrival_times => s Task oR pR Job jtR jaR arrR)).
  Definition tgt_job_arrival_times : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Periodic_ArrivalTimes_job_arrival_times
      Task dT oL pL Job dJ jtL jaL arrL)).
  Theorem job_arrival_times_correspondence :
    PropSPropRel src_job_arrival_times tgt_job_arrival_times.
  Proof.
    fpat_prefix.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (ARRIVES j)|].
    apply ar_imp_correspondence; [exact (TASK j tsk)|].
    apply ar_exists_nat_correspondence. intros nR nL Hn.
    exact (AT tsk j _ _ Hn).
  Qed.

  Definition src_job_arr_index : Prop :=
    ltac:(body_of (fun s : S.statement_job_arr_index => s Task oR pR Job jtR jaR arrR)).
  Definition tgt_job_arr_index : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Periodic_ArrivalTimes_job_arr_index
      Task dT oL pL Job dJ jtL jaL arrL)).
  Theorem job_arr_index_correspondence : PropSPropRel src_job_arr_index tgt_job_arr_index.
  Proof.
    fpat_prefix.
    apply ar_forall_nat_correspondence. intros nR nL Hn.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (ARRIVES j)|].
    apply ar_imp_correspondence; [exact (TASK j tsk)|].
    apply ar_imp_correspondence; [exact (AT tsk j _ _ Hn)|].
    exact (sub_nat_eq_correspondence _ _ _ _ (IDX j) Hn).
  Qed.
End ArrivalTimes.
