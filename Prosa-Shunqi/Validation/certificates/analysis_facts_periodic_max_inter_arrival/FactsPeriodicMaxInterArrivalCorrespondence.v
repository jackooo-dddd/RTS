From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsPeriodicMaxInterArrivalSemanticSource.
From prosa Require Import model.task.arrival.task_max_inter_arrival.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPeriodicMaxInterArrival ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  PeriodicCorrespondence TmiaCorrespondence.

Module I := ImportedFactsPeriodicMaxInterArrival.
Module S := FactsPeriodicMaxInterArrivalSemanticSource.FactsPeriodicMaxInterArrivalSemanticSource.
Module P := PeriodicSemanticSource.PeriodicSemanticSource.

(** Correspondences for [analysis/facts/periodic/max_inter_arrival.v].

    Source side: the extracted instance block and the extracted statements
    [S.statement_X] specialised at their leading inputs (task and job types,
    the periodic model, [job_task], [job_arrival], the arrival sequence and
    the task); target side: the compiled Lean instance and the imported Lean
    theorem types at related inputs (the accepted [PerRel], [Lean.eq] on
    [job_task], [ArJobArrivalRel], [ArArrivalSequenceRel]).  The instance is
    related by the accepted [TmClassRel] (its field is the period on both
    sides); [valid_period], the periodic task model and the
    maximum-inter-arrival predicates are closed by the accepted periodic and
    task-max-inter-arrival certificates re-instantiated at this artifact.  No
    source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section MaxInterArrival.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable pR : P.PeriodicModel Task.
  Variable pL : I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task dT.
  Hypothesis Hp : PerRel Task pR pL.

  Let cR := @S.max_inter_eq_period Task pR.
  Let cL := I.Prosa_Analysis_Facts_Periodic_MaxInterArrival_max_inter_eq_period Task dT pL.

  Theorem max_inter_eq_period_correspondence : TmClassRel Task cR cL.
  Proof. intro tsk. exact (Hp tsk). Qed.

  Definition src_valid_period_is_valid_max_inter_arrival_time : Prop :=
    ltac:(body_of (fun s : S.statement_valid_period_is_valid_max_inter_arrival_time => s Task pR)).
  Definition tgt_valid_period_is_valid_max_inter_arrival_time : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Periodic_MaxInterArrival_valid_period_is_valid_max_inter_arrival_time
        Task dT pL)).
  Theorem valid_period_is_valid_max_inter_arrival_time_correspondence :
    PropSPropRel src_valid_period_is_valid_max_inter_arrival_time
      tgt_valid_period_is_valid_max_inter_arrival_time.
  Proof.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (valid_period_correspondence Task pR pL Hp tsk))|].
    exact (ar_bool_truth_correspondence _ _
      (positive_task_max_inter_arrival_time_correspondence Task cR cL max_inter_eq_period_correspondence tsk)).
  Qed.

  Section Model.
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
    Variable tsk : Task.

    Definition src_periodic_model_respects_max_inter_arrival_model : Prop :=
      ltac:(body_of (fun s : S.statement_periodic_model_respects_max_inter_arrival_model =>
        s Task pR Job jtR jaR arrR tsk)).
    Definition tgt_periodic_model_respects_max_inter_arrival_model : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_Periodic_MaxInterArrival_periodic_model_respects_max_inter_arrival_model
          Task dT pL Job dJ jtL jaL arrL tsk)).
    Theorem periodic_model_respects_max_inter_arrival_model_correspondence :
      PropSPropRel src_periodic_model_respects_max_inter_arrival_model
        tgt_periodic_model_respects_max_inter_arrival_model.
    Proof.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (valid_period_correspondence Task pR pL Hp tsk))|].
      apply ar_imp_correspondence;
        [exact (respects_periodic_task_model_correspondence Task pR pL Hp Job jtR jtL Hjt jaR jaL Hja
          arrR arrL Harr tsk)|].
      exact (valid_task_max_inter_arrival_time_correspondence Task cR cL max_inter_eq_period_correspondence
        Job jtR jtL Hjt jaR jaL Hja arrR arrL Harr tsk).
    Qed.
  End Model.
End MaxInterArrival.
