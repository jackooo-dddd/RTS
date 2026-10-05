From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsSporadicArrivalTimesSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsSporadicArrivalTimes ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence.

Module I := ImportedFactsSporadicArrivalTimes.
Module S := FactsSporadicArrivalTimesSemanticSource.FactsSporadicArrivalTimesSemanticSource.

(** Correspondences for [analysis/facts/sporadic/arrival_times.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading class/data inputs; target side: the imported Lean theorem
    types.  Inputs: the sporadic model by its observable field ([SubNatRel]),
    [job_task] by [Lean.eq], [job_arrival] by [ArJobArrivalRel], arrival
    sequences by [ArArrivalSequenceRel].  Tasks and jobs are identity
    carriers.  The sporadic-model propositions and logical connectives are
    replayed from the accepted sporadic arrival-bound certificate, and
    [job_index] is the accepted Arrivals correspondence.  No source or target
    theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Logical connectives (replayed from the accepted certificates) *)

Lemma fsat_eq_correspondence (T : Type) (xR xL yR yL : T) :
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

Lemma fsat_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma fsat_neq_correspondence (T : Type) (x y : T) :
  PropSPropRel (x <> y) (I.Ne T x y).
Proof.
  unfold I.Ne, I.Not.
  apply ar_imp_correspondence.
  - exact (fsat_eq_correspondence T x x y y (@Lean.eq_refl _ _) (@Lean.eq_refl _ _)).
  - exact fsat_false_correspondence.
Qed.

Lemma fsat_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [HPQ HQP]. exact (I.Iff_intro PL QL
      (fun p => prop_to_sprop _ _ HQ (HPQ (sprop_to_prop _ _ HP p)))
      (fun q => prop_to_sprop _ _ HP (HQP (sprop_to_prop _ _ HQ q)))).
  - intro H. apply strictly_inhabits. split.
    + intro p. apply (sprop_to_prop _ _ HQ).
      exact (I.Iff_mp PL QL H (prop_to_sprop _ _ HP p)).
    + intro q. apply (sprop_to_prop _ _ HP).
      exact (I.Iff_mpr PL QL H (prop_to_sprop _ _ HQ q)).
Qed.

Section ArrivalTimes.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.

  Variable modelR : prosa.model.task.arrival.sporadic.SporadicModel Task.
  Variable modelL : I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task dT.
  Hypothesis Hmodel : forall tsk : Task,
    SubNatRel (@prosa.model.task.arrival.sporadic.task_min_inter_arrival_time Task modelR tsk)
      (I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time
        Task dT modelL tsk).
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

  Let VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.
  Let IDX := job_index_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja.

  Lemma fsat_valid_min_inter_arrival_related (tsk : Task) :
    PropSPropRel
      (is_true (@prosa.model.task.arrival.sporadic.valid_task_min_inter_arrival_time
        Task modelR tsk))
      (Lean.eq (I.Prosa_Model_Task_Arrival_Sporadic_valid_task_min_inter_arrival_time
        Task dT modelL tsk) I.Bool_true).
  Proof.
    apply ar_bool_truth_correspondence. cbn.
    exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical 0) (Hmodel tsk)).
  Qed.

  Lemma fsat_respects_sporadic_related (tsk : Task) :
    PropSPropRel
      (@prosa.model.task.arrival.sporadic.respects_sporadic_task_model
        Task modelR Job jtR jaR arrR tsk)
      (I.Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model
        Task dT modelL Job dJ jtL jaL arrL tsk).
  Proof.
    cbn [prosa.model.task.arrival.sporadic.respects_sporadic_task_model
      I.Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence; [exact (fsat_neq_correspondence Job j j')|].
    apply ar_imp_correspondence;
      [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (arrives_in_correspondence_certificate Job arrR arrL j' Harr)|].
    apply ar_imp_correspondence;
      [exact (fsat_eq_correspondence _ _ _ _ _ (Hjt j) (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence;
      [exact (fsat_eq_correspondence _ _ _ _ _ (Hjt j') (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j'))|].
    exact (sub_nat_le_correspondence _ _ _ _
      (sub_add_correspondence _ _ _ _ (Hja j) (Hmodel tsk)) (Hja j')).
  Qed.


  Definition src_lower_index_implies_earlier_arrival : Prop :=
    ltac:(body_of (fun s : S.statement_lower_index_implies_earlier_arrival => s Task modelR Job jtR jaR arrR)).
  Definition tgt_lower_index_implies_earlier_arrival : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Sporadic_ArrivalTimes_lower_index_implies_earlier_arrival Task dT modelL Job dJ jtL jaL arrL)).
  Theorem lower_index_implies_earlier_arrival_correspondence : PropSPropRel src_lower_index_implies_earlier_arrival tgt_lower_index_implies_earlier_arrival.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fsat_respects_sporadic_related tsk)|].
    apply ar_imp_correspondence; [exact (fsat_valid_min_inter_arrival_related tsk)|].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j1 Harr)|].
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j2 Harr)|].
    apply ar_imp_correspondence; [exact (fsat_eq_correspondence _ _ _ _ _ (Hjt j1) (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence; [exact (fsat_eq_correspondence _ _ _ _ _ (Hjt j2) (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (IDX j1) (IDX j2))|].
    exact (sub_nat_lt_correspondence _ _ _ _ (Hja j1) (Hja j2)).
  Qed.

  Definition src_same_jobs_iff_same_arr : Prop :=
    ltac:(body_of (fun s : S.statement_same_jobs_iff_same_arr => s Task modelR Job jtR jaR arrR)).
  Definition tgt_same_jobs_iff_same_arr : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Sporadic_ArrivalTimes_same_jobs_iff_same_arr Task dT modelL Job dJ jtL jaL arrL)).
  Theorem same_jobs_iff_same_arr_correspondence : PropSPropRel src_same_jobs_iff_same_arr tgt_same_jobs_iff_same_arr.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fsat_respects_sporadic_related tsk)|].
    apply ar_imp_correspondence; [exact (fsat_valid_min_inter_arrival_related tsk)|].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j1 Harr)|].
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j2 Harr)|].
    apply ar_imp_correspondence; [exact (fsat_eq_correspondence _ _ _ _ _ (Hjt j1) (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence; [exact (fsat_eq_correspondence _ _ _ _ _ (Hjt j2) (@Lean.eq_refl _ _))|].
    exact (fsat_iff_correspondence _ _ _ _
      (fsat_eq_correspondence _ _ _ _ _ (@Lean.eq_refl _ j1) (@Lean.eq_refl _ j2))
      (sub_nat_eq_correspondence _ _ _ _ (Hja j1) (Hja j2))).
  Qed.

  Definition src_uneq_job_uneq_arr : Prop :=
    ltac:(body_of (fun s : S.statement_uneq_job_uneq_arr => s Task modelR Job jtR jaR arrR)).
  Definition tgt_uneq_job_uneq_arr : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Sporadic_ArrivalTimes_uneq_job_uneq_arr Task dT modelL Job dJ jtL jaL arrL)).
  Theorem uneq_job_uneq_arr_correspondence : PropSPropRel src_uneq_job_uneq_arr tgt_uneq_job_uneq_arr.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fsat_respects_sporadic_related tsk)|].
    apply ar_imp_correspondence; [exact (fsat_valid_min_inter_arrival_related tsk)|].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j1 Harr)|].
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j2 Harr)|].
    apply ar_imp_correspondence; [exact (fsat_eq_correspondence _ _ _ _ _ (Hjt j1) (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence; [exact (fsat_eq_correspondence _ _ _ _ _ (Hjt j2) (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence; [exact (fsat_neq_correspondence Job j1 j2)|].
    unfold I.Ne, I.Not.
    apply ar_imp_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
    exact fsat_false_correspondence.
  Qed.
End ArrivalTimes.
