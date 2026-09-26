From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import PeriodicAsSporadicSemanticSource.
From prosa Require Import model.task.arrivals model.task.arrival.sporadic.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPeriodicAsSporadic ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  PeriodicCorrespondence.

Module I := ImportedPeriodicAsSporadic.
Module S := PeriodicAsSporadicSemanticSource.PeriodicAsSporadicSemanticSource.
Module P := PeriodicSemanticSource.PeriodicSemanticSource.

(** Correspondences for [model/task/arrival/periodic_as_sporadic.v].

    Source side: the extracted byte-identical instance block
    [S.periodic_as_sporadic] and the extracted statements [S.statement_X]
    specialised at their leading class/data inputs; target side: the imported
    Lean instance and theorem types.  Inputs: the periodic model by the
    accepted [PerRel], [job_task] by [Lean.eq], [job_arrival] by
    [ArJobArrivalRel], arrival sequences by [ArArrivalSequenceRel]; task sets
    are covered in both directions by [ArListRel].  The instance is related
    by its observable field; the periodic predicates are closed by the
    accepted [PeriodicCorrespondence]; the sporadic predicates replay the
    accepted sporadic-as-curve proofs at the instance.  No source or target
    theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma pas_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xR xL, ArListRel xR xL -> PropSPropRel (PR xR) (PL xL)) ->
  PropSPropRel (forall xR, PR xR) (forall xL, PL xL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR xL. exact (prop_to_sprop _ _ (H _ _ (ar_list_target_roundtrip xL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro xR.
    exact (sprop_to_prop _ _ (H xR (ar_list_to_imported xR) (@Lean.eq_refl _ _)) (HL _)).
Qed.

Lemma pas_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma pas_neq_correspondence (T : Type) (x y : T) :
  PropSPropRel (x <> y) (I.Ne T x y).
Proof.
  unfold I.Ne, I.Not.
  apply ar_imp_correspondence.
  - exact (per_eq_correspondence T x x y y (@Lean.eq_refl _ _) (@Lean.eq_refl _ _)).
  - exact pas_false_correspondence.
Qed.

Section PeriodicAsSporadic.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.

  Variable pR : P.PeriodicModel Task.
  Variable pL : I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task dT.
  Hypothesis Hp : PerRel Task pR pL.

  Let modelR := @S.periodic_as_sporadic Task pR.
  Let modelL := I.Prosa_Model_Task_Arrival_PeriodicAsSporadic_periodic_as_sporadic Task dT pL.

  (** The instance: related by its observable field. *)
  Theorem periodic_as_sporadic_correspondence (tsk : Task) :
    SubNatRel (@prosa.model.task.arrival.sporadic.task_min_inter_arrival_time Task modelR tsk)
      (I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time
        Task dT modelL tsk).
  Proof. exact (Hp tsk). Qed.

  Let Hmodel := periodic_as_sporadic_correspondence.

  Lemma pas_valid_min_inter_arrival_related (tsk : Task) :
    PropSPropRel
      (is_true (@prosa.model.task.arrival.sporadic.valid_task_min_inter_arrival_time
        Task modelR tsk))
      (Lean.eq (I.Prosa_Model_Task_Arrival_Sporadic_valid_task_min_inter_arrival_time
        Task dT modelL tsk) I.Bool_true).
  Proof.
    apply ar_bool_truth_correspondence. cbn.
    exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical 0) (Hmodel tsk)).
  Qed.

  Definition src_valid_period_is_valid_inter_arrival_time : Prop :=
    ltac:(body_of (fun s : S.statement_valid_period_is_valid_inter_arrival_time => s Task pR)).
  Definition tgt_valid_period_is_valid_inter_arrival_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_PeriodicAsSporadic_valid_period_is_valid_inter_arrival_time
      Task dT pL)).
  Theorem valid_period_is_valid_inter_arrival_time_correspondence :
    PropSPropRel src_valid_period_is_valid_inter_arrival_time
      tgt_valid_period_is_valid_inter_arrival_time.
  Proof.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (valid_period_correspondence Task pR pL Hp tsk))|].
    exact (pas_valid_min_inter_arrival_related tsk).
  Qed.

  Lemma pas_valid_taskset_related tsR tsL :
    ArListRel tsR tsL ->
    PropSPropRel
      (@prosa.model.task.arrival.sporadic.valid_taskset_inter_arrival_times Task modelR tsR)
      (I.Prosa_Model_Task_Arrival_Sporadic_valid_taskset_inter_arrival_times Task dT modelL tsL).
  Proof.
    intro Hts.
    cbn [prosa.model.task.arrival.sporadic.valid_taskset_inter_arrival_times
      I.Prosa_Model_Task_Arrival_Sporadic_valid_taskset_inter_arrival_times].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    exact (pas_valid_min_inter_arrival_related tsk).
  Qed.

  Definition src_valid_periods_are_valid_inter_arrival_times : Prop :=
    ltac:(body_of (fun s : S.statement_valid_periods_are_valid_inter_arrival_times => s Task pR)).
  Definition tgt_valid_periods_are_valid_inter_arrival_times : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_PeriodicAsSporadic_valid_periods_are_valid_inter_arrival_times
      Task dT pL)).
  Theorem valid_periods_are_valid_inter_arrival_times_correspondence :
    PropSPropRel src_valid_periods_are_valid_inter_arrival_times
      tgt_valid_periods_are_valid_inter_arrival_times.
  Proof.
    apply pas_forall_list. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (valid_periods_correspondence Task pR pL Hp tsR tsL Hts)|].
    exact (pas_valid_taskset_related tsR tsL Hts).
  Qed.

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

  Let VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.

  Lemma pas_respects_sporadic_related (tsk : Task) :
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
    apply ar_imp_correspondence; [exact (pas_neq_correspondence Job j j')|].
    apply ar_imp_correspondence;
      [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (arrives_in_correspondence_certificate Job arrR arrL j' Harr)|].
    apply ar_imp_correspondence;
      [exact (per_eq_correspondence _ _ _ _ _ (Hjt j) (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence;
      [exact (per_eq_correspondence _ _ _ _ _ (Hjt j') (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j'))|].
    exact (sub_nat_le_correspondence _ _ _ _
      (sub_add_correspondence _ _ _ _ (Hja j) (Hmodel tsk)) (Hja j')).
  Qed.

  Definition src_periodic_task_respects_sporadic_task_model : Prop :=
    ltac:(body_of (fun s : S.statement_periodic_task_respects_sporadic_task_model =>
      s Task pR Job jtR jaR arrR)).
  Definition tgt_periodic_task_respects_sporadic_task_model : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_PeriodicAsSporadic_periodic_task_respects_sporadic_task_model
      Task dT pL Job dJ jtL jaL arrL)).
  Theorem periodic_task_respects_sporadic_task_model_correspondence :
    PropSPropRel src_periodic_task_respects_sporadic_task_model
      tgt_periodic_task_respects_sporadic_task_model.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (valid_period_correspondence Task pR pL Hp tsk))|].
    apply ar_imp_correspondence;
      [exact (respects_periodic_task_model_correspondence Task pR pL Hp Job jtR jtL Hjt
        jaR jaL Hja arrR arrL Harr tsk)|].
    exact (pas_respects_sporadic_related tsk).
  Qed.

  Definition src_periodic_task_sets_respect_sporadic_task_model : Prop :=
    ltac:(body_of (fun s : S.statement_periodic_task_sets_respect_sporadic_task_model =>
      s Task pR Job jtR jaR arrR)).
  Definition tgt_periodic_task_sets_respect_sporadic_task_model : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_PeriodicAsSporadic_periodic_task_sets_respect_sporadic_task_model
      Task dT pL Job dJ jtL jaL arrL)).
  Theorem periodic_task_sets_respect_sporadic_task_model_correspondence :
    PropSPropRel src_periodic_task_sets_respect_sporadic_task_model
      tgt_periodic_task_sets_respect_sporadic_task_model.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply pas_forall_list. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (valid_periods_correspondence Task pR pL Hp tsR tsL Hts)|].
    apply ar_imp_correspondence;
      [exact (taskset_respects_periodic_task_model_correspondence Task pR pL Hp tsR tsL Hts
        Job jtR jtL Hjt jaR jaL Hja arrR arrL Harr)|].
    cbn [prosa.model.task.arrival.sporadic.taskset_respects_sporadic_task_model
      I.Prosa_Model_Task_Arrival_Sporadic_taskset_respects_sporadic_task_model].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    exact (pas_respects_sporadic_related tsk).
  Qed.
End PeriodicAsSporadic.
