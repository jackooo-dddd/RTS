From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From prosa Require Import SporadicAsCurveSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSporadicAsCurve ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence NatSubCorrespondence DivModCorrespondence
  CurvesCorrespondence.

Module I := ImportedSporadicAsCurve.
Module S := SporadicAsCurveSemanticSource.SporadicAsCurveSemanticSource.
Module B := prosa.FactsSporadicArrivalBoundSemanticSource.FactsSporadicArrivalBoundSemanticSource.

(** Correspondences for [model/task/arrival/sporadic_as_curve.v].

    Source side: the extracted byte-identical instance block
    [S.MaxArrivalsSporadic] and the extracted statements [S.statement_X]
    specialised at their leading class/data inputs; target side: the imported
    Lean instance and theorem types.  Inputs: the sporadic model by its
    observable field ([SubNatRel]), [job_task] by [Lean.eq], [job_arrival] by
    [ArJobArrivalRel], arrival sequences by [ArArrivalSequenceRel]; task sets
    are covered in both directions by [ArListRel].  The curve predicates are
    closed by the accepted [CurvesCorrespondence], the sporadic bound by the
    accepted arrival-bound certificate. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma sac_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xR xL, ArListRel xR xL -> PropSPropRel (PR xR) (PL xL)) ->
  PropSPropRel (forall xR, PR xR) (forall xL, PL xL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR xL. exact (prop_to_sprop _ _ (H _ _ (ar_list_target_roundtrip xL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro xR.
    exact (sprop_to_prop _ _ (H xR (ar_list_to_imported xR) (@Lean.eq_refl _ _)) (HL _)).
Qed.


(** ** Logical connectives and sporadic-model inputs (replayed from the
    accepted arrival-bound certificate) *)

Lemma sac_eq_correspondence (T : Type) (xR xL yR yL : T) :
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

Lemma sac_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma sac_neq_correspondence (T : Type) (x y : T) :
  PropSPropRel (x <> y) (I.Ne T x y).
Proof.
  unfold I.Ne, I.Not.
  apply ar_imp_correspondence.
  - exact (sac_eq_correspondence T x x y y (@Lean.eq_refl _ _) (@Lean.eq_refl _ _)).
  - exact sac_false_correspondence.
Qed.

Section SporadicAsCurve.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.

  Variable modelR : prosa.model.task.arrival.sporadic.SporadicModel Task.
  Variable modelL : I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task dT.
  Hypothesis Hmodel : forall tsk : Task,
    SubNatRel (@prosa.model.task.arrival.sporadic.task_min_inter_arrival_time Task modelR tsk)
      (I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time
        Task dT modelL tsk).

  Lemma sac_max_sporadic_arrivals_related (tsk : Task) :
    SubNatFunRel (@B.max_sporadic_arrivals Task modelR tsk)
      (I.Prosa_Analysis_Facts_Sporadic_ArrivalBound_max_sporadic_arrivals Task dT modelL tsk).
  Proof.
    intros dR dL Hd.
    unfold B.max_sporadic_arrivals, prosa.util.div_mod.div_ceil.
    cbn [I.Prosa_Analysis_Facts_Sporadic_ArrivalBound_max_sporadic_arrivals].
    exact (dm_div_ceil_correspondence _ _ _ _ Hd (Hmodel tsk)).
  Qed.

  Let BOUND := sac_max_sporadic_arrivals_related.

  (** The instance: related as a [MaxArrivals] curve family. *)
  Theorem MaxArrivalsSporadic_correspondence :
    CvMaxArrivalsRel Task (@S.MaxArrivalsSporadic Task modelR)
      (I.Prosa_Model_Task_Arrival_SporadicAsCurve_MaxArrivalsSporadic Task dT modelL).
  Proof. intro tsk. exact (BOUND tsk). Qed.

  Definition src_sporadic_arrival_curve_valid : Prop :=
    ltac:(body_of (fun s : S.statement_sporadic_arrival_curve_valid => s Task modelR)).
  Definition tgt_sporadic_arrival_curve_valid : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_SporadicAsCurve_sporadic_arrival_curve_valid
      Task dT modelL)).

  Theorem sporadic_arrival_curve_valid_correspondence :
    PropSPropRel src_sporadic_arrival_curve_valid tgt_sporadic_arrival_curve_valid.
  Proof.
    apply ar_forall_identity_correspondence. intro tsk.
    exact (valid_arrival_curve_correspondence _ _ (BOUND tsk)).
  Qed.

  Definition src_sporadic_task_sets_arrival_curve_valid : Prop :=
    ltac:(body_of (fun s : S.statement_sporadic_task_sets_arrival_curve_valid => s Task modelR)).
  Definition tgt_sporadic_task_sets_arrival_curve_valid : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_SporadicAsCurve_sporadic_task_sets_arrival_curve_valid
      Task dT modelL)).

  Theorem sporadic_task_sets_arrival_curve_valid_correspondence :
    PropSPropRel src_sporadic_task_sets_arrival_curve_valid
      tgt_sporadic_task_sets_arrival_curve_valid.
  Proof.
    apply sac_forall_list. intros tsR tsL Hts.
    exact (valid_taskset_arrival_curve_correspondence Task _ _ _ _ Hts
      MaxArrivalsSporadic_correspondence).
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
  Lemma sac_valid_min_inter_arrival_related (tsk : Task) :
    PropSPropRel
      (is_true (@prosa.model.task.arrival.sporadic.valid_task_min_inter_arrival_time
        Task modelR tsk))
      (Lean.eq (I.Prosa_Model_Task_Arrival_Sporadic_valid_task_min_inter_arrival_time
        Task dT modelL tsk) I.Bool_true).
  Proof.
    apply ar_bool_truth_correspondence. cbn.
    exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical 0) (Hmodel tsk)).
  Qed.

  Lemma sac_respects_sporadic_related (tsk : Task) :
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
    apply ar_imp_correspondence; [exact (sac_neq_correspondence Job j j')|].
    apply ar_imp_correspondence;
      [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (arrives_in_correspondence_certificate Job arrR arrL j' Harr)|].
    apply ar_imp_correspondence;
      [exact (sac_eq_correspondence _ _ _ _ _ (Hjt j) (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence;
      [exact (sac_eq_correspondence _ _ _ _ _ (Hjt j') (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j'))|].
    exact (sub_nat_le_correspondence _ _ _ _
      (sub_add_correspondence _ _ _ _ (Hja j) (Hmodel tsk)) (Hja j')).
  Qed.

  Let SPOR := sac_respects_sporadic_related.
  Let VMIN := sac_valid_min_inter_arrival_related.

  Definition src_sporadic_arrival_curve_respects_max_arrivals : Prop :=
    ltac:(body_of (fun s : S.statement_sporadic_arrival_curve_respects_max_arrivals =>
      s Task modelR Job jtR jaR arrR)).
  Definition tgt_sporadic_arrival_curve_respects_max_arrivals : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Model_Task_Arrival_SporadicAsCurve_sporadic_arrival_curve_respects_max_arrivals
        Task dT modelL Job dJ jtL jaL arrL)).

  Theorem sporadic_arrival_curve_respects_max_arrivals_correspondence :
    PropSPropRel src_sporadic_arrival_curve_respects_max_arrivals
      tgt_sporadic_arrival_curve_respects_max_arrivals.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (SPOR tsk)|].
    apply ar_imp_correspondence; [exact (VMIN tsk)|].
    exact (respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsk _ _
      (BOUND tsk)).
  Qed.

  Definition src_sporadic_task_sets_respects_max_arrivals : Prop :=
    ltac:(body_of (fun s : S.statement_sporadic_task_sets_respects_max_arrivals =>
      s Task modelR Job jtR jaR arrR)).
  Definition tgt_sporadic_task_sets_respects_max_arrivals : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Model_Task_Arrival_SporadicAsCurve_sporadic_task_sets_respects_max_arrivals
        Task dT modelL Job dJ jtL jaL arrL)).

  Theorem sporadic_task_sets_respects_max_arrivals_correspondence :
    PropSPropRel src_sporadic_task_sets_respects_max_arrivals
      tgt_sporadic_task_sets_respects_max_arrivals.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply sac_forall_list. intros tsR tsL Hts.
    have MEM := fun tsk => ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts).
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence. intro tsk.
      apply ar_imp_correspondence; [exact (MEM tsk)|]. exact (VMIN tsk). }
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence. intro tsk.
      apply ar_imp_correspondence; [exact (MEM tsk)|]. exact (SPOR tsk). }
    exact (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr
      tsR tsL Hts _ _ MaxArrivalsSporadic_correspondence).
  Qed.
End SporadicAsCurve.
