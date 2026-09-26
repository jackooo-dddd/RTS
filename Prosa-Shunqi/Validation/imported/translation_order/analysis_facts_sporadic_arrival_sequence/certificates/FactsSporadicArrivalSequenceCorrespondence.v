From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsSporadicArrivalSequenceSemanticSource.
From prosa Require Import model.task.arrivals model.task.arrival.sporadic.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsSporadicArrivalSequence ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence.

Module I := ImportedFactsSporadicArrivalSequence.
Module S := FactsSporadicArrivalSequenceSemanticSource.FactsSporadicArrivalSequenceSemanticSource.

(** Statement correspondences for [analysis/facts/sporadic/arrival_sequence.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.
    Inputs: the sporadic model by its observable field ([SubNatRel]),
    [job_task] by [Lean.eq], [job_arrival] by [ArJobArrivalRel], arrival
    sequences by [ArArrivalSequenceRel]; tasks and jobs are identity carriers,
    Nats are covered in both directions.  Task arrivals, [job_index],
    [prev_job], [size], [index] and concatenation are closed by the accepted
    arrival-sequence certificates; the sporadic-model propositions and the
    logical connectives are replayed from the accepted sporadic certificates.
    No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fsas_eq_correspondence (T : Type) (xR xL yR yL : T) :
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

Lemma fsas_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma fsas_neq_correspondence (T : Type) (x y : T) :
  PropSPropRel (x <> y) (I.Ne T x y).
Proof.
  unfold I.Ne, I.Not.
  apply ar_imp_correspondence.
  - exact (fsas_eq_correspondence T x x y y (@Lean.eq_refl _ _) (@Lean.eq_refl _ _)).
  - exact fsas_false_correspondence.
Qed.

Lemma fsas_exists_identity (T : Type) (P : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (P x) (PL x)) ->
  PropSPropRel (exists x, P x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Section Arrivals.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
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

  Let TAJ (j : Job) := task_arrivals_at_job_arrival_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j.
  Let UPTO (j : Job) := task_arrivals_up_to_job_arrival_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j.
  Let IDX (j : Job) := job_index_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j.
  Let PREV (j : Job) := prev_job_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j.

  Lemma fsas_singleton_related (j : Job) : ArListRel [:: j] (I.List_cons Job j (I.List_nil Job)).
  Proof. exact (@Lean.eq_refl _ _). Qed.

  Definition src_task_arrivals_at_as_task_arrivals_between : Prop :=
    ltac:(body_of (fun s : S.statement_task_arrivals_at_as_task_arrivals_between =>
      s Task Job jtR jaR arrR)).
  Definition tgt_task_arrivals_at_as_task_arrivals_between : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Sporadic_ArrivalSequence_task_arrivals_at_as_task_arrivals_between
      Task dT Job dJ jtL jaL arrL)).

  Theorem task_arrivals_at_as_task_arrivals_between_correspondence :
    PropSPropRel src_task_arrivals_at_as_task_arrivals_between
      tgt_task_arrivals_at_as_task_arrivals_between.
  Proof.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_imp_correspondence;
      [exact (fsas_eq_correspondence _ _ _ _ _ (Hjt j1) (@Lean.eq_refl _ _))|].
    apply ar_list_eq_correspondence; [exact (TAJ j1)|].
    exact (task_arrivals_between_correspondence Job Task jtR jtL Hjt arrR arrL Harr tsk tsk _ _ _ _
      (@Lean.eq_refl _ _) (Hja j1) (ari_succ_related _ _ (Hja j1))).
  Qed.

  Variable modelR : prosa.model.task.arrival.sporadic.SporadicModel Task.
  Variable modelL : I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task dT.
  Hypothesis Hmodel : forall tsk : Task,
    SubNatRel (@prosa.model.task.arrival.sporadic.task_min_inter_arrival_time Task modelR tsk)
      (I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time
        Task dT modelL tsk).

  Let VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.

  Lemma fsas_valid_min_inter_arrival_related (tsk : Task) :
    PropSPropRel
      (is_true (@prosa.model.task.arrival.sporadic.valid_task_min_inter_arrival_time Task modelR tsk))
      (Lean.eq (I.Prosa_Model_Task_Arrival_Sporadic_valid_task_min_inter_arrival_time
        Task dT modelL tsk) I.Bool_true).
  Proof.
    apply ar_bool_truth_correspondence. cbn.
    exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical 0) (Hmodel tsk)).
  Qed.

  Lemma fsas_respects_sporadic_related (tsk : Task) :
    PropSPropRel
      (@prosa.model.task.arrival.sporadic.respects_sporadic_task_model Task modelR Job jtR jaR arrR tsk)
      (I.Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model
        Task dT modelL Job dJ jtL jaL arrL tsk).
  Proof.
    cbn [prosa.model.task.arrival.sporadic.respects_sporadic_task_model
      I.Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence; [exact (fsas_neq_correspondence Job j j')|].
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j' Harr)|].
    apply ar_imp_correspondence;
      [exact (fsas_eq_correspondence _ _ _ _ _ (Hjt j) (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence;
      [exact (fsas_eq_correspondence _ _ _ _ _ (Hjt j') (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j'))|].
    exact (sub_nat_le_correspondence _ _ _ _
      (sub_add_correspondence _ _ _ _ (Hja j) (Hmodel tsk)) (Hja j')).
  Qed.

  Definition src_size_task_arrivals_at_leq_one : Prop :=
    ltac:(body_of (fun s : S.statement_size_task_arrivals_at_leq_one => s Task modelR Job jtR jaR arrR)).
  Definition tgt_size_task_arrivals_at_leq_one : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Sporadic_ArrivalSequence_size_task_arrivals_at_leq_one
      Task dT modelL Job dJ jtL jaL arrL)).

  Theorem size_task_arrivals_at_leq_one_correspondence :
    PropSPropRel src_size_task_arrivals_at_leq_one tgt_size_task_arrivals_at_leq_one.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    unfold I.Not. apply ar_imp_correspondence; [|exact fsas_false_correspondence].
    apply fsas_exists_identity. intro j.
    apply ar_and_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 1) (ari_size_related Job _ _ (TAJ j)))|].
    rewrite -> (imported_eq_to_coq_eq _ _ (Hjt j)) at 1.
    have E := imported_eq_to_coq_eq _ _ (Hjt j).
    apply ar_and_correspondence.
    - rewrite -E. exact (fsas_respects_sporadic_related _).
    - rewrite -E. exact (fsas_valid_min_inter_arrival_related _).
  Qed.

  Let SPOR := fsas_respects_sporadic_related.
  Let VMIN := fsas_valid_min_inter_arrival_related.

  Ltac fsas_prefix tsk j1 :=
    apply ar_imp_correspondence; [exact VALID|];
    apply ar_forall_identity_correspondence; intro tsk;
    apply ar_imp_correspondence; [exact (SPOR tsk)|];
    apply ar_imp_correspondence; [exact (VMIN tsk)|];
    apply ar_forall_identity_correspondence; intro j1;
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j1 Harr)|];
    apply ar_imp_correspondence; [exact (fsas_eq_correspondence _ _ _ _ _ (Hjt j1) (@Lean.eq_refl _ _))|].

  Definition src_only_j_in_task_arrivals_at_j : Prop :=
    ltac:(body_of (fun s : S.statement_only_j_in_task_arrivals_at_j => s Task modelR Job jtR jaR arrR)).
  Definition tgt_only_j_in_task_arrivals_at_j : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Sporadic_ArrivalSequence_only_j_in_task_arrivals_at_j
      Task dT modelL Job dJ jtL jaL arrL)).

  Theorem only_j_in_task_arrivals_at_j_correspondence :
    PropSPropRel src_only_j_in_task_arrivals_at_j tgt_only_j_in_task_arrivals_at_j.
  Proof.
    fsas_prefix tsk j1.
    exact (ar_list_eq_correspondence Job _ _ _ _ (TAJ j1) (fsas_singleton_related j1)).
  Qed.

  Definition src_only_j_at_job_arrival_j : Prop :=
    ltac:(body_of (fun s : S.statement_only_j_at_job_arrival_j => s Task modelR Job jtR jaR arrR)).
  Definition tgt_only_j_at_job_arrival_j : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Sporadic_ArrivalSequence_only_j_at_job_arrival_j
      Task dT modelL Job dJ jtL jaL arrL)).

  Theorem only_j_at_job_arrival_j_correspondence :
    PropSPropRel src_only_j_at_job_arrival_j tgt_only_j_at_job_arrival_j.
  Proof.
    fsas_prefix tsk j1.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ (Hja j1) Ht)|].
    exact (ar_list_eq_correspondence Job _ _ _ _
      (task_arrivals_at_correspondence Job Task jtR jtL Hjt arrR arrL Harr tsk tsk tR tL (@Lean.eq_refl _ _) Ht)
      (fsas_singleton_related j1)).
  Qed.

  Definition src_index_j_in_task_arrivals_at : Prop :=
    ltac:(body_of (fun s : S.statement_index_j_in_task_arrivals_at => s Task modelR Job jtR jaR arrR)).
  Definition tgt_index_j_in_task_arrivals_at : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Sporadic_ArrivalSequence_index_j_in_task_arrivals_at
      Task dT modelL Job dJ jtL jaL arrL)).

  Theorem index_j_in_task_arrivals_at_correspondence :
    PropSPropRel src_index_j_in_task_arrivals_at tgt_index_j_in_task_arrivals_at.
  Proof.
    fsas_prefix tsk j1.
    exact (sub_nat_eq_correspondence _ _ _ _ (ari_index_related Job j1 _ _ (TAJ j1)) (sub_nat_rel_canonical 0)).
  Qed.

  Lemma fsas_prev_arrival_related (j : Job) :
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR (@prev_job Job Task jtR jaR arrR j))
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL
        (I.Prosa_Model_Task_Arrivals_prev_job Job dJ Task dT jtL jaL arrL j)).
  Proof.
    exact (sub_imported_eq_trans _ _ _ (Hja _)
      (sub_imported_eq_congr (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL) _ _ (PREV j))).
  Qed.

  Definition src_prev_job_arr_lt : Prop :=
    ltac:(body_of (fun s : S.statement_prev_job_arr_lt => s Task modelR Job jtR jaR arrR)).
  Definition tgt_prev_job_arr_lt : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Sporadic_ArrivalSequence_prev_job_arr_lt
      Task dT modelL Job dJ jtL jaL arrL)).

  Theorem prev_job_arr_lt_correspondence :
    PropSPropRel src_prev_job_arr_lt tgt_prev_job_arr_lt.
  Proof.
    fsas_prefix tsk j1.
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (IDX j1))|].
    exact (sub_nat_lt_correspondence _ _ _ _ (fsas_prev_arrival_related j1) (Hja j1)).
  Qed.

  Definition src_prev_job_cat : Prop :=
    ltac:(body_of (fun s : S.statement_prev_job_cat => s Task modelR Job jtR jaR arrR)).
  Definition tgt_prev_job_cat : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Sporadic_ArrivalSequence_prev_job_cat
      Task dT modelL Job dJ jtL jaL arrL)).

  Theorem prev_job_cat_correspondence :
    PropSPropRel src_prev_job_cat tgt_prev_job_cat.
  Proof.
    fsas_prefix tsk j1.
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (IDX j1))|].
    apply ar_list_eq_correspondence; [|exact (UPTO j1)].
    apply ar_append_related; [|exact (fsas_singleton_related j1)].
    exact (sub_imported_eq_trans _ _ _ (UPTO _)
      (sub_imported_eq_congr
        (I.Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job dJ Task dT jtL jaL arrL) _ _
        (PREV j1))).
  Qed.
End Arrivals.
