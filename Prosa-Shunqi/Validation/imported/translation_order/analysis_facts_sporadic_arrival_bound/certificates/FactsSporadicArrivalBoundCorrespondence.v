From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From prosa Require Import FactsSporadicArrivalBoundSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsSporadicArrivalBound ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence NatSubCorrespondence DivModCorrespondence.

Module I := ImportedFactsSporadicArrivalBound.
Module S := FactsSporadicArrivalBoundSemanticSource.FactsSporadicArrivalBoundSemanticSource.

(** Correspondences for [analysis/facts/sporadic/arrival_bound.v].

    Source side: the extracted definition [S.max_sporadic_arrivals] (a
    byte-identical block) and the extracted statements [S.statement_X]
    specialised at their leading class/data inputs; target side: the imported
    Lean definition and theorem types.  Inputs: the sporadic model by its
    observable field ([SubNatRel], as in the accepted Sporadic certificate),
    [job_task] by [Lean.eq], [job_arrival] by the accepted [ArJobArrivalRel],
    arrival sequences by [ArArrivalSequenceRel].  Tasks and jobs are identity
    carriers; Nats are covered in both directions.  [div_ceil] is closed by
    the replayed DivMod correspondence, task arrivals by the accepted
    Arrivals correspondences, and [nth] against [List.getD] by the accepted
    [ari_nth_related]. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Logical connectives (replayed from the accepted Sporadic certificate) *)

Lemma fsb_eq_correspondence (T : Type) (xR xL yR yL : T) :
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

Lemma fsb_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma fsb_neq_correspondence (T : Type) (x y : T) :
  PropSPropRel (x <> y) (I.Ne T x y).
Proof.
  unfold I.Ne, I.Not.
  apply ar_imp_correspondence.
  - exact (fsb_eq_correspondence T x x y y (@Lean.eq_refl _ _) (@Lean.eq_refl _ _)).
  - exact fsb_false_correspondence.
Qed.

Section SporadicArrivalBound.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.

  Variable modelR : prosa.model.task.arrival.sporadic.SporadicModel Task.
  Variable modelL : I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task dT.
  Hypothesis Hmodel : forall tsk : Task,
    SubNatRel (@prosa.model.task.arrival.sporadic.task_min_inter_arrival_time Task modelR tsk)
      (I.Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time
        Task dT modelL tsk).

  Lemma max_sporadic_arrivals_correspondence (tsk : Task) (dR : nat) (dL : Lean.Nat) :
    SubNatRel dR dL ->
    SubNatRel (@S.max_sporadic_arrivals Task modelR tsk dR)
      (I.Prosa_Analysis_Facts_Sporadic_ArrivalBound_max_sporadic_arrivals Task dT modelL tsk dL).
  Proof.
    intro Hd.
    unfold S.max_sporadic_arrivals, prosa.util.div_mod.div_ceil.
    cbn [I.Prosa_Analysis_Facts_Sporadic_ArrivalBound_max_sporadic_arrivals].
    exact (dm_div_ceil_correspondence _ _ _ _ Hd (Hmodel tsk)).
  Qed.

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
  Let NUM (tsk : Task) t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :=
    number_of_task_arrivals_correspondence Job Task jtR jtL Hjt arrR arrL Harr tsk tsk
      t1R t1L t2R t2L (@Lean.eq_refl _ _) H1 H2.
  Let BETWEEN (tsk : Task) t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :=
    task_arrivals_between_correspondence Job Task jtR jtL Hjt arrR arrL Harr tsk tsk
      t1R t1L t2R t2L (@Lean.eq_refl _ _) H1 H2.

  Lemma fsb_valid_min_inter_arrival_related (tsk : Task) :
    PropSPropRel
      (is_true (@prosa.model.task.arrival.sporadic.valid_task_min_inter_arrival_time
        Task modelR tsk))
      (Lean.eq (I.Prosa_Model_Task_Arrival_Sporadic_valid_task_min_inter_arrival_time
        Task dT modelL tsk) I.Bool_true).
  Proof.
    apply ar_bool_truth_correspondence. cbn.
    exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical 0) (Hmodel tsk)).
  Qed.

  Lemma fsb_respects_sporadic_related (tsk : Task) :
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
    apply ar_imp_correspondence; [exact (fsb_neq_correspondence Job j j')|].
    apply ar_imp_correspondence;
      [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (arrives_in_correspondence_certificate Job arrR arrL j' Harr)|].
    apply ar_imp_correspondence;
      [exact (fsb_eq_correspondence _ _ _ _ _ (Hjt j) (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence;
      [exact (fsb_eq_correspondence _ _ _ _ _ (Hjt j') (@Lean.eq_refl _ _))|].
    apply ar_imp_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j'))|].
    exact (sub_nat_le_correspondence _ _ _ _
      (sub_add_correspondence _ _ _ _ (Hja j) (Hmodel tsk)) (Hja j')).
  Qed.

  (** *** arrival_of_nth_job *)
  Definition src_arrival_of_nth_job : Prop :=
    ltac:(body_of (fun s : S.statement_arrival_of_nth_job => s Task modelR Job jtR jaR arrR)).
  Definition tgt_arrival_of_nth_job : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Sporadic_ArrivalBound_arrival_of_nth_job
      Task dT modelL Job dJ jtL jaL arrL)).

  Theorem arrival_of_nth_job_correspondence :
    PropSPropRel src_arrival_of_nth_job tgt_arrival_of_nth_job.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fsb_respects_sporadic_related tsk)|].
    apply ar_imp_correspondence; [exact (fsb_valid_min_inter_arrival_related tsk)|].
    apply ar_forall_identity_correspondence. intro dummy.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply ar_forall_nat_correspondence. intros nR nL Hn.
    apply ar_forall_nat_correspondence. intros iR iL Hi.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence;
      [exact (sub_nat_eq_correspondence _ _ _ _ Hn (NUM tsk _ _ _ _ H1 H2))|].
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Hi Hn)|].
    apply ar_imp_correspondence.
    { exact (fsb_eq_correspondence _ _ _ _ _ (@Lean.eq_refl _ j)
        (ari_nth_related Job dummy _ _ _ _ (BETWEEN tsk _ _ _ _ H1 H2) Hi)). }
    exact (sub_nat_le_correspondence _ _ _ _
      (sub_add_correspondence _ _ _ _ H1 (sub_mul_correspondence _ _ _ _ (Hmodel tsk) Hi))
      (Hja j)).
  Qed.

  (** *** minimum_distance_for_n_sporadic_arrivals *)
  Definition src_minimum_distance_for_n_sporadic_arrivals : Prop :=
    ltac:(body_of (fun s : S.statement_minimum_distance_for_n_sporadic_arrivals =>
      s Task modelR Job jtR jaR arrR)).
  Definition tgt_minimum_distance_for_n_sporadic_arrivals : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Sporadic_ArrivalBound_minimum_distance_for_n_sporadic_arrivals
        Task dT modelL Job dJ jtL jaL arrL)).

  Theorem minimum_distance_for_n_sporadic_arrivals_correspondence :
    PropSPropRel src_minimum_distance_for_n_sporadic_arrivals
      tgt_minimum_distance_for_n_sporadic_arrivals.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fsb_respects_sporadic_related tsk)|].
    apply ar_imp_correspondence; [exact (fsb_valid_min_inter_arrival_related tsk)|].
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply ar_forall_nat_correspondence. intros nR nL Hn.
    apply ar_imp_correspondence;
      [exact (sub_nat_eq_correspondence _ _ _ _ (NUM tsk _ _ _ _ H1 H2) Hn)|].
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 1) Hn)|].
    rewrite -subn1.
    exact (sub_nat_lt_correspondence _ _ _ _
      (sub_add_correspondence _ _ _ _ H1
        (sub_mul_correspondence _ _ _ _ (Hmodel tsk)
          (dm_sub_correspondence _ _ _ _ Hn (sub_nat_rel_canonical 1))))
      H2).
  Qed.

  (** *** sporadic_task_arrivals_bound *)
  Definition src_sporadic_task_arrivals_bound : Prop :=
    ltac:(body_of (fun s : S.statement_sporadic_task_arrivals_bound =>
      s Task modelR Job jtR jaR arrR)).
  Definition tgt_sporadic_task_arrivals_bound : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Sporadic_ArrivalBound_sporadic_task_arrivals_bound
      Task dT modelL Job dJ jtL jaL arrL)).

  Theorem sporadic_task_arrivals_bound_correspondence :
    PropSPropRel src_sporadic_task_arrivals_bound tgt_sporadic_task_arrivals_bound.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (fsb_respects_sporadic_related tsk)|].
    apply ar_imp_correspondence; [exact (fsb_valid_min_inter_arrival_related tsk)|].
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    exact (sub_nat_le_correspondence _ _ _ _ (NUM tsk _ _ _ _ H1 H2)
      (max_sporadic_arrivals_correspondence tsk _ _ (dm_sub_correspondence _ _ _ _ H2 H1))).
  Qed.
End SporadicArrivalBound.
