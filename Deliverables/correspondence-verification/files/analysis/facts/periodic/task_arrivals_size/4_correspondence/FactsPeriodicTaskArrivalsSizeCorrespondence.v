From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsPeriodicTaskArrivalsSizeSemanticSource.
From prosa Require Import model.task.arrivals analysis.definitions.infinite_jobs.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPeriodicTaskArrivalsSize ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskOffsetCorrespondence PeriodicCorrespondence InfiniteJobsCorrespondence.

Module I := ImportedFactsPeriodicTaskArrivalsSize.
Module S := FactsPeriodicTaskArrivalsSizeSemanticSource.FactsPeriodicTaskArrivalsSizeSemanticSource.
Module O := TaskOffsetSemanticSource.TaskOffsetSemanticSource.
Module P := PeriodicSemanticSource.PeriodicSemanticSource.

(** Statement correspondences for [analysis/facts/periodic/task_arrivals_size.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types, the task offsets where they
    occur, the periodic model, [job_task], [job_arrival] and the arrival
    sequence); target side: the imported Lean theorem types at related inputs
    (the accepted [OffRel] and [PerRel], [Lean.eq] on [job_task],
    [ArJobArrivalRel], [ArArrivalSequenceRel]).  Tasks and jobs are identity
    carriers, Nats are covered in both directions.  The task-arrival lists
    are related by the accepted arrivals certificates ([ArListRel]), their
    sizes by the accepted [ari_size_related], [x.+1] by the accepted
    [ari_succ_related]; the empty list by the list conversion's round trip.
    Arrival-sequence validity, [valid_offset], [valid_period], the periodic
    task model, [infinite_jobs] and [job_index] are closed by the accepted
    certificates re-instantiated at this artifact.  No source or target
    theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma ptas_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma ptas_nat_neq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (aR <> bR) (I.Ne Lean.Nat aL bL).
Proof.
  intros Ha Hb. unfold I.Ne, I.Not.
  apply ar_imp_correspondence.
  - exact (sub_nat_eq_correspondence aR aL bR bL Ha Hb).
  - exact ptas_false_correspondence.
Qed.

Lemma ptas_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p|q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intro H. destruct H as [p|q].
    + exact (strictly_inhabits (or_introl _ (sprop_to_prop _ _ HP p))).
    + exact (strictly_inhabits (or_intror _ (sprop_to_prop _ _ HQ q))).
Qed.

Lemma ptas_exists_identity (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma ptas_list_eq_nil_correspondence (T : Type) (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL -> PropSPropRel (xsR = [::]) (Lean.eq xsL (I.List_nil T)).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hxs)
      (coq_eq_to_imported_eq _ _ (f_equal ar_list_to_imported E))).
  - intro HL. apply strictly_inhabits.
    have E := f_equal ar_list_to_rocq (imported_eq_to_coq_eq _ _ (sub_imported_eq_trans _ _ _ Hxs HL)).
    rewrite ar_list_source_roundtrip in E.
    exact E.
Qed.

Section TaskArrivalsSize.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
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

  Let VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.
  Let VP tsk := valid_period_correspondence Task pR pL Hp tsk.
  Let RP tsk := respects_periodic_task_model_correspondence Task pR pL Hp Job jtR jtL Hjt jaR jaL Hja
    arrR arrL Harr tsk.
  Let TAT tsk tR tL (Ht : SubNatRel tR tL) :=
    ari_size_related Job _ _ (task_arrivals_at_correspondence Job Task jtR jtL Hjt arrR arrL Harr
      tsk tsk tR tL (@Lean.eq_refl _ _) Ht).
  Let TAB tsk t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :=
    ari_size_related Job _ _ (task_arrivals_between_correspondence Job Task jtR jtL Hjt arrR arrL Harr
      tsk tsk t1R t1L t2R t2L (@Lean.eq_refl _ _) H1 H2).
  Let TAU tsk tR tL (Ht : SubNatRel tR tL) :=
    ari_size_related Job _ _ (task_arrivals_up_to_correspondence Job Task jtR jtL Hjt arrR arrL Harr
      tsk tsk tR tL (@Lean.eq_refl _ _) Ht).
  Let ONE := sub_nat_rel_canonical (S O).

  Definition src_task_arrivals_at_size_cases : Prop :=
    ltac:(body_of (fun s : S.statement_task_arrivals_at_size_cases => s Task pR Job jtR jaR arrR)).
  Definition tgt_task_arrivals_at_size_cases : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Periodic_TaskArrivalsSize_task_arrivals_at_size_cases
      Task dT pL Job dJ jtL jaL arrL)).
  Theorem task_arrivals_at_size_cases_correspondence :
    PropSPropRel src_task_arrivals_at_size_cases tgt_task_arrivals_at_size_cases.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (VP tsk))|].
    apply ar_imp_correspondence; [exact (RP tsk)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ptas_or_correspondence.
    - exact (sub_nat_eq_correspondence _ _ _ _ (TAT tsk _ _ Ht) (sub_nat_rel_canonical O)).
    - exact (sub_nat_eq_correspondence _ _ _ _ (TAT tsk _ _ Ht) ONE).
  Qed.

  Section Offset.
    Variable oR : O.TaskOffset Task.
    Variable oL : I.Prosa_Model_Task_Offset_TaskOffset Task dT.
    Hypothesis Hoff : OffRel Task oR oL.

    Let VO tsk := valid_offset_correspondence Task oR oL Hoff Job jtR jtL Hjt jaR jaL Hja arrR arrL Harr tsk.
    Let INF := infinite_jobs_correspondence Task Job jtR jtL Hjt jaR jaL Hja arrR arrL Harr.
    Let POINT tsk nR nL (Hn : SubNatRel nR nL) :=
      sub_add_correspondence _ _ _ _ (Hoff tsk) (sub_mul_correspondence _ _ _ _ Hn (Hp tsk)).

    Ltac ptas_prefix :=
      apply ar_imp_correspondence; [exact VALID|];
      apply ar_forall_identity_correspondence; let tsk := fresh "tsk" in intro tsk;
      apply ar_imp_correspondence; [exact (VO tsk)|];
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (VP tsk))|];
      apply ar_imp_correspondence; [exact (RP tsk)|].

    Definition src_task_arrivals_size_at_non_arrival : Prop :=
      ltac:(body_of (fun s : S.statement_task_arrivals_size_at_non_arrival => s Task oR pR Job jtR jaR arrR)).
    Definition tgt_task_arrivals_size_at_non_arrival : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Periodic_TaskArrivalsSize_task_arrivals_size_at_non_arrival
        Task dT oL pL Job dJ jtL jaL arrL)).
    Theorem task_arrivals_size_at_non_arrival_correspondence :
      PropSPropRel src_task_arrivals_size_at_non_arrival tgt_task_arrivals_size_at_non_arrival.
    Proof.
      ptas_prefix.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence.
      - apply ar_forall_nat_correspondence. intros nR nL Hn.
        exact (ptas_nat_neq_correspondence _ _ _ _ Ht (POINT tsk _ _ Hn)).
      - exact (ptas_list_eq_nil_correspondence Job _ _
          (task_arrivals_at_correspondence Job Task jtR jtL Hjt arrR arrL Harr
            tsk tsk tR tL (@Lean.eq_refl _ _) Ht)).
    Qed.

    Definition src_size_task_arrivals_between_eq0 : Prop :=
      ltac:(body_of (fun s : S.statement_size_task_arrivals_between_eq0 => s Task oR pR Job jtR jaR arrR)).
    Definition tgt_size_task_arrivals_between_eq0 : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Periodic_TaskArrivalsSize_size_task_arrivals_between_eq0
        Task dT oL pL Job dJ jtL jaL arrL)).
    Theorem size_task_arrivals_between_eq0_correspondence :
      PropSPropRel src_size_task_arrivals_between_eq0 tgt_size_task_arrivals_between_eq0.
    Proof.
      ptas_prefix.
      apply ar_forall_nat_correspondence. intros nR nL Hn.
      exact (sub_nat_eq_correspondence _ _ _ _
        (TAB tsk _ _ (ari_succ_related _ _ (POINT tsk _ _ Hn))
          _ _ (POINT tsk _ _ (ari_succ_related _ _ Hn)))
        (sub_nat_rel_canonical O)).
    Qed.

    Definition src_jobs_exists_later : Prop :=
      ltac:(body_of (fun s : S.statement_jobs_exists_later => s Task oR pR Job jtR jaR arrR)).
    Definition tgt_jobs_exists_later : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Periodic_TaskArrivalsSize_jobs_exists_later
        Task dT oL pL Job dJ jtL jaL arrL)).
    Theorem jobs_exists_later_correspondence :
      PropSPropRel src_jobs_exists_later tgt_jobs_exists_later.
    Proof.
      ptas_prefix.
      apply ar_imp_correspondence; [exact INF|].
      apply ar_forall_nat_correspondence. intros nR nL Hn.
      apply ptas_exists_identity. intro j.
      apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      apply ar_and_correspondence;
        [exact (per_eq_correspondence Task _ _ tsk tsk (Hjt j) (@Lean.eq_refl _ _))|].
      apply ar_and_correspondence;
        [exact (sub_nat_eq_correspondence _ _ _ _ (Hja j) (POINT tsk _ _ Hn))|].
      exact (sub_nat_eq_correspondence _ _ _ _
        (job_index_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j) Hn).
    Qed.

    Definition src_task_arrivals_at_size : Prop :=
      ltac:(body_of (fun s : S.statement_task_arrivals_at_size => s Task oR pR Job jtR jaR arrR)).
    Definition tgt_task_arrivals_at_size : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Periodic_TaskArrivalsSize_task_arrivals_at_size
        Task dT oL pL Job dJ jtL jaL arrL)).
    Theorem task_arrivals_at_size_correspondence :
      PropSPropRel src_task_arrivals_at_size tgt_task_arrivals_at_size.
    Proof.
      ptas_prefix.
      apply ar_imp_correspondence; [exact INF|].
      apply ar_forall_nat_correspondence. intros nR nL Hn.
      exact (sub_nat_eq_correspondence _ _ _ _ (TAT tsk _ _ (POINT tsk _ _ Hn)) ONE).
    Qed.

    Definition src_size_task_arrivals_up_to_offset : Prop :=
      ltac:(body_of (fun s : S.statement_size_task_arrivals_up_to_offset => s Task oR pR Job jtR jaR arrR)).
    Definition tgt_size_task_arrivals_up_to_offset : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Periodic_TaskArrivalsSize_size_task_arrivals_up_to_offset
        Task dT oL pL Job dJ jtL jaL arrL)).
    Theorem size_task_arrivals_up_to_offset_correspondence :
      PropSPropRel src_size_task_arrivals_up_to_offset tgt_size_task_arrivals_up_to_offset.
    Proof.
      ptas_prefix.
      apply ar_imp_correspondence; [exact INF|].
      exact (sub_nat_eq_correspondence _ _ _ _ (TAU tsk _ _ (Hoff tsk)) ONE).
    Qed.

    Definition src_task_arrivals_up_to_size : Prop :=
      ltac:(body_of (fun s : S.statement_task_arrivals_up_to_size => s Task oR pR Job jtR jaR arrR)).
    Definition tgt_task_arrivals_up_to_size : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Periodic_TaskArrivalsSize_task_arrivals_up_to_size
        Task dT oL pL Job dJ jtL jaL arrL)).
    Theorem task_arrivals_up_to_size_correspondence :
      PropSPropRel src_task_arrivals_up_to_size tgt_task_arrivals_up_to_size.
    Proof.
      ptas_prefix.
      apply ar_imp_correspondence; [exact INF|].
      apply ar_forall_nat_correspondence. intros nR nL Hn.
      exact (sub_nat_eq_correspondence _ _ _ _ (TAU tsk _ _ (POINT tsk _ _ Hn))
        (sub_add_correspondence _ _ _ _ Hn ONE)).
    Qed.

    Definition src_eq_size_of_task_arrivals_seperated_by_period : Prop :=
      ltac:(body_of (fun s : S.statement_eq_size_of_task_arrivals_seperated_by_period =>
        s Task oR pR Job jtR jaR arrR)).
    Definition tgt_eq_size_of_task_arrivals_seperated_by_period : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_Periodic_TaskArrivalsSize_eq_size_of_task_arrivals_seperated_by_period
          Task dT oL pL Job dJ jtL jaL arrL)).
    Theorem eq_size_of_task_arrivals_seperated_by_period_correspondence :
      PropSPropRel src_eq_size_of_task_arrivals_seperated_by_period
        tgt_eq_size_of_task_arrivals_seperated_by_period.
    Proof.
      ptas_prefix.
      apply ar_imp_correspondence; [exact INF|].
      apply ar_forall_nat_correspondence. intros nR nL Hn.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ (Hoff tsk) Ht)|].
      exact (sub_nat_eq_correspondence _ _ _ _ (TAT tsk _ _ Ht)
        (TAT tsk _ _ (sub_add_correspondence _ _ _ _ Ht (sub_mul_correspondence _ _ _ _ Hn (Hp tsk))))).
    Qed.
  End Offset.
End TaskArrivalsSize.
