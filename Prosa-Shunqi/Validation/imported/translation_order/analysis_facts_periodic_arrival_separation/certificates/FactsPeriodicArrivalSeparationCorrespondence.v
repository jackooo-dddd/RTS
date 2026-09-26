From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsPeriodicArrivalSeparationSemanticSource.
From prosa Require Import model.task.arrivals.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPeriodicArrivalSeparation ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  PeriodicCorrespondence.

Module I := ImportedFactsPeriodicArrivalSeparation.
Module S := FactsPeriodicArrivalSeparationSemanticSource.FactsPeriodicArrivalSeparationSemanticSource.
Module P := PeriodicSemanticSource.PeriodicSemanticSource.

(** Statement correspondences for [analysis/facts/periodic/arrival_separation.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types, the periodic model, [job_task],
    [job_arrival] and the arrival sequence); target side: the imported Lean
    theorem types at related inputs (the accepted [PerRel], [Lean.eq] on
    [job_task], [ArJobArrivalRel], [ArArrivalSequenceRel]).  Tasks and jobs
    are identity carriers, Nats are covered in both directions.  Validity of
    the arrival sequence, the periodic task model, [valid_period] and
    [job_index] are closed by the accepted arrival-sequence, arrivals and
    periodic certificates re-instantiated at this artifact.  No source or
    target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fpas_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma fpas_neq_correspondence (T : Type) (x y : T) :
  PropSPropRel (x <> y) (I.Ne T x y).
Proof.
  unfold I.Ne, I.Not.
  apply ar_imp_correspondence.
  - exact (per_eq_correspondence T x x y y (@Lean.eq_refl _ _) (@Lean.eq_refl _ _)).
  - exact fpas_false_correspondence.
Qed.

Section Separation.
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

  Let IDX (j : Job) := job_index_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j.
  Let VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.
  Let PERIODIC tsk :=
    respects_periodic_task_model_correspondence Task pR pL Hp Job jtR jtL Hjt jaR jaL Hja arrR arrL Harr tsk.
  Let TASK j tsk := per_eq_correspondence Task _ _ tsk tsk (Hjt j) (@Lean.eq_refl _ _).
  Let ARRIVES j := arrives_in_correspondence_certificate Job arrR arrL j Harr.

  Ltac fpas_prefix :=
    apply ar_imp_correspondence; [exact VALID|];
    apply ar_forall_identity_correspondence; let tsk := fresh "tsk" in intro tsk;
    apply ar_imp_correspondence; [exact (PERIODIC tsk)|];
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (valid_period_correspondence Task pR pL Hp tsk))|].

  Let SEP tsk j1 j2 nR nL (Hn : SubNatRel nR nL) :=
    ar_and_correspondence _ _ _ _ (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hn)
      (sub_nat_eq_correspondence _ _ _ _ (Hja j2)
        (sub_add_correspondence _ _ _ _ (Hja j1) (sub_mul_correspondence _ _ _ _ Hn (Hp tsk)))).

  Definition src_consecutive_job_separation : Prop :=
    ltac:(body_of (fun s : S.statement_consecutive_job_separation => s Task pR Job jtR jaR arrR)).
  Definition tgt_consecutive_job_separation : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Periodic_ArrivalSeparation_consecutive_job_separation
      Task dT pL Job dJ jtL jaL arrL)).
  Theorem consecutive_job_separation_correspondence :
    PropSPropRel src_consecutive_job_separation tgt_consecutive_job_separation.
  Proof.
    fpas_prefix.
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (ARRIVES j1)|].
    apply ar_imp_correspondence; [exact (ARRIVES j2)|].
    apply ar_imp_correspondence; [exact (TASK j1 tsk)|].
    apply ar_imp_correspondence; [exact (TASK j2 tsk)|].
    apply ar_imp_correspondence;
      [exact (sub_nat_eq_correspondence _ _ _ _ (IDX j2)
        (sub_add_correspondence _ _ _ _ (IDX j1) (sub_nat_rel_canonical (S O))))|].
    exact (sub_nat_eq_correspondence _ _ _ _ (Hja j2)
      (sub_add_correspondence _ _ _ _ (Hja j1) (Hp tsk))).
  Qed.

  Definition src_job_arrival_separation_when_index_diff_is_k : Prop :=
    ltac:(body_of (fun s : S.statement_job_arrival_separation_when_index_diff_is_k =>
      s Task pR Job jtR jaR arrR)).
  Definition tgt_job_arrival_separation_when_index_diff_is_k : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Periodic_ArrivalSeparation_job_arrival_separation_when_index_diff_is_k
        Task dT pL Job dJ jtL jaL arrL)).
  Theorem job_arrival_separation_when_index_diff_is_k_correspondence :
    PropSPropRel src_job_arrival_separation_when_index_diff_is_k
      tgt_job_arrival_separation_when_index_diff_is_k.
  Proof.
    fpas_prefix.
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (ARRIVES j1)|].
    apply ar_imp_correspondence; [exact (ARRIVES j2)|].
    apply ar_imp_correspondence; [exact (TASK j1 tsk)|].
    apply ar_imp_correspondence; [exact (TASK j2 tsk)|].
    apply ar_forall_nat_correspondence. intros kR kL Hk.
    apply ar_imp_correspondence;
      [exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (IDX j1) Hk) (IDX j2))|].
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
    apply ar_exists_nat_correspondence. intros nR nL Hn.
    exact (SEP tsk j1 j2 _ _ Hn).
  Qed.

  Definition src_job_sep_periodic : Prop :=
    ltac:(body_of (fun s : S.statement_job_sep_periodic => s Task pR Job jtR jaR arrR)).
  Definition tgt_job_sep_periodic : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Periodic_ArrivalSeparation_job_sep_periodic
      Task dT pL Job dJ jtL jaL arrL)).
  Theorem job_sep_periodic_correspondence : PropSPropRel src_job_sep_periodic tgt_job_sep_periodic.
  Proof.
    fpas_prefix.
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (fpas_neq_correspondence Job j1 j2)|].
    apply ar_imp_correspondence; [exact (ARRIVES j1)|].
    apply ar_imp_correspondence; [exact (ARRIVES j2)|].
    apply ar_imp_correspondence; [exact (TASK j1 tsk)|].
    apply ar_imp_correspondence; [exact (TASK j2 tsk)|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
    apply ar_exists_nat_correspondence. intros nR nL Hn.
    exact (SEP tsk j1 j2 _ _ Hn).
  Qed.
End Separation.
