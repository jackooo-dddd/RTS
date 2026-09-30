From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import PeriodicSemanticSource.
From prosa Require Import model.task.arrivals.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsHyperperiod ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence.

Module I := ImportedFactsHyperperiod.
Module S := PeriodicSemanticSource.PeriodicSemanticSource.

(** Definition certificates for [model/task/arrival/periodic.v].

    Source side: the extracted byte-identical class and definition blocks;
    target side: the compiled Lean class and definitions.  The class is
    related pointwise by [SubNatRel] ([PerRel]) with two-way totals.
    Inputs: [job_task] by [Lean.eq], [job_arrival] by [ArJobArrivalRel],
    arrival sequences by [ArArrivalSequenceRel], task sets by [ArListRel];
    jobs and tasks are identity carriers.  [job_index] is closed by the
    accepted [ArrivalsCorrespondence], membership by the accepted
    arrival-sequence certificates. *)

Lemma per_eq_correspondence (T : Type) (xR xL yR yL : T) :
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

Lemma per_exists_identity (T : Type) (P : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (P x) (PL x)) ->
  PropSPropRel (exists x, P x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Section Periodic.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.

  Definition PerRel (pR : S.PeriodicModel Task)
      (pL : I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task dT) : SProp :=
    forall tsk : Task, SubNatRel (@S.task_period Task pR tsk)
      (I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task dT pL tsk).

  Lemma PeriodicModel_source_total (pR : S.PeriodicModel Task) :
    PerRel pR (I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel_mk Task dT
      (fun tsk => sub_nat_to_imported (pR tsk))).
  Proof. intro tsk. exact (@Lean.eq_refl _ _). Qed.

  Lemma PeriodicModel_target_total (pL : I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task dT) :
    PerRel ((fun tsk => sub_nat_to_rocq
      (I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task dT pL tsk)) : S.PeriodicModel Task) pL.
  Proof. intro tsk. exact (sub_nat_imported_roundtrip _). Qed.

  Variable pR : S.PeriodicModel Task.
  Variable pL : I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task dT.
  Hypothesis Hp : PerRel pR pL.

  Theorem valid_period_correspondence (tsk : Task) :
    ArBoolRel (@S.valid_period Task pR tsk)
      (I.Prosa_Model_Task_Arrival_Periodic_valid_period Task dT pL tsk).
  Proof.
    unfold S.valid_period.
    cbn [I.Prosa_Model_Task_Arrival_Periodic_valid_period].
    exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hp tsk)).
  Qed.

  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.

  Theorem valid_periods_correspondence :
    PropSPropRel (@S.valid_periods Task pR tsR)
      (I.Prosa_Model_Task_Arrival_Periodic_valid_periods Task dT pL tsL).
  Proof.
    unfold S.valid_periods.
    cbn [I.Prosa_Model_Task_Arrival_Periodic_valid_periods].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    exact (ar_bool_truth_correspondence _ _ (valid_period_correspondence tsk)).
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

  Let IDX (j : Job) := job_index_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j.

  Theorem respects_periodic_task_model_correspondence (tsk : Task) :
    PropSPropRel (@S.respects_periodic_task_model Task pR Job jtR jaR arrR tsk)
      (I.Prosa_Model_Task_Arrival_Periodic_respects_periodic_task_model Task dT pL Job dJ jtL jaL arrL tsk).
  Proof.
    unfold S.respects_periodic_task_model.
    cbn [I.Prosa_Model_Task_Arrival_Periodic_respects_periodic_task_model].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (IDX j))|].
    apply ar_imp_correspondence;
      [exact (per_eq_correspondence Task _ _ tsk tsk (Hjt j) (@Lean.eq_refl _ _))|].
    apply per_exists_identity. intro j'.
    apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j' Harr)|].
    apply ar_and_correspondence;
      [exact (sub_nat_eq_correspondence _ _ _ _ (IDX j')
        (ari_nat_sub_related _ _ 1 _ (IDX j) (@Lean.eq_refl _ _)))|].
    apply ar_and_correspondence;
      [exact (per_eq_correspondence Task _ _ tsk tsk (Hjt j') (@Lean.eq_refl _ _))|].
    exact (sub_nat_eq_correspondence _ _ _ _ (Hja j)
      (sub_add_correspondence _ _ _ _ (Hja j') (Hp tsk))).
  Qed.

  Theorem taskset_respects_periodic_task_model_correspondence :
    PropSPropRel (@S.taskset_respects_periodic_task_model Task pR Job jtR jaR arrR tsR)
      (I.Prosa_Model_Task_Arrival_Periodic_taskset_respects_periodic_task_model Task dT pL Job dJ jtL jaL arrL tsL).
  Proof.
    unfold S.taskset_respects_periodic_task_model.
    cbn [I.Prosa_Model_Task_Arrival_Periodic_taskset_respects_periodic_task_model].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    exact (respects_periodic_task_model_correspondence tsk).
  Qed.
End Periodic.
