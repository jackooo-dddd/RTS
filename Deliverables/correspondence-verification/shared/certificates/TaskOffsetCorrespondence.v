From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import TaskOffsetSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskOffset ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence.

Module I := ImportedTaskOffset.
Module S := TaskOffsetSemanticSource.TaskOffsetSemanticSource.

(** Definition certificates for [model/task/offset.v].

    Source side: the extracted byte-identical class and definition blocks;
    target side: the compiled Lean class and definitions.  The class is
    related pointwise by [SubNatRel] ([OffRel]) with two-way totals.  Inputs:
    [job_task] by [Lean.eq], [job_arrival] by [ArJobArrivalRel], arrival
    sequences by [ArArrivalSequenceRel], task sets by [ArListRel]; jobs and
    tasks are identity carriers.  Membership and [max0] are closed by the
    accepted arrival-sequence and preemption-parameter certificates. *)

Lemma off_eq_correspondence (T : Type) (xR xL yR yL : T) :
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

Lemma off_exists_identity (T : Type) (P : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (P x) (PL x)) ->
  PropSPropRel (exists x, P x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Section Offset.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.

  Definition OffRel (oR : S.TaskOffset Task)
      (oL : I.Prosa_Model_Task_Offset_TaskOffset Task dT) : SProp :=
    forall tsk : Task, SubNatRel (@S.task_offset Task oR tsk)
      (I.Prosa_Model_Task_Offset_TaskOffset_task_offset Task dT oL tsk).

  Lemma TaskOffset_source_total (oR : S.TaskOffset Task) :
    OffRel oR (I.Prosa_Model_Task_Offset_TaskOffset_mk Task dT
      (fun tsk => sub_nat_to_imported (oR tsk))).
  Proof. intro tsk. exact (@Lean.eq_refl _ _). Qed.

  Lemma TaskOffset_target_total (oL : I.Prosa_Model_Task_Offset_TaskOffset Task dT) :
    OffRel ((fun tsk => sub_nat_to_rocq
      (I.Prosa_Model_Task_Offset_TaskOffset_task_offset Task dT oL tsk)) : S.TaskOffset Task) oL.
  Proof. intro tsk. exact (sub_nat_imported_roundtrip _). Qed.

  Variable oR : S.TaskOffset Task.
  Variable oL : I.Prosa_Model_Task_Offset_TaskOffset Task dT.
  Hypothesis Hoff : OffRel oR oL.

  Section Jobs.
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

    Theorem no_jobs_before_offset_correspondence (tsk : Task) :
      PropSPropRel (@S.no_jobs_before_offset Task oR Job jtR jaR tsk)
        (I.Prosa_Model_Task_Offset_no_jobs_before_offset Task dT oL Job dJ jtL jaL tsk).
    Proof.
      unfold S.no_jobs_before_offset.
      cbn [I.Prosa_Model_Task_Offset_no_jobs_before_offset].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence;
        [exact (off_eq_correspondence Task _ _ tsk tsk (Hjt j) (@Lean.eq_refl _ _))|].
      exact (sub_nat_le_correspondence _ _ _ _ (Hoff tsk) (Hja j)).
    Qed.

    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Theorem job_released_at_offset_correspondence (tsk : Task) :
      PropSPropRel (@S.job_released_at_offset Task oR Job jtR jaR arrR tsk)
        (I.Prosa_Model_Task_Offset_job_released_at_offset Task dT oL Job dJ jtL jaL arrL tsk).
    Proof.
      unfold S.job_released_at_offset.
      cbn [I.Prosa_Model_Task_Offset_job_released_at_offset].
      apply off_exists_identity. intro j.
      apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      apply ar_and_correspondence;
        [exact (off_eq_correspondence Task _ _ tsk tsk (Hjt j) (@Lean.eq_refl _ _))|].
      exact (sub_nat_eq_correspondence _ _ _ _ (Hja j) (Hoff tsk)).
    Qed.

    Theorem valid_offset_correspondence (tsk : Task) :
      PropSPropRel (@S.valid_offset Task oR Job jtR jaR arrR tsk)
        (I.Prosa_Model_Task_Offset_valid_offset Task dT oL Job dJ jtL jaL arrL tsk).
    Proof.
      unfold S.valid_offset.
      cbn [I.Prosa_Model_Task_Offset_valid_offset].
      apply ar_and_correspondence.
      - exact (no_jobs_before_offset_correspondence tsk).
      - exact (job_released_at_offset_correspondence tsk).
    Qed.

    Variable tsR : seq Task.
    Variable tsL : I.List Task.
    Hypothesis Hts : ArListRel tsR tsL.

    Theorem valid_offsets_correspondence :
      PropSPropRel (@S.valid_offsets Task oR Job jtR jaR arrR tsR)
        (I.Prosa_Model_Task_Offset_valid_offsets Task dT oL Job dJ jtL jaL arrL tsL).
    Proof.
      unfold S.valid_offsets.
      cbn [I.Prosa_Model_Task_Offset_valid_offsets].
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
      exact (valid_offset_correspondence tsk).
    Qed.
  End Jobs.

  Lemma off_map_canonical (xs : seq Task) :
    SvcNatListRel (map (@S.task_offset Task oR) xs)
      (I.List_map_inst2 Task Lean.Nat
        (I.Prosa_Model_Task_Offset_TaskOffset_task_offset Task dT oL) (ar_list_to_imported xs)).
  Proof.
    induction xs as [|x xs IH].
    - exact (@Lean.eq_refl _ _).
    - cbn [map ar_list_to_imported].
      exact (sub_imported_eq_congr2 (I.List_cons_inst1 Lean.Nat) _ _ _ _ (Hoff x) IH).
  Qed.

  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.

  Theorem task_offsets_correspondence :
    SvcNatListRel (@S.task_offsets Task oR tsR)
      (I.Prosa_Model_Task_Offset_task_offsets Task dT oL tsL).
  Proof.
    unfold S.task_offsets.
    cbn [I.Prosa_Model_Task_Offset_task_offsets].
    exact (sub_imported_eq_trans _ _ _ (off_map_canonical tsR)
      (sub_imported_eq_congr (I.List_map_inst2 Task Lean.Nat
        (I.Prosa_Model_Task_Offset_TaskOffset_task_offset Task dT oL)) _ _ Hts)).
  Qed.

  Theorem max_task_offset_correspondence :
    SubNatRel (@S.max_task_offset Task oR tsR)
      (I.Prosa_Model_Task_Offset_max_task_offset Task dT oL tsL).
  Proof.
    unfold S.max_task_offset.
    cbn [I.Prosa_Model_Task_Offset_max_task_offset].
    exact (pp_max0_related _ _ task_offsets_correspondence).
  Qed.
End Offset.
