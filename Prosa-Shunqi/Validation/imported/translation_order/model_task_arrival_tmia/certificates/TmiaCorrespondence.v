From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.task.arrival.task_max_inter_arrival.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTmia ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence.

Module I := ImportedTmia.

(** Definition certificates for [model/task/arrival/task_max_inter_arrival.v]:
    for related inputs, each source definition and the compiled Lean
    definition are related.  The class relation has import/export witnesses
    in both directions. *)

(** ** Generic connectives (same proofs as the accepted sporadic certificates) *)

Lemma tm_eq_correspondence (T : Type) (xR xL yR yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hx) Hy).
  - intro Heq. apply strictly_inhabits.
    exact (imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hx
        (sub_imported_eq_trans _ _ _ Heq (sub_imported_eq_sym _ _ Hy)))).
Qed.

Lemma tm_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma tm_neq_correspondence (T : Type) (x y : T) :
  PropSPropRel (x <> y) (I.Ne T x y).
Proof.
  unfold I.Ne, I.Not.
  apply ar_imp_correspondence.
  - exact (tm_eq_correspondence T x x y y (@Lean.eq_refl _ _) (@Lean.eq_refl _ _)).
  - exact tm_false_correspondence.
Qed.

Lemma tm_exists_id_correspondence (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits.
    exists x. exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Section Tmia.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.

  Definition TmClassRel (cR : prosa.model.task.arrival.task_max_inter_arrival.TaskMaxInterArrival Task)
      (cL : I.Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival Task dT) : SProp :=
    forall tsk : Task,
      SubNatRel (@prosa.model.task.arrival.task_max_inter_arrival.task_max_inter_arrival_time Task cR tsk)
        (I.Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival_task_max_inter_arrival_time
          Task dT cL tsk).

  Lemma TaskMaxInterArrival_source_total cR :
    TmClassRel cR (I.Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival_mk Task dT
      (fun tsk => sub_nat_to_imported (cR tsk))).
  Proof. intro tsk. exact (sub_nat_rel_canonical _). Qed.

  Lemma TaskMaxInterArrival_target_total cL :
    TmClassRel (fun tsk => sub_nat_to_rocq
      (I.Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival_task_max_inter_arrival_time
        Task dT cL tsk)) cL.
  Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

  Variable cR : prosa.model.task.arrival.task_max_inter_arrival.TaskMaxInterArrival Task.
  Variable cL : I.Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival Task dT.
  Hypothesis Hc : TmClassRel cR cL.

  Theorem positive_task_max_inter_arrival_time_correspondence (tsk : Task) :
    ArBoolRel (@prosa.model.task.arrival.task_max_inter_arrival.positive_task_max_inter_arrival_time Task cR tsk)
      (I.Prosa_Model_Task_Arrival_Task_max_inter_arrival_positive_task_max_inter_arrival_time Task dT cL tsk).
  Proof. exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hc tsk)). Qed.

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

  Let TASKEQ j tsk := tm_eq_correspondence Task _ _ tsk tsk (Hjt j) (@Lean.eq_refl _ tsk).
  Let ARR j := arrives_in_correspondence_certificate Job arrR arrL j Harr.

  Theorem arr_sep_task_max_inter_arrival_correspondence (tsk : Task) :
    PropSPropRel
      (@prosa.model.task.arrival.task_max_inter_arrival.arr_sep_task_max_inter_arrival
        Task cR Job jtR jaR arrR tsk)
      (I.Prosa_Model_Task_Arrival_Task_max_inter_arrival_arr_sep_task_max_inter_arrival
        Task dT cL Job dJ jtL jaL arrL tsk).
  Proof.
    unfold prosa.model.task.arrival.task_max_inter_arrival.arr_sep_task_max_inter_arrival.
    cbn [I.Prosa_Model_Task_Arrival_Task_max_inter_arrival_arr_sep_task_max_inter_arrival].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (ARR j)|].
    apply ar_imp_correspondence; [exact (TASKEQ j tsk)|].
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O)
         (job_index_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j))|].
    apply tm_exists_id_correspondence => j'.
    apply ar_and_correspondence; [exact (tm_neq_correspondence Job j j')|].
    apply ar_and_correspondence; [exact (ARR j')|].
    apply ar_and_correspondence; [exact (TASKEQ j' tsk)|].
    apply ar_bool_truth_correspondence.
    apply ar_bool_and_related.
    - exact (ar_decide_le_related _ _ _ _ (Hja j') (Hja j)).
    - exact (ar_decide_le_related _ _ _ _ (Hja j)
        (sub_add_correspondence _ _ _ _ (Hja j') (Hc tsk))).
  Qed.

  Theorem valid_task_max_inter_arrival_time_correspondence (tsk : Task) :
    PropSPropRel
      (@prosa.model.task.arrival.task_max_inter_arrival.valid_task_max_inter_arrival_time
        Task cR Job jtR jaR arrR tsk)
      (I.Prosa_Model_Task_Arrival_Task_max_inter_arrival_valid_task_max_inter_arrival_time
        Task dT cL Job dJ jtL jaL arrL tsk).
  Proof.
    unfold prosa.model.task.arrival.task_max_inter_arrival.valid_task_max_inter_arrival_time.
    cbn [I.Prosa_Model_Task_Arrival_Task_max_inter_arrival_valid_task_max_inter_arrival_time].
    apply ar_and_correspondence.
    - exact (ar_bool_truth_correspondence _ _ (positive_task_max_inter_arrival_time_correspondence tsk)).
    - exact (arr_sep_task_max_inter_arrival_correspondence tsk).
  Qed.

  Theorem taskset_respects_task_max_inter_arrival_model_correspondence tsR tsL :
    ArListRel tsR tsL ->
    PropSPropRel
      (@prosa.model.task.arrival.task_max_inter_arrival.taskset_respects_task_max_inter_arrival_model
        Task cR Job jtR jaR arrR tsR)
      (I.Prosa_Model_Task_Arrival_Task_max_inter_arrival_taskset_respects_task_max_inter_arrival_model
        Task dT cL Job dJ jtL jaL arrL tsL).
  Proof.
    intro Hts.
    unfold prosa.model.task.arrival.task_max_inter_arrival.taskset_respects_task_max_inter_arrival_model.
    cbn [I.Prosa_Model_Task_Arrival_Task_max_inter_arrival_taskset_respects_task_max_inter_arrival_model].
    apply ar_forall_identity_correspondence => tsk.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    exact (valid_task_max_inter_arrival_time_correspondence tsk).
  Qed.
End Tmia.
