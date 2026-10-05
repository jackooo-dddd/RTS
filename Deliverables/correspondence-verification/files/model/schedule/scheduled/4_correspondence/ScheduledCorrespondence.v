From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import model.schedule.scheduled.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedScheduledFull.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ReadyArrivalBaseAdapter
  ReadyArrivalOperations ReadyArrivalCorrespondence
  ScheduledStateBaseAdapter ScheduledStateOperations.

(** Recover the imported Boolean value from its certified truth observation.
    This is a two-constructor case analysis, not an extra semantic premise. *)
Lemma scheduled_bool_of_truth (bR : bool)
    (bL : ImportedScheduledFull.Bool) :
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedScheduledFull.Bool_true) ->
  ArBoolRel bR bL.
Proof.
  intro Htruth. destruct bR, bL; cbn [ArBoolRel ar_bool_to_imported].
  - exact (ar_false_elim _ (ar_false_ne_true
      (prop_to_sprop _ _ Htruth (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - have Hfalse := sprop_to_prop _ _ Htruth (@Lean.eq_refl _ _).
    discriminate Hfalse.
Qed.

Definition scheduled_option_to_imported {T : Type} (o : option T) :
    ImportedScheduledFull.Option T :=
  match o with
  | None => ImportedScheduledFull.Option_none T
  | Some x => ImportedScheduledFull.Option_some T x
  end.

Definition ScheduledOptionRel {T : Type} (oR : option T)
    (oL : ImportedScheduledFull.Option T) : SProp :=
  Lean.eq (scheduled_option_to_imported oR) oL.

Lemma scheduled_ohead_correspondence {T : Type}
    (xsR : seq T) (xsL : ImportedScheduledFull.List T) :
  ArListRel xsR xsL ->
  ScheduledOptionRel (ohead xsR)
    (ImportedScheduledFull.List_head__q T xsL).
Proof.
  intro Hxs. unfold ScheduledOptionRel, ArListRel in *.
  refine (sub_imported_eq_trans _ _ _ _
    (sub_imported_eq_congr (ImportedScheduledFull.List_head__q T)
      _ _ Hxs)).
  destruct xsR as [|x xs]; cbn [ohead ar_list_to_imported
    scheduled_option_to_imported
    ImportedScheduledFull.List_head__q
    ImportedScheduledFull.List_getLast__q_match_1];
    exact (@Lean.eq_refl _ _).
Qed.

Lemma scheduled_nil_eq_isEmpty_correspondence {T : eqType}
    (xsR : seq T) (xsL : ImportedScheduledFull.List T) :
  ArListRel xsR xsL ->
  ArBoolRel (xsR == [::])
    (ImportedScheduledFull.List_isEmpty T xsL).
Proof.
  intro Hxs. unfold ArBoolRel, ArListRel in *.
  destruct xsR as [|x xs]; cbn [eqseq ar_bool_to_imported
    ar_list_to_imported].
  - exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _
        (ImportedScheduledFull.Prosa_Validation_ScheduledInterface_production_isEmpty_nil T))
      (sub_imported_eq_congr (ImportedScheduledFull.List_isEmpty T)
        _ _ Hxs)).
  - exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _
        (ImportedScheduledFull.Prosa_Validation_ScheduledInterface_production_isEmpty_cons
          T x (ar_list_to_imported xs)))
      (sub_imported_eq_congr (ImportedScheduledFull.List_isEmpty T)
        _ _ Hxs)).
Qed.

Section ScheduledCorrespondence.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Context (PStateL : ImportedScheduledFull.Prosa_Behavior_Schedule_ProcessorState
    Job (ar_decidable_eq Job)).
  Context (R : EdfProcessorRel Job PStateR PStateL).
  Context (schedR : @prosa.behavior.schedule.schedule Job PStateR).
  Context (schedL : ImportedScheduledFull.Prosa_Behavior_Schedule_schedule
    Job (ar_decidable_eq Job) PStateL).
  Context (Hsched : EdfScheduleRel Job PStateR PStateL R schedR schedL).
  Context (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job).
  Context (arrL : ImportedScheduledFull.Prosa_Behavior_Arrival_sequence_arrival_sequence
    Job (ar_decidable_eq Job)).
  Context (Harr : ArArrivalSequenceRel Job arrR arrL).

  Lemma scheduled_at_bool_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel (@prosa.behavior.service.scheduled_at
      Job PStateR schedR j tR)
      (ImportedScheduledFull.Prosa_Behavior_Service_scheduled_at
        Job (ar_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. apply scheduled_bool_of_truth.
    exact (edf_scheduled_at_truth Job PStateR PStateL R
      schedR schedL j tR tL Hsched Ht).
  Qed.

  Theorem scheduled_jobs_at_correspondence (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArListRel
      (@prosa.model.schedule.scheduled.scheduled_jobs_at
        Job PStateR arrR schedR tR)
      (ImportedScheduledFull.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at
        Job (ar_decidable_eq Job) PStateL arrL schedL tL).
  Proof.
    intro Ht. unfold prosa.model.schedule.scheduled.scheduled_jobs_at.
    cbn [ImportedScheduledFull.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at].
    apply ar_filter_related.
    - intro j. exact (scheduled_at_bool_related j tR tL Ht).
    - exact (arrivals_up_to_correspondence_certificate
        Job arrR arrL Harr tR tL Ht).
  Qed.

  Theorem scheduled_job_at_correspondence (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ScheduledOptionRel
      (@prosa.model.schedule.scheduled.scheduled_job_at
        Job PStateR arrR schedR tR)
      (ImportedScheduledFull.Prosa_Model_Schedule_Scheduled_scheduled_job_at
        Job (ar_decidable_eq Job) PStateL arrL schedL tL).
  Proof.
    intro Ht. unfold prosa.model.schedule.scheduled.scheduled_job_at.
    cbn [ImportedScheduledFull.Prosa_Model_Schedule_Scheduled_scheduled_job_at].
    apply scheduled_ohead_correspondence.
    exact (scheduled_jobs_at_correspondence tR tL Ht).
  Qed.

  Theorem is_idle_correspondence (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel
      (@prosa.model.schedule.scheduled.is_idle
        Job PStateR arrR schedR tR)
      (ImportedScheduledFull.Prosa_Model_Schedule_Scheduled_is_idle
        Job (ar_decidable_eq Job) PStateL arrL schedL tL).
  Proof.
    intro Ht. unfold prosa.model.schedule.scheduled.is_idle.
    cbn [ImportedScheduledFull.Prosa_Model_Schedule_Scheduled_is_idle].
    apply scheduled_nil_eq_isEmpty_correspondence.
    exact (scheduled_jobs_at_correspondence tR tL Ht).
  Qed.
End ScheduledCorrespondence.
