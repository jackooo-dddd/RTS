From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.processor.overheads.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedScheduleChange.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ScheduleChangeBaseAdapter.

(** The approved Overheads state and selected DecidableEq are replayed against
    this exact imported artifact. No field or law is replaced by a premise. *)
Definition ScSourceState (Job : eqType) : Type :=
  @prosa.model.processor.overheads.proc_state Job.

Definition ScTargetState (Job : Type) : Type :=
  ImportedScheduleChange.Prosa_Model_Processor_Overheads_proc_state Job.

Definition sc_option_to_imported {T : Type} (x : option T) :
    ImportedScheduleChange.Option T :=
  match x with
  | None => ImportedScheduleChange.Option_none T
  | Some j => ImportedScheduleChange.Option_some T j
  end.

Definition ScOptionRel {T : Type} (xR : option T)
    (xL : ImportedScheduleChange.Option T) : SProp :=
  Lean.eq (sc_option_to_imported xR) xL.

Definition sc_state_to_imported (Job : eqType) (s : ScSourceState Job) :
    ScTargetState Job :=
  match s with
  | prosa.model.processor.overheads.Idle =>
      ImportedScheduleChange.Prosa_Model_Processor_Overheads_proc_state_Idle Job
  | prosa.model.processor.overheads.ContextSwitch j1 j2 =>
      ImportedScheduleChange.Prosa_Model_Processor_Overheads_proc_state_ContextSwitch
        Job (sc_option_to_imported j1) (sc_option_to_imported j2)
  | prosa.model.processor.overheads.Dispatch j =>
      ImportedScheduleChange.Prosa_Model_Processor_Overheads_proc_state_Dispatch
        Job (sc_option_to_imported j)
  | prosa.model.processor.overheads.CacheRelatedPreemptionDelay j =>
      ImportedScheduleChange.Prosa_Model_Processor_Overheads_proc_state_CacheRelatedPreemptionDelay
        Job j
  | prosa.model.processor.overheads.Progress j =>
      ImportedScheduleChange.Prosa_Model_Processor_Overheads_proc_state_Progress Job j
  end.

Definition ScStateRel (Job : eqType) (sR : ScSourceState Job)
    (sL : ScTargetState Job) : SProp :=
  Lean.eq (sc_state_to_imported Job sR) sL.

Definition ScSourceSchedule (Job : eqType) : Type :=
  @prosa.behavior.schedule.schedule Job
    (@prosa.model.processor.overheads.processor_state Job).

Definition ScTargetSchedule (Job : eqType) : Type :=
  Lean.Nat -> ScTargetState Job.

Definition ScScheduleRel (Job : eqType)
    (schedR : ScSourceSchedule Job)
    (schedL : ScTargetSchedule Job) : SProp :=
  forall tR tL, SubNatRel tR tL ->
    ScStateRel Job (schedR tR) (schedL tL).

Definition sc_schedule_to_imported (Job : eqType)
    (schedR : ScSourceSchedule Job) : ScTargetSchedule Job :=
  fun tL => sc_state_to_imported Job (schedR (sub_nat_to_rocq tL)).

Lemma sc_schedule_canonical (Job : eqType)
    (schedR : ScSourceSchedule Job) :
  ScScheduleRel Job schedR (sc_schedule_to_imported Job schedR).
Proof.
  unfold ScScheduleRel, ScStateRel, sc_schedule_to_imported.
  move=> tR tL Ht.
  have Ht' : Logic.eq (sub_nat_to_rocq tL) tR :=
    Logic.eq_trans
      (f_equal sub_nat_to_rocq
        (Logic.eq_sym (imported_eq_to_coq_eq _ _ Ht)))
      (sub_nat_rocq_roundtrip tR).
  rewrite Ht'. exact (@Lean.eq_refl _ _).
Qed.

Lemma sc_scheduled_job_correspondence (Job : eqType)
    (schedR : ScSourceSchedule Job) (schedL : ScTargetSchedule Job)
    (tR : nat) (tL : Lean.Nat) :
  ScScheduleRel Job schedR schedL -> SubNatRel tR tL ->
  ScOptionRel
    (@prosa.model.processor.overheads.scheduled_job Job schedR tR)
    (ImportedScheduleChange.Prosa_Model_Processor_Overheads_scheduled_job
      Job (sc_decidable_eq Job) schedL tL).
Proof.
  intros Hsched Ht.
  unfold prosa.model.processor.overheads.scheduled_job,
    ImportedScheduleChange.Prosa_Model_Processor_Overheads_scheduled_job.
  have Hstate : Logic.eq (sc_state_to_imported Job (schedR tR))
      (schedL tL) := imported_eq_to_coq_eq _ _ (Hsched tR tL Ht).
  rewrite <- Hstate.
  destruct (schedR tR) as [|a b|a|a|a]; cbn;
    exact (@Lean.eq_refl _ _).
Qed.
