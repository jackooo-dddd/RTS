(* Helper copy of the accepted model/processor/overheads certificate (Validation/imported/translation_order/overheads/
   certificates/OverheadsCorrespondence.v), re-bound to this export; its Print Assumptions commands and its
   total_time_in_* interval-count section are dropped (those definitions are not part of this export), and so is its
   ConcreteOverheads section (processor-state instance fields; the processor-state instance of this export is a
   universe-specialised copy, and no certificate here uses that section)
   (the assumptions of this file's certificates are audited by this file's audit module). *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.overheads.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaOvhFpFullyNonpreemptive.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  OverheadsBaseAdapter OverheadsNatBoolOperations
  OverheadsIntervalOperations.

Definition OvhSource (Job : eqType) : Type :=
  @prosa.model.processor.overheads.proc_state Job.

Definition OvhTarget (Job : Type) : Type :=
  ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_proc_state Job.

Definition ovh_option_to_imported {T : Type} (x : option T) :
    ImportedRtaOvhFpFullyNonpreemptive.Option T :=
  match x with
  | None => ImportedRtaOvhFpFullyNonpreemptive.Option_none T
  | Some j => ImportedRtaOvhFpFullyNonpreemptive.Option_some T j
  end.

Definition ovh_option_to_source {T : Type} (x : ImportedRtaOvhFpFullyNonpreemptive.Option T) :
    option T :=
  match x with
  | ImportedRtaOvhFpFullyNonpreemptive.Option_none => None
  | ImportedRtaOvhFpFullyNonpreemptive.Option_some j => Some j
  end.

Definition OvhOptionRel {T : Type} (xR : option T)
    (xL : ImportedRtaOvhFpFullyNonpreemptive.Option T) : SProp :=
  Lean.eq (ovh_option_to_imported xR) xL.

Lemma ovh_option_source_roundtrip {T : Type} (x : option T) :
  Logic.eq (ovh_option_to_source (ovh_option_to_imported x)) x.
Proof. destruct x; reflexivity. Qed.

Lemma ovh_option_target_roundtrip {T : Type} (x : ImportedRtaOvhFpFullyNonpreemptive.Option T) :
  OvhOptionRel (ovh_option_to_source x) x.
Proof. destruct x; cbn; exact (@Lean.eq_refl _ _). Qed.

Definition ovh_state_to_imported (Job : eqType) (s : OvhSource Job) :
    OvhTarget Job :=
  match s with
  | prosa.model.processor.overheads.Idle =>
      ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_proc_state_Idle Job
  | prosa.model.processor.overheads.ContextSwitch j1 j2 =>
      ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_proc_state_ContextSwitch
        Job (ovh_option_to_imported j1) (ovh_option_to_imported j2)
  | prosa.model.processor.overheads.Dispatch j =>
      ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_proc_state_Dispatch
        Job (ovh_option_to_imported j)
  | prosa.model.processor.overheads.CacheRelatedPreemptionDelay j =>
      ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_proc_state_CacheRelatedPreemptionDelay
        Job j
  | prosa.model.processor.overheads.Progress j =>
      ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_proc_state_Progress Job j
  end.

Definition ovh_state_to_source (Job : eqType) (s : OvhTarget Job) :
    OvhSource Job :=
  match s with
  | ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_proc_state_Idle =>
      @prosa.model.processor.overheads.Idle Job
  | ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_proc_state_ContextSwitch j1 j2 =>
      @prosa.model.processor.overheads.ContextSwitch Job
        (ovh_option_to_source j1) (ovh_option_to_source j2)
  | ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_proc_state_Dispatch j =>
      @prosa.model.processor.overheads.Dispatch Job (ovh_option_to_source j)
  | ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_proc_state_CacheRelatedPreemptionDelay j =>
      @prosa.model.processor.overheads.CacheRelatedPreemptionDelay Job j
  | ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_proc_state_Progress j =>
      @prosa.model.processor.overheads.Progress Job j
  end.

Definition OvhRel (Job : eqType) (sR : OvhSource Job)
    (sL : OvhTarget Job) : SProp :=
  Lean.eq (ovh_state_to_imported Job sR) sL.

Lemma ovh_state_source_roundtrip (Job : eqType) (s : OvhSource Job) :
  Logic.eq (ovh_state_to_source Job (ovh_state_to_imported Job s)) s.
Proof.
  destruct s as [|a b|a|a|a]; cbn; try reflexivity.
  - destruct a, b; reflexivity.
  - destruct a; reflexivity.
Qed.

Lemma ovh_state_target_roundtrip (Job : eqType) (s : OvhTarget Job) :
  OvhRel Job (ovh_state_to_source Job s) s.
Proof.
  destruct s as [|a b|a|a|a]; cbn; try exact (@Lean.eq_refl _ _).
  - destruct a, b; exact (@Lean.eq_refl _ _).
  - destruct a; exact (@Lean.eq_refl _ _).
Qed.

Definition ovh_target_false_elim (Q : SProp)
    (H : ImportedRtaOvhFpFullyNonpreemptive.False) : Q := match H return Q with end.

Lemma ovh_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedRtaOvhFpFullyNonpreemptive.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  OvhBoolRel bR (ImportedRtaOvhFpFullyNonpreemptive.Decidable_decide Q d).
Proof.
  intro Hrel. unfold OvhBoolRel.
  destruct d as [Hfalse | Htrue]; destruct bR; cbn.
  - exact (ovh_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (ovh_target_false_elim _ (ovh_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Lemma ovh_job_equality_truth (Job : eqType) (x y : Job) :
  PropSPropRel (is_true (x == y)) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - move/eqP=> H. exact (coq_eq_to_imported_eq x y H).
  - intro H. apply strictly_inhabits. apply/eqP.
    exact (imported_eq_to_coq_eq x y H).
Qed.

Lemma ovh_bool_false_correspondence (bR : bool)
    (bL : ImportedRtaOvhFpFullyNonpreemptive.Bool) :
  OvhBoolRel bR bL ->
  PropSPropRel (is_true (~~ bR))
    (Lean.eq bL ImportedRtaOvhFpFullyNonpreemptive.Bool_false).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Hfalse. destruct bR, bL; cbn in *.
    + discriminate Hfalse.
    + discriminate Hfalse.
    + exact (@Lean.eq_refl _ _).
    + exact (ovh_false_elim _ (ovh_false_ne_true Hb)).
  - intro Hfalse. destruct bR, bL; cbn in *.
    + exact (ovh_false_elim _ (ovh_false_ne_true
        (sub_imported_eq_sym _ _ Hb))).
    + exact (ovh_false_elim _ (ovh_false_ne_true
        (sub_imported_eq_sym _ _ Hfalse))).
    + exact (strictly_inhabits (Logic.eq_refl true)).
    + exact (ovh_false_elim _ (ovh_false_ne_true Hb)).
Qed.

Section OverheadsOperations.
  Context (Job : eqType).

  Lemma ovh_scheduled_on_correspondence (j : Job) (s : OvhSource Job) :
    OvhBoolRel
      (@prosa.model.processor.overheads.overheads_scheduled_on Job j s tt)
      (ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_overheads_scheduled_on
        Job (ovh_decidable_eq Job) j (ovh_state_to_imported Job s)
        ImportedRtaOvhFpFullyNonpreemptive.Unit_unit).
  Proof.
    destruct s as [|a b|a|a|a]; cbn;
      try exact (@Lean.eq_refl _ _).
    - destruct b as [b|]; cbn;
        try exact (@Lean.eq_refl _ _).
      apply ovh_decide_bool_correspondence.
      exact (ovh_job_equality_truth Job j b).
    - destruct a as [a|]; cbn;
        try exact (@Lean.eq_refl _ _).
      apply ovh_decide_bool_correspondence.
      exact (ovh_job_equality_truth Job j a).
    - apply ovh_decide_bool_correspondence.
      exact (ovh_job_equality_truth Job j a).
    - apply ovh_decide_bool_correspondence.
      exact (ovh_job_equality_truth Job j a).
  Qed.

  Lemma ovh_supply_on_correspondence (s : OvhSource Job) :
    SubNatRel
      (@prosa.model.processor.overheads.overheads_supply_on Job s tt)
      (ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_overheads_supply_on
        Job (ovh_decidable_eq Job) (ovh_state_to_imported Job s)
        ImportedRtaOvhFpFullyNonpreemptive.Unit_unit).
  Proof.
    destruct s; cbn; exact (sub_nat_rel_canonical _).
  Qed.

  Lemma ovh_service_on_correspondence (j : Job) (s : OvhSource Job) :
    SubNatRel
      (@prosa.model.processor.overheads.overheads_service_on Job j s tt)
      (ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_overheads_service_on
        Job (ovh_decidable_eq Job) j (ovh_state_to_imported Job s)
        ImportedRtaOvhFpFullyNonpreemptive.Unit_unit).
  Proof.
    destruct s as [|a b|a|a|a]; cbn;
      try exact (sub_nat_rel_canonical O).
    have Hdec := ovh_decide_bool_correspondence
      (a == j) (Lean.eq a j) (ovh_decidable_eq Job a j)
      (ovh_job_equality_truth Job a j).
    unfold OvhBoolRel in Hdec. destruct Hdec.
    destruct (a == j); cbn; exact (sub_nat_rel_canonical _).
  Qed.
End OverheadsOperations.

Section ScheduleObservations.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.overheads.processor_state Job.
  Let stateL :=
    ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_processor_state
      Job (ovh_decidable_eq Job).

  Definition OvhScheduleRel
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      OvhRel Job (schedR tR) (schedL tL).

  Lemma ovh_scheduled_job_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job)
      (tR : nat) (tL : ImportedRtaOvhFpFullyNonpreemptive.Prosa_Behavior_Time_instant) :
    OvhScheduleRel schedR schedL -> SubNatRel tR tL ->
    OvhOptionRel
      (@prosa.model.processor.overheads.scheduled_job Job schedR tR)
      (ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_scheduled_job
        Job (ovh_decidable_eq Job) schedL tL).
  Proof.
    intros Hsched Ht.
    unfold prosa.model.processor.overheads.scheduled_job,
      ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_scheduled_job.
    have Hstate : Logic.eq (ovh_state_to_imported Job (schedR tR))
        (schedL tL) := imported_eq_to_coq_eq _ _ (Hsched tR tL Ht).
    rewrite <- Hstate.
    destruct (schedR tR) as [|a b|a|a|a]; cbn;
      exact (@Lean.eq_refl _ _).
  Qed.

  Lemma ovh_is_progress_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job)
      (tR : nat) (tL : ImportedRtaOvhFpFullyNonpreemptive.Prosa_Behavior_Time_instant) :
    OvhScheduleRel schedR schedL -> SubNatRel tR tL ->
    OvhBoolRel
      (@prosa.model.processor.overheads.is_progress Job schedR tR)
      (ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_is_progress
        Job (ovh_decidable_eq Job) schedL tL).
  Proof.
    intros Hsched Ht.
    unfold prosa.model.processor.overheads.is_progress,
      ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_is_progress.
    have Hstate : Logic.eq (ovh_state_to_imported Job (schedR tR))
        (schedL tL) := imported_eq_to_coq_eq _ _ (Hsched tR tL Ht).
    rewrite <- Hstate.
    destruct (schedR tR) as [|a b|a|a|a]; cbn;
      exact (@Lean.eq_refl _ _).
  Qed.

  Lemma ovh_is_context_switch_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job)
      (tR : nat) (tL : ImportedRtaOvhFpFullyNonpreemptive.Prosa_Behavior_Time_instant) :
    OvhScheduleRel schedR schedL -> SubNatRel tR tL ->
    OvhBoolRel
      (@prosa.model.processor.overheads.is_context_switch Job schedR tR)
      (ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_is_context_switch
        Job (ovh_decidable_eq Job) schedL tL).
  Proof.
    intros Hsched Ht.
    unfold prosa.model.processor.overheads.is_context_switch,
      ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_is_context_switch.
    have Hstate : Logic.eq (ovh_state_to_imported Job (schedR tR))
        (schedL tL) := imported_eq_to_coq_eq _ _ (Hsched tR tL Ht).
    rewrite <- Hstate.
    destruct (schedR tR) as [|a b|a|a|a]; cbn;
      exact (@Lean.eq_refl _ _).
  Qed.

  Lemma ovh_is_dispatch_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job)
      (tR : nat) (tL : ImportedRtaOvhFpFullyNonpreemptive.Prosa_Behavior_Time_instant) :
    OvhScheduleRel schedR schedL -> SubNatRel tR tL ->
    OvhBoolRel
      (@prosa.model.processor.overheads.is_dispatch Job schedR tR)
      (ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_is_dispatch
        Job (ovh_decidable_eq Job) schedL tL).
  Proof.
    intros Hsched Ht.
    unfold prosa.model.processor.overheads.is_dispatch,
      ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_is_dispatch.
    have Hstate : Logic.eq (ovh_state_to_imported Job (schedR tR))
        (schedL tL) := imported_eq_to_coq_eq _ _ (Hsched tR tL Ht).
    rewrite <- Hstate.
    destruct (schedR tR) as [|a b|a|a|a]; cbn;
      exact (@Lean.eq_refl _ _).
  Qed.

  Lemma ovh_is_CRPD_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job)
      (tR : nat) (tL : ImportedRtaOvhFpFullyNonpreemptive.Prosa_Behavior_Time_instant) :
    OvhScheduleRel schedR schedL -> SubNatRel tR tL ->
    OvhBoolRel
      (@prosa.model.processor.overheads.is_CRPD Job schedR tR)
      (ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_is_CRPD
        Job (ovh_decidable_eq Job) schedL tL).
  Proof.
    intros Hsched Ht.
    unfold prosa.model.processor.overheads.is_CRPD,
      ImportedRtaOvhFpFullyNonpreemptive.Prosa_Model_Processor_Overheads_is_CRPD.
    have Hstate : Logic.eq (ovh_state_to_imported Job (schedR tR))
        (schedL tL) := imported_eq_to_coq_eq _ _ (Hsched tR tL Ht).
    rewrite <- Hstate.
    destruct (schedR tR) as [|a b|a|a|a]; cbn;
      exact (@Lean.eq_refl _ _).
  Qed.
End ScheduleObservations.

Lemma ovh_bool_to_nat_related (bR : bool) (bL : ImportedRtaOvhFpFullyNonpreemptive.Bool) :
  OvhBoolRel bR bL ->
  SubNatRel (nat_of_bool bR) (ImportedRtaOvhFpFullyNonpreemptive.Bool_toNat bL).
Proof.
  intro Hb.
  have H : Logic.eq (ovh_bool_to_imported bR) bL :=
    imported_eq_to_coq_eq _ _ Hb.
  rewrite <- H. destruct bR; exact (sub_nat_rel_canonical _).
Qed.


