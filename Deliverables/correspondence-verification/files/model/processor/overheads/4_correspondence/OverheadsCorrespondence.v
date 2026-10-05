From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.overheads.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedOverheads.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  OverheadsBaseAdapter OverheadsNatBoolOperations
  OverheadsIntervalOperations.

Definition OvhSource (Job : eqType) : Type :=
  @prosa.model.processor.overheads.proc_state Job.

Definition OvhTarget (Job : Type) : Type :=
  ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state Job.

Definition ovh_option_to_imported {T : Type} (x : option T) :
    ImportedOverheads.Option T :=
  match x with
  | None => ImportedOverheads.Option_none T
  | Some j => ImportedOverheads.Option_some T j
  end.

Definition ovh_option_to_source {T : Type} (x : ImportedOverheads.Option T) :
    option T :=
  match x with
  | ImportedOverheads.Option_none => None
  | ImportedOverheads.Option_some j => Some j
  end.

Definition OvhOptionRel {T : Type} (xR : option T)
    (xL : ImportedOverheads.Option T) : SProp :=
  Lean.eq (ovh_option_to_imported xR) xL.

Lemma ovh_option_source_roundtrip {T : Type} (x : option T) :
  Logic.eq (ovh_option_to_source (ovh_option_to_imported x)) x.
Proof. destruct x; reflexivity. Qed.

Lemma ovh_option_target_roundtrip {T : Type} (x : ImportedOverheads.Option T) :
  OvhOptionRel (ovh_option_to_source x) x.
Proof. destruct x; cbn; exact (@Lean.eq_refl _ _). Qed.

Definition ovh_state_to_imported (Job : eqType) (s : OvhSource Job) :
    OvhTarget Job :=
  match s with
  | prosa.model.processor.overheads.Idle =>
      ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state_Idle Job
  | prosa.model.processor.overheads.ContextSwitch j1 j2 =>
      ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state_ContextSwitch
        Job (ovh_option_to_imported j1) (ovh_option_to_imported j2)
  | prosa.model.processor.overheads.Dispatch j =>
      ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state_Dispatch
        Job (ovh_option_to_imported j)
  | prosa.model.processor.overheads.CacheRelatedPreemptionDelay j =>
      ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state_CacheRelatedPreemptionDelay
        Job j
  | prosa.model.processor.overheads.Progress j =>
      ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state_Progress Job j
  end.

Definition ovh_state_to_source (Job : eqType) (s : OvhTarget Job) :
    OvhSource Job :=
  match s with
  | ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state_Idle =>
      @prosa.model.processor.overheads.Idle Job
  | ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state_ContextSwitch j1 j2 =>
      @prosa.model.processor.overheads.ContextSwitch Job
        (ovh_option_to_source j1) (ovh_option_to_source j2)
  | ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state_Dispatch j =>
      @prosa.model.processor.overheads.Dispatch Job (ovh_option_to_source j)
  | ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state_CacheRelatedPreemptionDelay j =>
      @prosa.model.processor.overheads.CacheRelatedPreemptionDelay Job j
  | ImportedOverheads.Prosa_Model_Processor_Overheads_proc_state_Progress j =>
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
    (H : ImportedOverheads.False) : Q := match H return Q with end.

Lemma ovh_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedOverheads.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  OvhBoolRel bR (ImportedOverheads.Decidable_decide Q d).
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
    (bL : ImportedOverheads.Bool) :
  OvhBoolRel bR bL ->
  PropSPropRel (is_true (~~ bR))
    (Lean.eq bL ImportedOverheads.Bool_false).
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
      (ImportedOverheads.Prosa_Model_Processor_Overheads_overheads_scheduled_on
        Job (ovh_decidable_eq Job) j (ovh_state_to_imported Job s)
        ImportedOverheads.Unit_unit).
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
      (ImportedOverheads.Prosa_Model_Processor_Overheads_overheads_supply_on
        Job (ovh_decidable_eq Job) (ovh_state_to_imported Job s)
        ImportedOverheads.Unit_unit).
  Proof.
    destruct s; cbn; exact (sub_nat_rel_canonical _).
  Qed.

  Lemma ovh_service_on_correspondence (j : Job) (s : OvhSource Job) :
    SubNatRel
      (@prosa.model.processor.overheads.overheads_service_on Job j s tt)
      (ImportedOverheads.Prosa_Model_Processor_Overheads_overheads_service_on
        Job (ovh_decidable_eq Job) j (ovh_state_to_imported Job s)
        ImportedOverheads.Unit_unit).
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

Section ConcreteOverheads.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.overheads.processor_state Job.
  Let stateL :=
    ImportedOverheads.Prosa_Model_Processor_Overheads_processor_state
      Job (ovh_decidable_eq Job).

  Local Transparent prosa.behavior.schedule.scheduled_on
    prosa.behavior.schedule.supply_on
    prosa.behavior.schedule.service_on.

  Lemma ovh_instance_scheduled_field (j : Job) (s : OvhSource Job) :
    OvhBoolRel
      (@prosa.behavior.schedule.scheduled_on Job stateR j s tt)
      (ImportedOverheads.scheduled_on0 Job (ovh_decidable_eq Job)
        stateL j (ovh_state_to_imported Job s) ImportedOverheads.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (ovh_scheduled_on_correspondence Job j s).
  Qed.

  Lemma ovh_instance_supply_field (s : OvhSource Job) :
    SubNatRel
      (@prosa.behavior.schedule.supply_on Job stateR s tt)
      (ImportedOverheads.supply_on0 Job (ovh_decidable_eq Job)
        stateL (ovh_state_to_imported Job s) ImportedOverheads.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (ovh_supply_on_correspondence Job s).
  Qed.

  Lemma ovh_instance_service_field (j : Job) (s : OvhSource Job) :
    SubNatRel
      (@prosa.behavior.schedule.service_on Job stateR j s tt)
      (ImportedOverheads.service_on0 Job (ovh_decidable_eq Job)
        stateL j (ovh_state_to_imported Job s) ImportedOverheads.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (ovh_service_on_correspondence Job j s).
  Qed.

  Definition OvhSupplyLawR : Prop :=
    forall (j : Job) (s : OvhSource Job) (r : unit),
      is_true (leq
        (@prosa.model.processor.overheads.overheads_service_on Job j s r)
        (@prosa.model.processor.overheads.overheads_supply_on Job s r)).

  Definition OvhSupplyLawL : SProp :=
    forall (j : Job) (s : OvhTarget Job) (r : ImportedOverheads.Unit),
      ImportedOverheads.LE_le_inst1 Lean.Nat ImportedOverheads.instLENat
        (ImportedOverheads.Prosa_Model_Processor_Overheads_overheads_service_on
          Job (ovh_decidable_eq Job) j s r)
        (ImportedOverheads.Prosa_Model_Processor_Overheads_overheads_supply_on
          Job (ovh_decidable_eq Job) s r).

  Lemma ovh_supply_law_correspondence :
    PropSPropRel OvhSupplyLawR OvhSupplyLawL.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL rL.
      destruct rL.
      pose (sR := ovh_state_to_source Job sL).
      have Hstate : Logic.eq (ovh_state_to_imported Job sR) sL :=
        imported_eq_to_coq_eq _ _ (ovh_state_target_roundtrip Job sL).
      rewrite <- Hstate.
      exact (prop_to_sprop _ _
        (sub_nat_le_correspondence _ _ _ _
          (ovh_service_on_correspondence Job j sR)
          (ovh_supply_on_correspondence Job sR))
        (Hsource j sR tt)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR rR. destruct rR.
      exact (sprop_to_prop _ _
        (sub_nat_le_correspondence _ _ _ _
          (ovh_service_on_correspondence Job j sR)
          (ovh_supply_on_correspondence Job sR))
        (Htarget j (ovh_state_to_imported Job sR)
          ImportedOverheads.Unit_unit)).
  Qed.

  Definition OvhServiceRuleR : Prop :=
    forall (j : Job) (s : OvhSource Job) (r : unit),
      is_true (~~ @prosa.model.processor.overheads.overheads_scheduled_on
        Job j s r) ->
      Logic.eq (@prosa.model.processor.overheads.overheads_service_on Job j s r) O.

  Definition OvhServiceRuleL : SProp :=
    forall (j : Job) (s : OvhTarget Job) (r : ImportedOverheads.Unit),
      Lean.eq
        (ImportedOverheads.Prosa_Model_Processor_Overheads_overheads_scheduled_on
          Job (ovh_decidable_eq Job) j s r) ImportedOverheads.Bool_false ->
      Lean.eq
        (ImportedOverheads.Prosa_Model_Processor_Overheads_overheads_service_on
          Job (ovh_decidable_eq Job) j s r) Lean.Nat_zero.

  Lemma ovh_service_rule_correspondence :
    PropSPropRel OvhServiceRuleR OvhServiceRuleL.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL rL Hfalse.
      destruct rL.
      pose (sR := ovh_state_to_source Job sL).
      have Hstate : Logic.eq (ovh_state_to_imported Job sR) sL :=
        imported_eq_to_coq_eq _ _ (ovh_state_target_roundtrip Job sL).
      rewrite <- Hstate in Hfalse |- *.
      have Hscheduled := ovh_scheduled_on_correspondence Job j sR.
      have Hservice := ovh_service_on_correspondence Job j sR.
      have HsourceFalse := sprop_to_prop _ _
        (ovh_bool_false_correspondence _ _ Hscheduled) Hfalse.
      exact (prop_to_sprop _ _
        (sub_nat_eq_correspondence _ _ O Lean.Nat_zero
          Hservice (sub_nat_rel_canonical O))
        (Hsource j sR tt HsourceFalse)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR rR Hfalse. destruct rR.
      have Hscheduled := ovh_scheduled_on_correspondence Job j sR.
      have Hservice := ovh_service_on_correspondence Job j sR.
      have HtargetFalse := prop_to_sprop _ _
        (ovh_bool_false_correspondence _ _ Hscheduled) Hfalse.
      exact (sprop_to_prop _ _
        (sub_nat_eq_correspondence _ _ O Lean.Nat_zero
          Hservice (sub_nat_rel_canonical O))
        (Htarget j (ovh_state_to_imported Job sR)
          ImportedOverheads.Unit_unit HtargetFalse)).
  Qed.

  Definition ovh_core_to_imported (_ : unit) : ImportedOverheads.Unit :=
    ImportedOverheads.Unit_unit.

  Definition ovh_core_to_source (_ : ImportedOverheads.Unit) : unit := tt.

  Record OvhConcreteStateCertificate : Type := {
    ovh_state_source_inverse : forall s : OvhSource Job,
      Logic.eq (ovh_state_to_source Job (ovh_state_to_imported Job s)) s;
    ovh_state_target_inverse : forall s : OvhTarget Job,
      OvhRel Job (ovh_state_to_source Job s) s;
    ovh_core_source_inverse : forall c : unit,
      Logic.eq (ovh_core_to_source (ovh_core_to_imported c)) c;
    ovh_core_target_inverse : forall c : ImportedOverheads.Unit,
      Lean.eq (ovh_core_to_imported (ovh_core_to_source c)) c;
    ovh_scheduled_observation : forall j s,
      OvhBoolRel
        (@prosa.behavior.schedule.scheduled_on Job stateR j s tt)
        (ImportedOverheads.scheduled_on0 Job (ovh_decidable_eq Job)
          stateL j (ovh_state_to_imported Job s) ImportedOverheads.Unit_unit);
    ovh_supply_observation : forall s,
      SubNatRel
        (@prosa.behavior.schedule.supply_on Job stateR s tt)
        (ImportedOverheads.supply_on0 Job (ovh_decidable_eq Job)
          stateL (ovh_state_to_imported Job s) ImportedOverheads.Unit_unit);
    ovh_service_observation : forall j s,
      SubNatRel
        (@prosa.behavior.schedule.service_on Job stateR j s tt)
        (ImportedOverheads.service_on0 Job (ovh_decidable_eq Job)
          stateL j (ovh_state_to_imported Job s) ImportedOverheads.Unit_unit);
    ovh_supply_law_observation : PropSPropRel OvhSupplyLawR OvhSupplyLawL;
    ovh_service_law_observation : PropSPropRel OvhServiceRuleR OvhServiceRuleL
  }.

  Definition ovh_processor_state_correspondence :
      OvhConcreteStateCertificate :=
    {| ovh_state_source_inverse := ovh_state_source_roundtrip Job;
       ovh_state_target_inverse := ovh_state_target_roundtrip Job;
       ovh_core_source_inverse := fun c =>
         match c with tt => Logic.eq_refl tt end;
       ovh_core_target_inverse := fun c =>
         match c with ImportedOverheads.PUnit_unit => @Lean.eq_refl _ _ end;
       ovh_scheduled_observation := ovh_instance_scheduled_field;
       ovh_supply_observation := ovh_instance_supply_field;
       ovh_service_observation := ovh_instance_service_field;
       ovh_supply_law_observation := ovh_supply_law_correspondence;
       ovh_service_law_observation := ovh_service_rule_correspondence |}.
End ConcreteOverheads.

Section ScheduleObservations.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.overheads.processor_state Job.
  Let stateL :=
    ImportedOverheads.Prosa_Model_Processor_Overheads_processor_state
      Job (ovh_decidable_eq Job).

  Definition OvhScheduleRel
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      OvhRel Job (schedR tR) (schedL tL).

  Lemma ovh_scheduled_job_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job)
      (tR : nat) (tL : ImportedOverheads.Prosa_Behavior_Time_instant) :
    OvhScheduleRel schedR schedL -> SubNatRel tR tL ->
    OvhOptionRel
      (@prosa.model.processor.overheads.scheduled_job Job schedR tR)
      (ImportedOverheads.Prosa_Model_Processor_Overheads_scheduled_job
        Job (ovh_decidable_eq Job) schedL tL).
  Proof.
    intros Hsched Ht.
    unfold prosa.model.processor.overheads.scheduled_job,
      ImportedOverheads.Prosa_Model_Processor_Overheads_scheduled_job.
    have Hstate : Logic.eq (ovh_state_to_imported Job (schedR tR))
        (schedL tL) := imported_eq_to_coq_eq _ _ (Hsched tR tL Ht).
    rewrite <- Hstate.
    destruct (schedR tR) as [|a b|a|a|a]; cbn;
      exact (@Lean.eq_refl _ _).
  Qed.

  Lemma ovh_is_progress_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job)
      (tR : nat) (tL : ImportedOverheads.Prosa_Behavior_Time_instant) :
    OvhScheduleRel schedR schedL -> SubNatRel tR tL ->
    OvhBoolRel
      (@prosa.model.processor.overheads.is_progress Job schedR tR)
      (ImportedOverheads.Prosa_Model_Processor_Overheads_is_progress
        Job (ovh_decidable_eq Job) schedL tL).
  Proof.
    intros Hsched Ht.
    unfold prosa.model.processor.overheads.is_progress,
      ImportedOverheads.Prosa_Model_Processor_Overheads_is_progress.
    have Hstate : Logic.eq (ovh_state_to_imported Job (schedR tR))
        (schedL tL) := imported_eq_to_coq_eq _ _ (Hsched tR tL Ht).
    rewrite <- Hstate.
    destruct (schedR tR) as [|a b|a|a|a]; cbn;
      exact (@Lean.eq_refl _ _).
  Qed.

  Lemma ovh_is_context_switch_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job)
      (tR : nat) (tL : ImportedOverheads.Prosa_Behavior_Time_instant) :
    OvhScheduleRel schedR schedL -> SubNatRel tR tL ->
    OvhBoolRel
      (@prosa.model.processor.overheads.is_context_switch Job schedR tR)
      (ImportedOverheads.Prosa_Model_Processor_Overheads_is_context_switch
        Job (ovh_decidable_eq Job) schedL tL).
  Proof.
    intros Hsched Ht.
    unfold prosa.model.processor.overheads.is_context_switch,
      ImportedOverheads.Prosa_Model_Processor_Overheads_is_context_switch.
    have Hstate : Logic.eq (ovh_state_to_imported Job (schedR tR))
        (schedL tL) := imported_eq_to_coq_eq _ _ (Hsched tR tL Ht).
    rewrite <- Hstate.
    destruct (schedR tR) as [|a b|a|a|a]; cbn;
      exact (@Lean.eq_refl _ _).
  Qed.

  Lemma ovh_is_dispatch_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job)
      (tR : nat) (tL : ImportedOverheads.Prosa_Behavior_Time_instant) :
    OvhScheduleRel schedR schedL -> SubNatRel tR tL ->
    OvhBoolRel
      (@prosa.model.processor.overheads.is_dispatch Job schedR tR)
      (ImportedOverheads.Prosa_Model_Processor_Overheads_is_dispatch
        Job (ovh_decidable_eq Job) schedL tL).
  Proof.
    intros Hsched Ht.
    unfold prosa.model.processor.overheads.is_dispatch,
      ImportedOverheads.Prosa_Model_Processor_Overheads_is_dispatch.
    have Hstate : Logic.eq (ovh_state_to_imported Job (schedR tR))
        (schedL tL) := imported_eq_to_coq_eq _ _ (Hsched tR tL Ht).
    rewrite <- Hstate.
    destruct (schedR tR) as [|a b|a|a|a]; cbn;
      exact (@Lean.eq_refl _ _).
  Qed.

  Lemma ovh_is_CRPD_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job)
      (tR : nat) (tL : ImportedOverheads.Prosa_Behavior_Time_instant) :
    OvhScheduleRel schedR schedL -> SubNatRel tR tL ->
    OvhBoolRel
      (@prosa.model.processor.overheads.is_CRPD Job schedR tR)
      (ImportedOverheads.Prosa_Model_Processor_Overheads_is_CRPD
        Job (ovh_decidable_eq Job) schedL tL).
  Proof.
    intros Hsched Ht.
    unfold prosa.model.processor.overheads.is_CRPD,
      ImportedOverheads.Prosa_Model_Processor_Overheads_is_CRPD.
    have Hstate : Logic.eq (ovh_state_to_imported Job (schedR tR))
        (schedL tL) := imported_eq_to_coq_eq _ _ (Hsched tR tL Ht).
    rewrite <- Hstate.
    destruct (schedR tR) as [|a b|a|a|a]; cbn;
      exact (@Lean.eq_refl _ _).
  Qed.
End ScheduleObservations.

Lemma ovh_bool_to_nat_related (bR : bool) (bL : ImportedOverheads.Bool) :
  OvhBoolRel bR bL ->
  SubNatRel (nat_of_bool bR) (ImportedOverheads.Bool_toNat bL).
Proof.
  intro Hb.
  have H : Logic.eq (ovh_bool_to_imported bR) bL :=
    imported_eq_to_coq_eq _ _ Hb.
  rewrite <- H. destruct bR; exact (sub_nat_rel_canonical _).
Qed.

Section IntervalCounts.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.overheads.processor_state Job.
  Let stateL :=
    ImportedOverheads.Prosa_Model_Processor_Overheads_processor_state
      Job (ovh_decidable_eq Job).

  Lemma ovh_total_time_in_dispatch_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job)
      (t1R t2R : nat)
      (t1L t2L : ImportedOverheads.Prosa_Behavior_Time_instant) :
    OvhScheduleRel Job schedR schedL ->
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@prosa.model.processor.overheads.total_time_in_dispatch
        Job schedR t1R t2R)
      (ImportedOverheads.Prosa_Model_Processor_Overheads_total_time_in_dispatch
        Job (ovh_decidable_eq Job) schedL t1L t2L).
  Proof.
    intros Hsched Ht1 Ht2.
    change (SubNatRel
      (\sum_(t1R <= t < t2R)
        nat_of_bool (@prosa.model.processor.overheads.is_dispatch Job schedR t))
      (svc_target_interval_value t1L t2L
        (fun t => ImportedOverheads.Bool_toNat
          (ImportedOverheads.Prosa_Model_Processor_Overheads_is_dispatch
            Job (ovh_decidable_eq Job) schedL t)))).
    apply svc_interval_sum_related; try assumption.
    intros tR tL Ht.
    apply ovh_bool_to_nat_related.
    exact (ovh_is_dispatch_correspondence Job schedR schedL tR tL Hsched Ht).
  Qed.

  Lemma ovh_total_time_in_context_switch_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job)
      (t1R t2R : nat)
      (t1L t2L : ImportedOverheads.Prosa_Behavior_Time_instant) :
    OvhScheduleRel Job schedR schedL ->
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@prosa.model.processor.overheads.total_time_in_context_switch
        Job schedR t1R t2R)
      (ImportedOverheads.Prosa_Model_Processor_Overheads_total_time_in_context_switch
        Job (ovh_decidable_eq Job) schedL t1L t2L).
  Proof.
    intros Hsched Ht1 Ht2.
    change (SubNatRel
      (\sum_(t1R <= t < t2R)
        nat_of_bool (@prosa.model.processor.overheads.is_context_switch Job schedR t))
      (svc_target_interval_value t1L t2L
        (fun t => ImportedOverheads.Bool_toNat
          (ImportedOverheads.Prosa_Model_Processor_Overheads_is_context_switch
            Job (ovh_decidable_eq Job) schedL t)))).
    apply svc_interval_sum_related; try assumption.
    intros tR tL Ht.
    apply ovh_bool_to_nat_related.
    exact (ovh_is_context_switch_correspondence
      Job schedR schedL tR tL Hsched Ht).
  Qed.

  Lemma ovh_total_time_in_CRPD_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : Lean.Nat -> OvhTarget Job)
      (t1R t2R : nat)
      (t1L t2L : ImportedOverheads.Prosa_Behavior_Time_instant) :
    OvhScheduleRel Job schedR schedL ->
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@prosa.model.processor.overheads.total_time_in_CRPD
        Job schedR t1R t2R)
      (ImportedOverheads.Prosa_Model_Processor_Overheads_total_time_in_CRPD
        Job (ovh_decidable_eq Job) schedL t1L t2L).
  Proof.
    intros Hsched Ht1 Ht2.
    change (SubNatRel
      (\sum_(t1R <= t < t2R)
        nat_of_bool (@prosa.model.processor.overheads.is_CRPD Job schedR t))
      (svc_target_interval_value t1L t2L
        (fun t => ImportedOverheads.Bool_toNat
          (ImportedOverheads.Prosa_Model_Processor_Overheads_is_CRPD
            Job (ovh_decidable_eq Job) schedL t)))).
    apply svc_interval_sum_related; try assumption.
    intros tR tL Ht.
    apply ovh_bool_to_nat_related.
    exact (ovh_is_CRPD_correspondence Job schedR schedL tR tL Hsched Ht).
  Qed.
End IntervalCounts.

Print Assumptions ovh_option_target_roundtrip.
Print Assumptions ovh_state_target_roundtrip.
Print Assumptions ovh_scheduled_on_correspondence.
Print Assumptions ovh_supply_on_correspondence.
Print Assumptions ovh_service_on_correspondence.
Print Assumptions ovh_scheduled_job_correspondence.
Print Assumptions ovh_is_progress_correspondence.
Print Assumptions ovh_is_context_switch_correspondence.
Print Assumptions ovh_is_dispatch_correspondence.
Print Assumptions ovh_is_CRPD_correspondence.
Print Assumptions ovh_processor_state_correspondence.
Print Assumptions ovh_total_time_in_dispatch_correspondence.
Print Assumptions ovh_total_time_in_context_switch_correspondence.
Print Assumptions ovh_total_time_in_CRPD_correspondence.
