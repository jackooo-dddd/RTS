From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import behavior.all model.processor.overheads model.processor.platform_properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedOverheadsSbfJlfp ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence
  OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations
  OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPStateCoverHelpers.

Module I := ImportedOverheadsSbfJlfp.

(** The concrete overheads processor states related constructor-wise; the unit core;
    [scheduled_on] per core by case analysis; [service_in]/[supply_in] through the
    kernel-checked closed forms of the validation interface. *)

Section OvhState.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PR := prosa.model.processor.overheads.processor_state Job.
  Let PL := I.Prosa_Model_Processor_Overheads_processor_state Job dJ.

  Definition ovh_opt_to (x : option Job) : I.Option Job :=
    match x with Some j => I.Option_some Job j | None => I.Option_none Job end.
  Definition ovh_opt_from (y : I.Option Job) : option Job :=
    match y with I.Option_some j => Some j | I.Option_none => None end.

  Definition ovh_st_to (s : prosa.model.processor.overheads.proc_state Job) :
      I.Prosa_Model_Processor_Overheads_proc_state Job :=
    match s with
    | prosa.model.processor.overheads.Idle => I.Prosa_Model_Processor_Overheads_proc_state_Idle Job
    | prosa.model.processor.overheads.ContextSwitch a b =>
        I.Prosa_Model_Processor_Overheads_proc_state_ContextSwitch Job (ovh_opt_to a) (ovh_opt_to b)
    | prosa.model.processor.overheads.Dispatch a =>
        I.Prosa_Model_Processor_Overheads_proc_state_Dispatch Job (ovh_opt_to a)
    | prosa.model.processor.overheads.CacheRelatedPreemptionDelay j =>
        I.Prosa_Model_Processor_Overheads_proc_state_CacheRelatedPreemptionDelay Job j
    | prosa.model.processor.overheads.Progress j =>
        I.Prosa_Model_Processor_Overheads_proc_state_Progress Job j
    end.

  Definition ovh_st_from (s : I.Prosa_Model_Processor_Overheads_proc_state Job) :
      prosa.model.processor.overheads.proc_state Job :=
    match s with
    | I.Prosa_Model_Processor_Overheads_proc_state_Idle => prosa.model.processor.overheads.Idle Job
    | I.Prosa_Model_Processor_Overheads_proc_state_ContextSwitch a b =>
        prosa.model.processor.overheads.ContextSwitch Job (ovh_opt_from a) (ovh_opt_from b)
    | I.Prosa_Model_Processor_Overheads_proc_state_Dispatch a =>
        prosa.model.processor.overheads.Dispatch Job (ovh_opt_from a)
    | I.Prosa_Model_Processor_Overheads_proc_state_CacheRelatedPreemptionDelay j =>
        prosa.model.processor.overheads.CacheRelatedPreemptionDelay Job j
    | I.Prosa_Model_Processor_Overheads_proc_state_Progress j =>
        prosa.model.processor.overheads.Progress Job j
    end.

  Lemma ovh_opt_rt_source x : ovh_opt_from (ovh_opt_to x) = x.
  Proof. by case: x. Qed.
  Lemma ovh_opt_rt_target y : Lean.eq (ovh_opt_to (ovh_opt_from y)) y.
  Proof. destruct y; exact (@Lean.eq_refl _ _). Qed.

  Lemma ovh_st_rt_source s : ovh_st_from (ovh_st_to s) = s.
  Proof. by case: s => //= *; rewrite !ovh_opt_rt_source. Qed.
  Lemma ovh_st_rt_target s : Lean.eq (ovh_st_to (ovh_st_from s)) s.
  Proof.
    destruct s as [| a b | a | j | j]; cbn; try exact (@Lean.eq_refl _ _).
    - destruct a, b; exact (@Lean.eq_refl _ _).
    - destruct a; exact (@Lean.eq_refl _ _).
  Qed.

  Definition ovh_co_to (c : unit) : I.Prosa_Behavior_Schedule_ProcessorState_Core_inst2 Job dJ PL := I.PUnit_unit.
  Definition ovh_co_from (c : I.Prosa_Behavior_Schedule_ProcessorState_Core_inst2 Job dJ PL) : unit := tt.
  Lemma ovh_co_rt_target c : Lean.eq (ovh_co_to (ovh_co_from c)) c.
  Proof. destruct c; exact (@Lean.eq_refl _ _). Qed.

  (* the two sides decide job equality through the same [eqP] *)
  Lemma ovh_eq_rel (x y : Job) :
    SvcBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (dJ x y)).
  Proof. exact (ari_decide_eq_related Job x y). Qed.

  Lemma ovh_sch_rel j s c :
    SvcBoolRel (@prosa.behavior.schedule.scheduled_on Job PR j s c)
      (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_on_inst2 Job dJ PL j (ovh_st_to s) (ovh_co_to c)).
  Proof.
    destruct s as [| a b | a | j' | j']; cbn.
    - exact (@Lean.eq_refl _ _).
    - destruct b as [j'|]; cbn; [exact (ovh_eq_rel j j') | exact (@Lean.eq_refl _ _)].
    - destruct a as [j'|]; cbn; [exact (ovh_eq_rel j j') | exact (@Lean.eq_refl _ _)].
    - exact (ovh_eq_rel j j').
    - exact (ovh_eq_rel j j').
  Qed.

  Lemma ovh_sum_unit (F : unit -> nat) : \sum_(r : unit) F r = F tt.
  Proof. by rewrite (big_pred1 tt) // => -[]. Qed.

  Lemma ovh_subnat_transport (a b : nat) (x : Lean.Nat) : a = b -> SubNatRel b x -> SubNatRel a x.
  Proof. intro E. destruct E. exact (fun h => h). Qed.

  Lemma ovh_srv_on_rel j s :
    SubNatRel (prosa.model.processor.overheads.overheads_service_on Job j s tt)
      (I.Prosa_Model_Processor_Overheads_overheads_service_on Job dJ j (ovh_st_to s) I.PUnit_unit).
  Proof.
    destruct s as [| a b | a | j' | j']; try exact (sub_nat_rel_canonical O).
    cbn. unfold dJ, ar_decidable_eq. destruct (@eqP Job j' j); exact (sub_nat_rel_canonical _).
  Qed.

  Lemma ovh_sup_on_rel s :
    SubNatRel (prosa.model.processor.overheads.overheads_supply_on Job s tt)
      (I.Prosa_Model_Processor_Overheads_overheads_supply_on Job dJ (ovh_st_to s) I.PUnit_unit).
  Proof. destruct s; exact (sub_nat_rel_canonical _). Qed.

  Lemma ovh_srv_in_rel j s :
    SubNatRel (@prosa.behavior.schedule.service_in Job PR j s)
      (I.Prosa_Behavior_Schedule_ProcessorState_service_in_inst4 Job dJ PL j (ovh_st_to s)).
  Proof.
    exact (sub_imported_eq_trans _ _ _
      (ovh_subnat_transport _ _ _ (ovh_sum_unit _) (ovh_srv_on_rel j s))
      (sub_imported_eq_sym _ _
        (I.Prosa_Validation_OverheadsInterface_production_overheads_service_in Job dJ j (ovh_st_to s)))).
  Qed.

  Lemma ovh_sup_in_rel s :
    SubNatRel (@prosa.behavior.schedule.supply_in Job PR s)
      (I.Prosa_Behavior_Schedule_ProcessorState_supply_in_inst4 Job dJ PL (ovh_st_to s)).
  Proof.
    exact (sub_imported_eq_trans _ _ _
      (ovh_subnat_transport _ _ _ (ovh_sum_unit _) (ovh_sup_on_rel s))
      (sub_imported_eq_sym _ _
        (I.Prosa_Validation_OverheadsInterface_production_overheads_supply_in Job dJ (ovh_st_to s)))).
  Qed.

  Definition ovh_psrel : IsjPSRel Job PR PL :=
    Build_IsjPSRel Job PR PL (ovh_st_to) (ovh_st_from) ovh_st_rt_source ovh_st_rt_target
      ovh_co_to ovh_co_from ovh_co_rt_target ovh_sch_rel ovh_srv_in_rel ovh_sup_in_rel.
End OvhState.
