From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import behavior.all model.processor.ideal_uni_exceed model.processor.platform_properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaExcFpFullyNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ExcArrivalsSeqBaseAdapter ExcArrivalsSeqOperations ExcArrivalsSeqCorrespondence ExcArrivalsCorrespondence
  ExcJitterSvcBaseAdapter ExcJitterSvcNatBoolOperations ExcJitterSvcIntervalOperations
  ExcJitterSvcScheduleOperations ExcJitterSvcJobOperations ExcPStateCoverHelpers.

Module I := ImportedRtaExcFpFullyNonpreemptive.

(** The concrete exceedance processor states related constructor-wise; the unit core;
    [scheduled_on] per core by case analysis; [service_in]/[supply_in] through the
    kernel-checked closed forms of the validation interface. *)

Section ExcState.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PR := prosa.model.processor.ideal_uni_exceed.exceedance_proc_state Job.
  Let PL := I.Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job dJ.

  Definition exc_st_to (s : @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state Job) :
      I.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job :=
    match s with
    | prosa.model.processor.ideal_uni_exceed.NominalExecution j =>
        I.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_NominalExecution Job j
    | prosa.model.processor.ideal_uni_exceed.ExceedanceExecution j =>
        I.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_ExceedanceExecution Job j
    | prosa.model.processor.ideal_uni_exceed.Idle =>
        I.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_Idle Job
    end.

  Definition exc_st_from (s : I.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job) :
      @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state Job :=
    match s with
    | I.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_NominalExecution j =>
        prosa.model.processor.ideal_uni_exceed.NominalExecution j
    | I.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_ExceedanceExecution j =>
        prosa.model.processor.ideal_uni_exceed.ExceedanceExecution j
    | I.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_Idle =>
        prosa.model.processor.ideal_uni_exceed.Idle
    end.

  Lemma exc_st_rt_source s : exc_st_from (exc_st_to s) = s.
  Proof. by case: s. Qed.
  Lemma exc_st_rt_target s : Lean.eq (exc_st_to (exc_st_from s)) s.
  Proof. destruct s; exact (@Lean.eq_refl _ _). Qed.

  Definition exc_co_to (c : unit) : I.Prosa_Behavior_Schedule_ProcessorState_Core_inst2 Job dJ PL := I.PUnit_unit.
  Definition exc_co_from (c : I.Prosa_Behavior_Schedule_ProcessorState_Core_inst2 Job dJ PL) : unit := tt.
  Lemma exc_co_rt_target c : Lean.eq (exc_co_to (exc_co_from c)) c.
  Proof. destruct c; exact (@Lean.eq_refl _ _). Qed.

  (* the two sides decide job equality through the same [eqP] *)
  Lemma exc_eq_rel (x y : Job) :
    SvcBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (dJ x y)).
  Proof. exact (ari_decide_eq_related Job x y). Qed.

  Lemma exc_sch_rel j s c :
    SvcBoolRel (@prosa.behavior.schedule.scheduled_on Job PR j s c)
      (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_on_inst2 Job dJ PL j (exc_st_to s) (exc_co_to c)).
  Proof.
    destruct s as [j' | j' |]; cbn.
    - exact (exc_eq_rel j' j).
    - exact (exc_eq_rel j' j).
    - exact (@Lean.eq_refl _ _).
  Qed.

  Lemma exc_sum_unit (F : unit -> nat) : \sum_(r : unit) F r = F tt.
  Proof. by rewrite (big_pred1 tt) // => -[]. Qed.

  Lemma exc_subnat_transport (a b : nat) (x : Lean.Nat) : a = b -> SubNatRel b x -> SubNatRel a x.
  Proof. intro E. destruct E. exact (fun h => h). Qed.

  Lemma exc_srv_on_rel j s :
    SubNatRel (prosa.model.processor.ideal_uni_exceed.exceedance_service_on j s tt)
      (I.Prosa_Model_Processor_IdealUniExceed_exceedance_service_on Job dJ j (exc_st_to s) I.PUnit_unit).
  Proof.
    destruct s as [j' | j' |]; try exact (sub_nat_rel_canonical O).
    cbn. unfold dJ, ar_decidable_eq. destruct (@eqP Job j' j); exact (sub_nat_rel_canonical _).
  Qed.

  Lemma exc_sup_on_rel s :
    SubNatRel (prosa.model.processor.ideal_uni_exceed.exceedance_supply_on s tt)
      (I.Prosa_Model_Processor_IdealUniExceed_exceedance_supply_on Job dJ (exc_st_to s) I.PUnit_unit).
  Proof. destruct s; exact (sub_nat_rel_canonical _). Qed.

  Lemma exc_srv_in_rel j s :
    SubNatRel (@prosa.behavior.schedule.service_in Job PR j s)
      (I.Prosa_Behavior_Schedule_ProcessorState_service_in_inst4 Job dJ PL j (exc_st_to s)).
  Proof.
    exact (sub_imported_eq_trans _ _ _
      (exc_subnat_transport _ _ _ (exc_sum_unit _) (exc_srv_on_rel j s))
      (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ExceedanceInterface_production_exceedance_service_in Job dJ j (exc_st_to s)))).
  Qed.

  Lemma exc_sup_in_rel s :
    SubNatRel (@prosa.behavior.schedule.supply_in Job PR s)
      (I.Prosa_Behavior_Schedule_ProcessorState_supply_in_inst4 Job dJ PL (exc_st_to s)).
  Proof.
    exact (sub_imported_eq_trans _ _ _
      (exc_subnat_transport _ _ _ (exc_sum_unit _) (exc_sup_on_rel s))
      (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ExceedanceInterface_production_exceedance_supply_in Job dJ (exc_st_to s)))).
  Qed.

  Definition exc_psrel : IsjPSRel Job PR PL :=
    Build_IsjPSRel Job PR PL (exc_st_to) (exc_st_from) exc_st_rt_source exc_st_rt_target
      exc_co_to exc_co_from exc_co_rt_target exc_sch_rel exc_srv_in_rel exc_sup_in_rel.
End ExcState.
