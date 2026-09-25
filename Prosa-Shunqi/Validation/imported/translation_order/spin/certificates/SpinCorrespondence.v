From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.spin.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSpinFull.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence SpinBaseAdapter.

Definition SpinSource (Job : eqType) : Type :=
  @prosa.model.processor.spin.processor_state Job.

Definition SpinTarget (Job : Type) : Type :=
  ImportedSpinFull.Prosa_Model_Processor_Spin_processor_state Job.

Definition spin_to_target (Job : eqType) (s : SpinSource Job) : SpinTarget Job :=
  match s with
  | prosa.model.processor.spin.Idle =>
      ImportedSpinFull.Prosa_Model_Processor_Spin_processor_state_Idle Job
  | prosa.model.processor.spin.Spin j =>
      ImportedSpinFull.Prosa_Model_Processor_Spin_processor_state_Spin Job j
  | prosa.model.processor.spin.Progress j =>
      ImportedSpinFull.Prosa_Model_Processor_Spin_processor_state_Progress Job j
  end.

Definition spin_to_source (Job : eqType) (s : SpinTarget Job) : SpinSource Job :=
  match s with
  | ImportedSpinFull.Prosa_Model_Processor_Spin_processor_state_Idle =>
      @prosa.model.processor.spin.Idle Job
  | ImportedSpinFull.Prosa_Model_Processor_Spin_processor_state_Spin j =>
      @prosa.model.processor.spin.Spin Job j
  | ImportedSpinFull.Prosa_Model_Processor_Spin_processor_state_Progress j =>
      @prosa.model.processor.spin.Progress Job j
  end.

Definition SpinStateRel (Job : eqType) (sR : SpinSource Job)
    (sL : SpinTarget Job) : SProp := Lean.eq (spin_to_target Job sR) sL.

Lemma spin_source_roundtrip (Job : eqType) (s : SpinSource Job) :
  Logic.eq (spin_to_source Job (spin_to_target Job s)) s.
Proof. by destruct s. Qed.

Lemma spin_target_roundtrip (Job : eqType) (s : SpinTarget Job) :
  SpinStateRel Job (spin_to_source Job s) s.
Proof. destruct s; cbn; exact (@Lean.eq_refl _ _). Qed.

Record SpinStateTypeCertificate (Job : eqType) : Type := {
  spin_state_source_roundtrip : forall s : SpinSource Job,
    Logic.eq (spin_to_source Job (spin_to_target Job s)) s;
  spin_state_target_roundtrip : forall s : SpinTarget Job,
    SpinStateRel Job (spin_to_source Job s) s
}.

Definition spin_state_type_correspondence (Job : eqType) :
    SpinStateTypeCertificate Job :=
  {| spin_state_source_roundtrip := spin_source_roundtrip Job;
     spin_state_target_roundtrip := spin_target_roundtrip Job |}.

Lemma spin_job_equality_truth (Job : eqType) (x y : Job) :
  PropSPropRel (is_true (x == y)) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - move/eqP=> H. exact (coq_eq_to_imported_eq x y H).
  - intro H. apply strictly_inhabits. apply/eqP.
    exact (imported_eq_to_coq_eq x y H).
Qed.

Definition spin_target_false_elim (Q : SProp)
    (H : ImportedSpinFull.False) : Q :=
  match H return Q with end.

Lemma spin_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedSpinFull.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  SpinBoolRel bR (ImportedSpinFull.Decidable_decide Q d).
Proof.
  intro Hrel. unfold SpinBoolRel.
  destruct d as [Hfalse | Htrue]; destruct bR; cbn.
  - exact (spin_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (spin_target_false_elim _ (spin_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Section ConcreteSpin.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.spin.pstate_instance Job.
  Let stateL :=
    ImportedSpinFull.Prosa_Model_Processor_Spin_pstate_instance
      Job (spin_decidable_eq Job).

  Local Transparent prosa.behavior.schedule.scheduled_on
    prosa.behavior.schedule.supply_on
    prosa.behavior.schedule.service_on.

  Definition spin_core_to_imported (_ : unit) : ImportedSpinFull.Unit :=
    ImportedSpinFull.Unit_unit.
  Definition spin_core_to_source (_ : ImportedSpinFull.Unit) : unit := tt.

  Lemma spin_scheduled_on_correspondence (j : Job) (s : SpinSource Job) :
    SpinBoolRel
      (@prosa.model.processor.spin.spin_scheduled_on Job j s tt)
      (ImportedSpinFull.Prosa_Model_Processor_Spin_spin_scheduled_on
        Job (spin_decidable_eq Job) j (spin_to_target Job s)
        ImportedSpinFull.Unit_unit).
  Proof.
    destruct s as [|a|a]; cbn;
      try exact (@Lean.eq_refl _ _);
      apply spin_decide_bool_correspondence;
      exact (spin_job_equality_truth Job a j).
  Qed.

  Lemma spin_supply_on_correspondence (s : SpinSource Job) :
    SubNatRel
      (@prosa.model.processor.spin.spin_supply_on Job s tt)
      (ImportedSpinFull.Prosa_Model_Processor_Spin_spin_supply_on
        Job (spin_decidable_eq Job) (spin_to_target Job s)
        ImportedSpinFull.Unit_unit).
  Proof. destruct s; cbn; exact (sub_nat_rel_canonical _). Qed.

  Lemma spin_service_on_correspondence (j : Job) (s : SpinSource Job) :
    SubNatRel
      (@prosa.model.processor.spin.spin_service_on Job j s tt)
      (ImportedSpinFull.Prosa_Model_Processor_Spin_spin_service_on
        Job (spin_decidable_eq Job) j (spin_to_target Job s)
        ImportedSpinFull.Unit_unit).
  Proof.
    destruct s as [|a|a]; cbn;
      try exact (sub_nat_rel_canonical O).
    have Hdec := spin_decide_bool_correspondence
      (a == j) (Lean.eq a j) (spin_decidable_eq Job a j)
      (spin_job_equality_truth Job a j).
    unfold SpinBoolRel in Hdec. destruct Hdec.
    destruct (a == j); cbn; exact (sub_nat_rel_canonical _).
  Qed.

  Lemma spin_instance_scheduled_field (j : Job) (s : SpinSource Job) :
    SpinBoolRel
      (@prosa.behavior.schedule.scheduled_on Job stateR j s tt)
      (ImportedSpinFull.scheduled_on0 Job (spin_decidable_eq Job)
        stateL j (spin_to_target Job s) ImportedSpinFull.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (spin_scheduled_on_correspondence j s).
  Qed.

  Lemma spin_instance_supply_field (s : SpinSource Job) :
    SubNatRel
      (@prosa.behavior.schedule.supply_on Job stateR s tt)
      (ImportedSpinFull.supply_on0 Job (spin_decidable_eq Job)
        stateL (spin_to_target Job s) ImportedSpinFull.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (spin_supply_on_correspondence s).
  Qed.

  Lemma spin_instance_service_field (j : Job) (s : SpinSource Job) :
    SubNatRel
      (@prosa.behavior.schedule.service_on Job stateR j s tt)
      (ImportedSpinFull.service_on0 Job (spin_decidable_eq Job)
        stateL j (spin_to_target Job s) ImportedSpinFull.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (spin_service_on_correspondence j s).
  Qed.

  Lemma spin_bool_false_correspondence (bR : bool)
      (bL : ImportedSpinFull.Bool) :
    SpinBoolRel bR bL ->
    PropSPropRel (is_true (~~ bR))
      (Lean.eq bL ImportedSpinFull.Bool_false).
  Proof.
    intro Hb. apply prop_sprop_rel_intro.
    - intro Hfalse. destruct bR, bL; cbn in *.
      + discriminate Hfalse.
      + discriminate Hfalse.
      + exact (@Lean.eq_refl _ _).
      + exact (spin_false_elim _ (spin_false_ne_true Hb)).
    - intro Hfalse. destruct bR, bL; cbn in *.
      + exact (spin_false_elim _ (spin_false_ne_true
          (sub_imported_eq_sym _ _ Hb))).
      + exact (spin_false_elim _ (spin_false_ne_true
          (sub_imported_eq_sym _ _ Hfalse))).
      + exact (strictly_inhabits (Logic.eq_refl true)).
      + exact (spin_false_elim _ (spin_false_ne_true Hb)).
  Qed.

  Definition SpinSupplyLawR : Prop :=
    forall (j : Job) (s : SpinSource Job) (r : unit),
      is_true (leq
        (@prosa.model.processor.spin.spin_service_on Job j s r)
        (@prosa.model.processor.spin.spin_supply_on Job s r)).

  Definition SpinSupplyLawL : SProp :=
    forall (j : Job) (s : SpinTarget Job)
        (r : ImportedSpinFull.Unit),
      ImportedSpinFull.LE_le_inst1 Lean.Nat
        ImportedSpinFull.instLENat
        (ImportedSpinFull.Prosa_Model_Processor_Spin_spin_service_on
          Job (spin_decidable_eq Job) j s r)
        (ImportedSpinFull.Prosa_Model_Processor_Spin_spin_supply_on
          Job (spin_decidable_eq Job) s r).

  Lemma spin_supply_law_correspondence :
    PropSPropRel SpinSupplyLawR SpinSupplyLawL.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL rL. destruct rL.
      pose (sR := spin_to_source Job sL).
      have Hstate : Logic.eq (spin_to_target Job sR) sL :=
        imported_eq_to_coq_eq _ _ (spin_target_roundtrip Job sL).
      rewrite <- Hstate.
      exact (prop_to_sprop _ _
        (sub_nat_le_correspondence _ _ _ _
          (spin_service_on_correspondence j sR)
          (spin_supply_on_correspondence sR))
        (Hsource j sR tt)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR rR. destruct rR.
      exact (sprop_to_prop _ _
        (sub_nat_le_correspondence _ _ _ _
          (spin_service_on_correspondence j sR)
          (spin_supply_on_correspondence sR))
        (Htarget j (spin_to_target Job sR)
          ImportedSpinFull.Unit_unit)).
  Qed.

  Definition SpinServiceRuleR : Prop :=
    forall (j : Job) (s : SpinSource Job) (r : unit),
      is_true (~~ @prosa.model.processor.spin.spin_scheduled_on
        Job j s r) ->
      Logic.eq
        (@prosa.model.processor.spin.spin_service_on Job j s r) O.

  Definition SpinServiceRuleL : SProp :=
    forall (j : Job) (s : SpinTarget Job)
        (r : ImportedSpinFull.Unit),
      Lean.eq
        (ImportedSpinFull.Prosa_Model_Processor_Spin_spin_scheduled_on
          Job (spin_decidable_eq Job) j s r) ImportedSpinFull.Bool_false ->
      Lean.eq
        (ImportedSpinFull.Prosa_Model_Processor_Spin_spin_service_on
          Job (spin_decidable_eq Job) j s r) Lean.Nat_zero.

  Lemma spin_service_rule_correspondence :
    PropSPropRel SpinServiceRuleR SpinServiceRuleL.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL rL Hfalse. destruct rL.
      pose (sR := spin_to_source Job sL).
      have Hstate : Logic.eq (spin_to_target Job sR) sL :=
        imported_eq_to_coq_eq _ _ (spin_target_roundtrip Job sL).
      rewrite <- Hstate in Hfalse |- *.
      have Hscheduled := spin_scheduled_on_correspondence j sR.
      have Hservice := spin_service_on_correspondence j sR.
      have HsourceFalse := sprop_to_prop _ _
        (spin_bool_false_correspondence _ _ Hscheduled) Hfalse.
      exact (prop_to_sprop _ _
        (sub_nat_eq_correspondence _ _ O Lean.Nat_zero
          Hservice (sub_nat_rel_canonical O))
        (Hsource j sR tt HsourceFalse)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR rR Hfalse. destruct rR.
      have Hscheduled := spin_scheduled_on_correspondence j sR.
      have Hservice := spin_service_on_correspondence j sR.
      have HtargetFalse := prop_to_sprop _ _
        (spin_bool_false_correspondence _ _ Hscheduled) Hfalse.
      exact (sprop_to_prop _ _
        (sub_nat_eq_correspondence _ _ O Lean.Nat_zero
          Hservice (sub_nat_rel_canonical O))
        (Htarget j (spin_to_target Job sR)
          ImportedSpinFull.Unit_unit HtargetFalse)).
  Qed.

  Record SpinConcreteStateCertificate : Type := {
    spin_state_roundtrip_source : forall s : SpinSource Job,
      Logic.eq (spin_to_source Job (spin_to_target Job s)) s;
    spin_state_roundtrip_target : forall s : SpinTarget Job,
      SpinStateRel Job (spin_to_source Job s) s;
    spin_core_roundtrip_source : forall c : unit,
      Logic.eq (spin_core_to_source (spin_core_to_imported c)) c;
    spin_core_roundtrip_target : forall c : ImportedSpinFull.Unit,
      Lean.eq (spin_core_to_imported (spin_core_to_source c)) c;
    spin_scheduled_field : forall j s, SpinBoolRel
      (@prosa.behavior.schedule.scheduled_on Job stateR j s tt)
      (ImportedSpinFull.scheduled_on0 Job (spin_decidable_eq Job)
        stateL j (spin_to_target Job s) ImportedSpinFull.Unit_unit);
    spin_supply_field : forall s, SubNatRel
      (@prosa.behavior.schedule.supply_on Job stateR s tt)
      (ImportedSpinFull.supply_on0 Job (spin_decidable_eq Job)
        stateL (spin_to_target Job s) ImportedSpinFull.Unit_unit);
    spin_service_field : forall j s, SubNatRel
      (@prosa.behavior.schedule.service_on Job stateR j s tt)
      (ImportedSpinFull.service_on0 Job (spin_decidable_eq Job)
        stateL j (spin_to_target Job s) ImportedSpinFull.Unit_unit);
    spin_supply_law_field : PropSPropRel SpinSupplyLawR SpinSupplyLawL;
    spin_service_law_field : PropSPropRel SpinServiceRuleR SpinServiceRuleL
  }.

  Definition pstate_instance_correspondence :
      SpinConcreteStateCertificate :=
    {| spin_state_roundtrip_source := spin_source_roundtrip Job;
       spin_state_roundtrip_target := spin_target_roundtrip Job;
       spin_core_roundtrip_source := fun c =>
         match c with tt => Logic.eq_refl tt end;
       spin_core_roundtrip_target := fun c =>
         match c with ImportedSpinFull.PUnit_unit =>
           @Lean.eq_refl _ _ end;
       spin_scheduled_field := spin_instance_scheduled_field;
       spin_supply_field := spin_instance_supply_field;
       spin_service_field := spin_instance_service_field;
       spin_supply_law_field := spin_supply_law_correspondence;
       spin_service_law_field := spin_service_rule_correspondence |}.

End ConcreteSpin.
