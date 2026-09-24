From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.restricted_supply.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRestrictedSupplyFull.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence RestrictedSupplyBaseAdapter.

Definition RsSource (Job : eqType) : Type :=
  @prosa.model.processor.restricted_supply.processor_state Job.

Definition RsTarget (Job : Type) : Type :=
  ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_processor_state Job.

Definition rs_to_target (Job : eqType) (s : RsSource Job) : RsTarget Job :=
  match s with
  | prosa.model.processor.restricted_supply.Idle =>
      ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_processor_state_Idle Job
  | prosa.model.processor.restricted_supply.Active j =>
      ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_processor_state_Active Job j
  | prosa.model.processor.restricted_supply.Unavailable j =>
      ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_processor_state_Unavailable Job j
  | prosa.model.processor.restricted_supply.Inactive =>
      ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_processor_state_Inactive Job
  end.

Definition rs_to_source (Job : eqType) (s : RsTarget Job) : RsSource Job :=
  match s with
  | ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_processor_state_Idle =>
      @prosa.model.processor.restricted_supply.Idle Job
  | ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_processor_state_Active j =>
      @prosa.model.processor.restricted_supply.Active Job j
  | ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_processor_state_Unavailable j =>
      @prosa.model.processor.restricted_supply.Unavailable Job j
  | ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_processor_state_Inactive =>
      @prosa.model.processor.restricted_supply.Inactive Job
  end.

Definition RsStateRel (Job : eqType) (sR : RsSource Job)
    (sL : RsTarget Job) : SProp := Lean.eq (rs_to_target Job sR) sL.

Lemma rs_source_roundtrip (Job : eqType) (s : RsSource Job) :
  Logic.eq (rs_to_source Job (rs_to_target Job s)) s.
Proof. by destruct s. Qed.

Lemma rs_target_roundtrip (Job : eqType) (s : RsTarget Job) :
  RsStateRel Job (rs_to_source Job s) s.
Proof. destruct s; cbn; exact (@Lean.eq_refl _ _). Qed.

Record RsStateTypeCertificate (Job : eqType) : Type := {
  rs_state_source_roundtrip : forall s : RsSource Job,
    Logic.eq (rs_to_source Job (rs_to_target Job s)) s;
  rs_state_target_roundtrip : forall s : RsTarget Job,
    RsStateRel Job (rs_to_source Job s) s
}.

Definition rs_state_type_correspondence (Job : eqType) :
    RsStateTypeCertificate Job :=
  {| rs_state_source_roundtrip := rs_source_roundtrip Job;
     rs_state_target_roundtrip := rs_target_roundtrip Job |}.

Lemma rs_job_equality_truth (Job : eqType) (x y : Job) :
  PropSPropRel (is_true (x == y)) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - move/eqP=> H. exact (coq_eq_to_imported_eq x y H).
  - intro H. apply strictly_inhabits. apply/eqP.
    exact (imported_eq_to_coq_eq x y H).
Qed.

Definition rs_target_false_elim (Q : SProp)
    (H : ImportedRestrictedSupplyFull.False) : Q :=
  match H return Q with end.

Lemma rs_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedRestrictedSupplyFull.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  RsBoolRel bR (ImportedRestrictedSupplyFull.Decidable_decide Q d).
Proof.
  intro Hrel. unfold RsBoolRel.
  destruct d as [Hfalse | Htrue]; destruct bR; cbn.
  - exact (rs_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (rs_target_false_elim _ (rs_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Section ConcreteRestrictedSupply.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.restricted_supply.rs_processor_state Job.
  Let stateL :=
    ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_rs_processor_state
      Job (rs_decidable_eq Job).

  Local Transparent prosa.behavior.schedule.scheduled_on
    prosa.behavior.schedule.supply_on
    prosa.behavior.schedule.service_on.

  Definition rs_core_to_imported (_ : unit) : ImportedRestrictedSupplyFull.Unit :=
    ImportedRestrictedSupplyFull.Unit_unit.
  Definition rs_core_to_source (_ : ImportedRestrictedSupplyFull.Unit) : unit := tt.

  Lemma rs_scheduled_on_correspondence (j : Job) (s : RsSource Job) :
    RsBoolRel
      (@prosa.model.processor.restricted_supply.rs_scheduled_on Job j s)
      (ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_rs_scheduled_on
        Job (rs_decidable_eq Job) j (rs_to_target Job s)).
  Proof.
    destruct s as [|a|a|]; cbn;
      try exact (@Lean.eq_refl _ _);
      apply rs_decide_bool_correspondence;
      exact (rs_job_equality_truth Job a j).
  Qed.

  Lemma rs_supply_on_correspondence (s : RsSource Job) :
    SubNatRel
      (@prosa.model.processor.restricted_supply.rs_supply_on Job s)
      (ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_rs_supply_on
        Job (rs_decidable_eq Job) (rs_to_target Job s)).
  Proof. destruct s; cbn; exact (sub_nat_rel_canonical _). Qed.

  Lemma rs_service_on_correspondence (j : Job) (s : RsSource Job) :
    SubNatRel
      (@prosa.model.processor.restricted_supply.rs_service_on Job j s)
      (ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_rs_service_on
        Job (rs_decidable_eq Job) j (rs_to_target Job s)).
  Proof.
    destruct s as [|a|a|]; cbn;
      try exact (sub_nat_rel_canonical O).
    have Hdec := rs_decide_bool_correspondence
      (a == j) (Lean.eq a j) (rs_decidable_eq Job a j)
      (rs_job_equality_truth Job a j).
    unfold RsBoolRel in Hdec. destruct Hdec.
    destruct (a == j); cbn; exact (sub_nat_rel_canonical _).
  Qed.

  Lemma rs_instance_scheduled_field (j : Job) (s : RsSource Job) :
    RsBoolRel
      (@prosa.behavior.schedule.scheduled_on Job stateR j s tt)
      (ImportedRestrictedSupplyFull.scheduled_on0 Job (rs_decidable_eq Job)
        stateL j (rs_to_target Job s) ImportedRestrictedSupplyFull.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (rs_scheduled_on_correspondence j s).
  Qed.

  Lemma rs_instance_supply_field (s : RsSource Job) :
    SubNatRel
      (@prosa.behavior.schedule.supply_on Job stateR s tt)
      (ImportedRestrictedSupplyFull.supply_on0 Job (rs_decidable_eq Job)
        stateL (rs_to_target Job s) ImportedRestrictedSupplyFull.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (rs_supply_on_correspondence s).
  Qed.

  Lemma rs_instance_service_field (j : Job) (s : RsSource Job) :
    SubNatRel
      (@prosa.behavior.schedule.service_on Job stateR j s tt)
      (ImportedRestrictedSupplyFull.service_on0 Job (rs_decidable_eq Job)
        stateL j (rs_to_target Job s) ImportedRestrictedSupplyFull.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (rs_service_on_correspondence j s).
  Qed.

  Lemma rs_bool_false_correspondence (bR : bool)
      (bL : ImportedRestrictedSupplyFull.Bool) :
    RsBoolRel bR bL ->
    PropSPropRel (is_true (~~ bR))
      (Lean.eq bL ImportedRestrictedSupplyFull.Bool_false).
  Proof.
    intro Hb. apply prop_sprop_rel_intro.
    - intro Hfalse. destruct bR, bL; cbn in *.
      + discriminate Hfalse.
      + discriminate Hfalse.
      + exact (@Lean.eq_refl _ _).
      + exact (rs_false_elim _ (rs_false_ne_true Hb)).
    - intro Hfalse. destruct bR, bL; cbn in *.
      + exact (rs_false_elim _ (rs_false_ne_true
          (sub_imported_eq_sym _ _ Hb))).
      + exact (rs_false_elim _ (rs_false_ne_true
          (sub_imported_eq_sym _ _ Hfalse))).
      + exact (strictly_inhabits (Logic.eq_refl true)).
      + exact (rs_false_elim _ (rs_false_ne_true Hb)).
  Qed.

  Definition RsSupplyLawR : Prop :=
    forall (j : Job) (s : RsSource Job) (r : unit),
      is_true (leq
        (@prosa.model.processor.restricted_supply.rs_service_on Job j s)
        (@prosa.model.processor.restricted_supply.rs_supply_on Job s)).

  Definition RsSupplyLawL : SProp :=
    forall (j : Job) (s : RsTarget Job)
        (r : ImportedRestrictedSupplyFull.Unit),
      ImportedRestrictedSupplyFull.LE_le_inst1 Lean.Nat
        ImportedRestrictedSupplyFull.instLENat
        (ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_rs_service_on
          Job (rs_decidable_eq Job) j s)
        (ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_rs_supply_on
          Job (rs_decidable_eq Job) s).

  Lemma rs_supply_law_correspondence :
    PropSPropRel RsSupplyLawR RsSupplyLawL.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL rL. destruct rL.
      pose (sR := rs_to_source Job sL).
      have Hstate : Logic.eq (rs_to_target Job sR) sL :=
        imported_eq_to_coq_eq _ _ (rs_target_roundtrip Job sL).
      rewrite <- Hstate.
      exact (prop_to_sprop _ _
        (sub_nat_le_correspondence _ _ _ _
          (rs_service_on_correspondence j sR)
          (rs_supply_on_correspondence sR))
        (Hsource j sR tt)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR rR. destruct rR.
      exact (sprop_to_prop _ _
        (sub_nat_le_correspondence _ _ _ _
          (rs_service_on_correspondence j sR)
          (rs_supply_on_correspondence sR))
        (Htarget j (rs_to_target Job sR)
          ImportedRestrictedSupplyFull.Unit_unit)).
  Qed.

  Definition RsServiceRuleR : Prop :=
    forall (j : Job) (s : RsSource Job) (r : unit),
      is_true (~~ @prosa.model.processor.restricted_supply.rs_scheduled_on
        Job j s) ->
      Logic.eq
        (@prosa.model.processor.restricted_supply.rs_service_on Job j s) O.

  Definition RsServiceRuleL : SProp :=
    forall (j : Job) (s : RsTarget Job)
        (r : ImportedRestrictedSupplyFull.Unit),
      Lean.eq
        (ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_rs_scheduled_on
          Job (rs_decidable_eq Job) j s) ImportedRestrictedSupplyFull.Bool_false ->
      Lean.eq
        (ImportedRestrictedSupplyFull.Prosa_Model_Processor_RestrictedSupply_rs_service_on
          Job (rs_decidable_eq Job) j s) Lean.Nat_zero.

  Lemma rs_service_rule_correspondence :
    PropSPropRel RsServiceRuleR RsServiceRuleL.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL rL Hfalse. destruct rL.
      pose (sR := rs_to_source Job sL).
      have Hstate : Logic.eq (rs_to_target Job sR) sL :=
        imported_eq_to_coq_eq _ _ (rs_target_roundtrip Job sL).
      rewrite <- Hstate in Hfalse |- *.
      have Hscheduled := rs_scheduled_on_correspondence j sR.
      have Hservice := rs_service_on_correspondence j sR.
      have HsourceFalse := sprop_to_prop _ _
        (rs_bool_false_correspondence _ _ Hscheduled) Hfalse.
      exact (prop_to_sprop _ _
        (sub_nat_eq_correspondence _ _ O Lean.Nat_zero
          Hservice (sub_nat_rel_canonical O))
        (Hsource j sR tt HsourceFalse)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR rR Hfalse. destruct rR.
      have Hscheduled := rs_scheduled_on_correspondence j sR.
      have Hservice := rs_service_on_correspondence j sR.
      have HtargetFalse := prop_to_sprop _ _
        (rs_bool_false_correspondence _ _ Hscheduled) Hfalse.
      exact (sprop_to_prop _ _
        (sub_nat_eq_correspondence _ _ O Lean.Nat_zero
          Hservice (sub_nat_rel_canonical O))
        (Htarget j (rs_to_target Job sR)
          ImportedRestrictedSupplyFull.Unit_unit HtargetFalse)).
  Qed.

  Record RsConcreteStateCertificate : Type := {
    rs_state_roundtrip_source : forall s : RsSource Job,
      Logic.eq (rs_to_source Job (rs_to_target Job s)) s;
    rs_state_roundtrip_target : forall s : RsTarget Job,
      RsStateRel Job (rs_to_source Job s) s;
    rs_core_roundtrip_source : forall c : unit,
      Logic.eq (rs_core_to_source (rs_core_to_imported c)) c;
    rs_core_roundtrip_target : forall c : ImportedRestrictedSupplyFull.Unit,
      Lean.eq (rs_core_to_imported (rs_core_to_source c)) c;
    rs_scheduled_field : forall j s, RsBoolRel
      (@prosa.behavior.schedule.scheduled_on Job stateR j s tt)
      (ImportedRestrictedSupplyFull.scheduled_on0 Job (rs_decidable_eq Job)
        stateL j (rs_to_target Job s) ImportedRestrictedSupplyFull.Unit_unit);
    rs_supply_field : forall s, SubNatRel
      (@prosa.behavior.schedule.supply_on Job stateR s tt)
      (ImportedRestrictedSupplyFull.supply_on0 Job (rs_decidable_eq Job)
        stateL (rs_to_target Job s) ImportedRestrictedSupplyFull.Unit_unit);
    rs_service_field : forall j s, SubNatRel
      (@prosa.behavior.schedule.service_on Job stateR j s tt)
      (ImportedRestrictedSupplyFull.service_on0 Job (rs_decidable_eq Job)
        stateL j (rs_to_target Job s) ImportedRestrictedSupplyFull.Unit_unit);
    rs_supply_law_field : PropSPropRel RsSupplyLawR RsSupplyLawL;
    rs_service_law_field : PropSPropRel RsServiceRuleR RsServiceRuleL
  }.

  Definition rs_processor_state_correspondence :
      RsConcreteStateCertificate :=
    {| rs_state_roundtrip_source := rs_source_roundtrip Job;
       rs_state_roundtrip_target := rs_target_roundtrip Job;
       rs_core_roundtrip_source := fun c =>
         match c with tt => Logic.eq_refl tt end;
       rs_core_roundtrip_target := fun c =>
         match c with ImportedRestrictedSupplyFull.PUnit_unit =>
           @Lean.eq_refl _ _ end;
       rs_scheduled_field := rs_instance_scheduled_field;
       rs_supply_field := rs_instance_supply_field;
       rs_service_field := rs_instance_service_field;
       rs_supply_law_field := rs_supply_law_correspondence;
       rs_service_law_field := rs_service_rule_correspondence |}.

End ConcreteRestrictedSupply.
