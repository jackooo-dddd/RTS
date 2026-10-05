From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.varspeed.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedVarspeedFull.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  VarspeedBaseAdapter.

Definition VsSource (Job : eqType) : Type :=
  @prosa.model.processor.varspeed.processor_state Job.

Definition VsTarget (Job : Type) : Type :=
  ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state Job.

Definition vs_to_target (Job : eqType) (s : VsSource Job) : VsTarget Job :=
  match s with
  | prosa.model.processor.varspeed.Idle speed =>
      ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state_Idle
        Job (sub_nat_to_imported speed)
  | prosa.model.processor.varspeed.Progress j speed =>
      ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state_Progress
        Job j (sub_nat_to_imported speed)
  end.

Definition vs_to_source (Job : eqType) (s : VsTarget Job) : VsSource Job :=
  match s with
  | ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state_Idle speed =>
      @prosa.model.processor.varspeed.Idle Job (sub_nat_to_rocq speed)
  | ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state_Progress j speed =>
      @prosa.model.processor.varspeed.Progress Job j (sub_nat_to_rocq speed)
  end.

Definition VsStateRel (Job : eqType) (sR : VsSource Job)
    (sL : VsTarget Job) : SProp := Lean.eq (vs_to_target Job sR) sL.

Lemma vs_source_roundtrip (Job : eqType) (s : VsSource Job) :
  Logic.eq (vs_to_source Job (vs_to_target Job s)) s.
Proof.
  destruct s as [speed|j speed]; cbn;
    rewrite sub_nat_rocq_roundtrip; reflexivity.
Qed.

Lemma vs_target_roundtrip (Job : eqType) (s : VsTarget Job) :
  VsStateRel Job (vs_to_source Job s) s.
Proof.
  destruct s as [speed|j speed]; cbn.
  - exact (sub_imported_eq_congr
      (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state_Idle Job)
      _ _ (sub_nat_imported_roundtrip speed)).
  - exact (sub_imported_eq_congr
      (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_processor_state_Progress
        Job j) _ _ (sub_nat_imported_roundtrip speed)).
Qed.

Record VsStateTypeCertificate (Job : eqType) : Type := {
  vs_state_source_roundtrip : forall s : VsSource Job,
    Logic.eq (vs_to_source Job (vs_to_target Job s)) s;
  vs_state_target_roundtrip : forall s : VsTarget Job,
    VsStateRel Job (vs_to_source Job s) s
}.

Definition vs_state_type_correspondence (Job : eqType) :
    VsStateTypeCertificate Job :=
  {| vs_state_source_roundtrip := vs_source_roundtrip Job;
     vs_state_target_roundtrip := vs_target_roundtrip Job |}.

Section ConcreteVarspeed.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.varspeed.pstate_instance Job.
  Let stateL :=
    ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_pstate_instance
      Job (vs_decidable_eq Job).

  Local Transparent prosa.behavior.schedule.scheduled_on
    prosa.behavior.schedule.supply_on
    prosa.behavior.schedule.service_on.

  Definition vs_core_to_imported (_ : unit) : ImportedVarspeedFull.Unit :=
    ImportedVarspeedFull.Unit_unit.
  Definition vs_core_to_source (_ : ImportedVarspeedFull.Unit) : unit := tt.

  Lemma vs_scheduled_on_correspondence (j : Job) (s : VsSource Job) :
    VsBoolRel
      (@prosa.model.processor.varspeed.varspeed_scheduled_on Job j s tt)
      (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_varspeed_scheduled_on
        Job (vs_decidable_eq Job) j (vs_to_target Job s)
        ImportedVarspeedFull.Unit_unit).
  Proof.
    destruct s as [speed|j' speed]; cbn.
    - exact (@Lean.eq_refl _ _).
    - apply vs_decide_bool_correspondence.
      exact (vs_job_equality_truth Job j' j).
  Qed.

  Lemma vs_supply_on_correspondence (s : VsSource Job) :
    SubNatRel
      (@prosa.model.processor.varspeed.varspeed_supply_on Job s tt)
      (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_varspeed_supply_on
        Job (vs_decidable_eq Job) (vs_to_target Job s)
        ImportedVarspeedFull.Unit_unit).
  Proof.
    destruct s as [speed|j' speed]; cbn;
      exact (sub_nat_rel_canonical speed).
  Qed.

  Lemma vs_service_on_correspondence (j : Job) (s : VsSource Job) :
    SubNatRel
      (@prosa.model.processor.varspeed.varspeed_service_on Job j s tt)
      (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_varspeed_service_on
        Job (vs_decidable_eq Job) j (vs_to_target Job s)
        ImportedVarspeedFull.Unit_unit).
  Proof.
    destruct s as [speed|j' speed]; cbn.
    - exact (sub_nat_rel_canonical O).
    - have Hdec := vs_decide_bool_correspondence
        (j' == j) (Lean.eq j' j) (vs_decidable_eq Job j' j)
        (vs_job_equality_truth Job j' j).
      unfold VsBoolRel in Hdec. destruct Hdec.
      destruct (j' == j); cbn; exact (sub_nat_rel_canonical _).
  Qed.

  Lemma vs_instance_scheduled_field (j : Job) (s : VsSource Job) :
    VsBoolRel
      (@prosa.behavior.schedule.scheduled_on Job stateR j s tt)
      (ImportedVarspeedFull.scheduled_on0 Job (vs_decidable_eq Job)
        stateL j (vs_to_target Job s) ImportedVarspeedFull.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (vs_scheduled_on_correspondence j s).
  Qed.

  Lemma vs_instance_supply_field (s : VsSource Job) :
    SubNatRel
      (@prosa.behavior.schedule.supply_on Job stateR s tt)
      (ImportedVarspeedFull.supply_on0 Job (vs_decidable_eq Job)
        stateL (vs_to_target Job s) ImportedVarspeedFull.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (vs_supply_on_correspondence s).
  Qed.

  Lemma vs_instance_service_field (j : Job) (s : VsSource Job) :
    SubNatRel
      (@prosa.behavior.schedule.service_on Job stateR j s tt)
      (ImportedVarspeedFull.service_on0 Job (vs_decidable_eq Job)
        stateL j (vs_to_target Job s) ImportedVarspeedFull.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (vs_service_on_correspondence j s).
  Qed.

  Definition VsSupplyLawR : Prop :=
    forall (j : Job) (s : VsSource Job) (r : unit),
      is_true (leq
        (@prosa.model.processor.varspeed.varspeed_service_on Job j s r)
        (@prosa.model.processor.varspeed.varspeed_supply_on Job s r)).

  Definition VsSupplyLawL : SProp :=
    forall (j : Job) (s : VsTarget Job)
        (r : ImportedVarspeedFull.Unit),
      ImportedVarspeedFull.LE_le_inst1 Lean.Nat
        ImportedVarspeedFull.instLENat
        (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_varspeed_service_on
          Job (vs_decidable_eq Job) j s r)
        (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_varspeed_supply_on
          Job (vs_decidable_eq Job) s r).

  Lemma vs_supply_law_correspondence :
    PropSPropRel VsSupplyLawR VsSupplyLawL.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL rL. destruct rL.
      pose (sR := vs_to_source Job sL).
      have Hstate : Logic.eq (vs_to_target Job sR) sL :=
        imported_eq_to_coq_eq _ _ (vs_target_roundtrip Job sL).
      rewrite <- Hstate.
      exact (prop_to_sprop _ _
        (sub_nat_le_correspondence _ _ _ _
          (vs_service_on_correspondence j sR)
          (vs_supply_on_correspondence sR))
        (Hsource j sR tt)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR rR. destruct rR.
      exact (sprop_to_prop _ _
        (sub_nat_le_correspondence _ _ _ _
          (vs_service_on_correspondence j sR)
          (vs_supply_on_correspondence sR))
        (Htarget j (vs_to_target Job sR)
          ImportedVarspeedFull.Unit_unit)).
  Qed.

  Definition VsServiceRuleR : Prop :=
    forall (j : Job) (s : VsSource Job) (r : unit),
      is_true (~~ @prosa.model.processor.varspeed.varspeed_scheduled_on
        Job j s r) ->
      Logic.eq
        (@prosa.model.processor.varspeed.varspeed_service_on Job j s r) O.

  Definition VsServiceRuleL : SProp :=
    forall (j : Job) (s : VsTarget Job)
        (r : ImportedVarspeedFull.Unit),
      Lean.eq
        (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_varspeed_scheduled_on
          Job (vs_decidable_eq Job) j s r) ImportedVarspeedFull.Bool_false ->
      Lean.eq
        (ImportedVarspeedFull.Prosa_Model_Processor_Varspeed_varspeed_service_on
          Job (vs_decidable_eq Job) j s r) Lean.Nat_zero.

  Lemma vs_service_rule_correspondence :
    PropSPropRel VsServiceRuleR VsServiceRuleL.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL rL Hfalse. destruct rL.
      pose (sR := vs_to_source Job sL).
      have Hstate : Logic.eq (vs_to_target Job sR) sL :=
        imported_eq_to_coq_eq _ _ (vs_target_roundtrip Job sL).
      rewrite <- Hstate in Hfalse |- *.
      have Hscheduled := vs_scheduled_on_correspondence j sR.
      have Hservice := vs_service_on_correspondence j sR.
      have HsourceFalse := sprop_to_prop _ _
        (vs_bool_false_correspondence _ _ Hscheduled) Hfalse.
      exact (prop_to_sprop _ _
        (sub_nat_eq_correspondence _ _ O Lean.Nat_zero
          Hservice (sub_nat_rel_canonical O))
        (Hsource j sR tt HsourceFalse)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR rR Hfalse. destruct rR.
      have Hscheduled := vs_scheduled_on_correspondence j sR.
      have Hservice := vs_service_on_correspondence j sR.
      have HtargetFalse := prop_to_sprop _ _
        (vs_bool_false_correspondence _ _ Hscheduled) Hfalse.
      exact (sprop_to_prop _ _
        (sub_nat_eq_correspondence _ _ O Lean.Nat_zero
          Hservice (sub_nat_rel_canonical O))
        (Htarget j (vs_to_target Job sR)
          ImportedVarspeedFull.Unit_unit HtargetFalse)).
  Qed.

  Record VsConcreteStateCertificate : Type := {
    vs_state_roundtrip_source : forall s : VsSource Job,
      Logic.eq (vs_to_source Job (vs_to_target Job s)) s;
    vs_state_roundtrip_target : forall s : VsTarget Job,
      VsStateRel Job (vs_to_source Job s) s;
    vs_core_roundtrip_source : forall c : unit,
      Logic.eq (vs_core_to_source (vs_core_to_imported c)) c;
    vs_core_roundtrip_target : forall c : ImportedVarspeedFull.Unit,
      Lean.eq (vs_core_to_imported (vs_core_to_source c)) c;
    vs_scheduled_field : forall j s, VsBoolRel
      (@prosa.behavior.schedule.scheduled_on Job stateR j s tt)
      (ImportedVarspeedFull.scheduled_on0 Job (vs_decidable_eq Job)
        stateL j (vs_to_target Job s) ImportedVarspeedFull.Unit_unit);
    vs_supply_field : forall s, SubNatRel
      (@prosa.behavior.schedule.supply_on Job stateR s tt)
      (ImportedVarspeedFull.supply_on0 Job (vs_decidable_eq Job)
        stateL (vs_to_target Job s) ImportedVarspeedFull.Unit_unit);
    vs_service_field : forall j s, SubNatRel
      (@prosa.behavior.schedule.service_on Job stateR j s tt)
      (ImportedVarspeedFull.service_on0 Job (vs_decidable_eq Job)
        stateL j (vs_to_target Job s) ImportedVarspeedFull.Unit_unit);
    vs_supply_law_field : PropSPropRel VsSupplyLawR VsSupplyLawL;
    vs_service_law_field : PropSPropRel VsServiceRuleR VsServiceRuleL
  }.

  Definition vs_processor_state_correspondence :
      VsConcreteStateCertificate :=
    {| vs_state_roundtrip_source := vs_source_roundtrip Job;
       vs_state_roundtrip_target := vs_target_roundtrip Job;
       vs_core_roundtrip_source := fun c =>
         match c with tt => Logic.eq_refl tt end;
       vs_core_roundtrip_target := fun c =>
         match c with ImportedVarspeedFull.PUnit_unit =>
           @Lean.eq_refl _ _ end;
       vs_scheduled_field := vs_instance_scheduled_field;
       vs_supply_field := vs_instance_supply_field;
       vs_service_field := vs_instance_service_field;
       vs_supply_law_field := vs_supply_law_correspondence;
       vs_service_law_field := vs_service_rule_correspondence |}.

End ConcreteVarspeed.
