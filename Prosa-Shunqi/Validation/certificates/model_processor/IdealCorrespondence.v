From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.ideal.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdeal.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  IdealBaseAdapter.

(** The concrete Option/Unit carriers are related by constructor-preserving
    maps, not by claiming Rocq and imported Lean datatypes are identical. *)
Definition ideal_option_to_imported {T : Type} (x : option T) :
    ImportedIdeal.Option T :=
  match x with
  | None => ImportedIdeal.Option_none T
  | Some j => ImportedIdeal.Option_some T j
  end.

Definition IdealOptionRel {T : Type} (x : option T)
    (y : ImportedIdeal.Option T) : SProp :=
  Lean.eq (ideal_option_to_imported x) y.

Definition ideal_option_to_rocq {T : Type}
    (y : ImportedIdeal.Option T) : option T :=
  match y with
  | ImportedIdeal.Option_none => None
  | ImportedIdeal.Option_some j => Some j
  end.

Lemma ideal_option_source_roundtrip {T : Type} (x : option T) :
  Logic.eq
    (match ideal_option_to_imported x with
     | ImportedIdeal.Option_none => None
     | ImportedIdeal.Option_some j => Some j
     end) x.
Proof. by case: x. Qed.

Lemma ideal_option_target_surjective {T : Type}
    (y : ImportedIdeal.Option T) :
  IdealOptionRel
    (match y with
     | ImportedIdeal.Option_none => None
     | ImportedIdeal.Option_some j => Some j
     end) y.
Proof. destruct y; cbn; exact (@Lean.eq_refl _ _). Qed.

Lemma ideal_option_target_roundtrip {T : Type}
    (y : ImportedIdeal.Option T) :
  Lean.eq (ideal_option_to_imported (ideal_option_to_rocq y)) y.
Proof. destruct y; cbn; exact (@Lean.eq_refl _ _). Qed.

Definition ideal_target_false_elim (Q : SProp)
    (H : ImportedIdeal.False) : Q := match H return Q with end.

Lemma ideal_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedIdeal.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  IdealBoolRel b (ImportedIdeal.Decidable_decide Q d).
Proof.
  intro Hrel. unfold IdealBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (ideal_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (ideal_target_false_elim _ (ideal_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Lemma ideal_option_some_eq_correspondence (T : eqType)
    (s : option T) (j : T) :
  PropSPropRel (is_true (s == Some j))
    (Lean.eq (ideal_option_to_imported s)
      (ImportedIdeal.Option_some T j)).
Proof.
  apply prop_sprop_rel_intro.
  - intro H. move/eqP: H => ->. exact (@Lean.eq_refl _ _).
  - intro H. apply strictly_inhabits.
    have Hcoq := imported_eq_to_coq_eq _ _ H.
    destruct s as [k|]; cbn in Hcoq.
    + injection Hcoq as Hkj. subst k. exact (eqxx (Some j)).
    + discriminate Hcoq.
Qed.

Lemma ideal_bool_false_correspondence (bR : bool)
    (bL : ImportedIdeal.Bool) :
  IdealBoolRel bR bL ->
  PropSPropRel (is_true (~~ bR))
    (Lean.eq bL ImportedIdeal.Bool_false).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Hfalse. destruct bR, bL; cbn in *.
    + discriminate Hfalse.
    + discriminate Hfalse.
    + exact (@Lean.eq_refl _ _).
    + exact (ideal_false_elim _ (ideal_false_ne_true Hb)).
  - intro Hfalse. destruct bR, bL; cbn in *.
    + exact (ideal_false_elim _ (ideal_false_ne_true
        (sub_imported_eq_sym _ _ Hb))).
    + exact (ideal_false_elim _ (ideal_false_ne_true
        (sub_imported_eq_sym _ _ Hfalse))).
    + exact (strictly_inhabits (Logic.eq_refl true)).
    + exact (ideal_false_elim _ (ideal_false_ne_true Hb)).
Qed.

Section ConcreteIdeal.
  Context (Job : eqType).

  Let stateR := prosa.model.processor.ideal.processor_state Job.
  Let stateL := ImportedIdeal.Prosa_Model_Processor_Ideal_processor_state
    Job (ideal_decidable_eq Job).

  Definition IdealScheduleRel
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : ImportedIdeal.Prosa_Behavior_Schedule_schedule_inst4
        Job (ideal_decidable_eq Job) stateL) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      IdealOptionRel (schedR tR) (schedL tL).

  Local Transparent prosa.behavior.schedule.scheduled_on
    prosa.behavior.schedule.service_on.

  Lemma ideal_scheduled_on_correspondence
      (j : Job) (s : option Job) :
    IdealBoolRel
      (@prosa.behavior.schedule.scheduled_on Job stateR j s tt)
      (ImportedIdeal.scheduled_on0 Job (ideal_decidable_eq Job)
        stateL j (ideal_option_to_imported s) ImportedIdeal.Unit_unit).
  Proof.
    unfold stateR, stateL.
    cbn.
    apply ideal_decide_bool_correspondence.
    exact (ideal_option_some_eq_correspondence Job s j).
  Qed.

  Lemma ideal_supply_on_correspondence (s : option Job) :
    SubNatRel
      (@prosa.behavior.schedule.supply_on Job stateR s tt)
      (ImportedIdeal.supply_on0 Job (ideal_decidable_eq Job)
        stateL (ideal_option_to_imported s) ImportedIdeal.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (sub_nat_rel_canonical 1).
  Qed.

  Lemma ideal_service_on_correspondence (j : Job) (s : option Job) :
    SubNatRel
      (@prosa.behavior.schedule.service_on Job stateR j s tt)
      (ImportedIdeal.service_on0 Job (ideal_decidable_eq Job)
        stateL j (ideal_option_to_imported s) ImportedIdeal.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    have Hscheduled := ideal_scheduled_on_correspondence j s.
    unfold IdealBoolRel in Hscheduled.
    cbn in Hscheduled.
    destruct Hscheduled.
    destruct (opt_eq s (Some j)).
    - cbn.
      exact (sub_nat_rel_canonical 1).
    - cbn.
      exact (sub_nat_rel_canonical O).
  Qed.

  Definition IdealSupplyLawR : Prop :=
    forall (j : Job) (s : option Job) (r : unit),
      is_true (leq
        (@prosa.behavior.schedule.service_on Job stateR j s r)
        (@prosa.behavior.schedule.supply_on Job stateR s r)).

  Definition IdealSupplyLawL : SProp :=
    forall (j : Job) (s : ImportedIdeal.Option Job)
        (r : ImportedIdeal.Unit),
      ImportedIdeal.LE_le_inst1 Lean.Nat ImportedIdeal.instLENat
        (ImportedIdeal.service_on0 Job (ideal_decidable_eq Job)
          stateL j s r)
        (ImportedIdeal.supply_on0 Job (ideal_decidable_eq Job)
          stateL s r).

  Lemma ideal_supply_law_correspondence :
    PropSPropRel IdealSupplyLawR IdealSupplyLawL.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL rL.
      destruct rL. destruct sL as [|x].
      + exact (prop_to_sprop _ _
          (sub_nat_le_correspondence _ _ _ _
            (ideal_service_on_correspondence j None)
            (ideal_supply_on_correspondence None))
          (Hsource j None tt)).
      + exact (prop_to_sprop _ _
          (sub_nat_le_correspondence _ _ _ _
            (ideal_service_on_correspondence j (Some x))
            (ideal_supply_on_correspondence (Some x)))
          (Hsource j (Some x) tt)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR rR. destruct rR.
      exact (sprop_to_prop _ _
        (sub_nat_le_correspondence _ _ _ _
          (ideal_service_on_correspondence j sR)
          (ideal_supply_on_correspondence sR))
        (Htarget j (ideal_option_to_imported sR)
          ImportedIdeal.Unit_unit)).
  Qed.

  Definition IdealServiceRuleR : Prop :=
    forall (j : Job) (s : option Job) (r : unit),
      is_true (~~ @prosa.behavior.schedule.scheduled_on Job stateR j s r) ->
      Logic.eq (@prosa.behavior.schedule.service_on Job stateR j s r) O.

  Definition IdealServiceRuleL : SProp :=
    forall (j : Job) (s : ImportedIdeal.Option Job)
        (r : ImportedIdeal.Unit),
      Lean.eq
        (ImportedIdeal.scheduled_on0 Job (ideal_decidable_eq Job)
          stateL j s r) ImportedIdeal.Bool_false ->
      Lean.eq
        (ImportedIdeal.service_on0 Job (ideal_decidable_eq Job)
          stateL j s r) Lean.Nat_zero.

  Lemma ideal_service_rule_correspondence :
    PropSPropRel IdealServiceRuleR IdealServiceRuleL.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL rL.
      destruct rL. destruct sL as [|x].
      + intro Hfalse.
        have Hscheduled := ideal_scheduled_on_correspondence j None.
        have Hservice := ideal_service_on_correspondence j None.
        have HsourceFalse := sprop_to_prop _ _
          (ideal_bool_false_correspondence _ _ Hscheduled) Hfalse.
        exact (prop_to_sprop _ _
          (sub_nat_eq_correspondence _ _ O Lean.Nat_zero
            Hservice (sub_nat_rel_canonical O))
          (Hsource j None tt HsourceFalse)).
      + intro Hfalse.
        have Hscheduled := ideal_scheduled_on_correspondence j (Some x).
        have Hservice := ideal_service_on_correspondence j (Some x).
        have HsourceFalse := sprop_to_prop _ _
          (ideal_bool_false_correspondence _ _ Hscheduled) Hfalse.
        exact (prop_to_sprop _ _
          (sub_nat_eq_correspondence _ _ O Lean.Nat_zero
            Hservice (sub_nat_rel_canonical O))
          (Hsource j (Some x) tt HsourceFalse)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR rR Hfalse. destruct rR.
      have Hscheduled := ideal_scheduled_on_correspondence j sR.
      have Hservice := ideal_service_on_correspondence j sR.
      have HtargetFalse := prop_to_sprop _ _
        (ideal_bool_false_correspondence _ _ Hscheduled) Hfalse.
      exact (sprop_to_prop _ _
        (sub_nat_eq_correspondence _ _ O Lean.Nat_zero
          Hservice (sub_nat_rel_canonical O))
        (Htarget j (ideal_option_to_imported sR)
          ImportedIdeal.Unit_unit HtargetFalse)).
  Qed.

  Definition ideal_core_to_imported (_ : unit) : ImportedIdeal.Unit :=
    ImportedIdeal.Unit_unit.

  Definition ideal_core_to_rocq (_ : ImportedIdeal.Unit) : unit := tt.

  Record IdealConcreteStateCertificate : Type := {
    ideal_state_roundtrip_source : forall s : option Job,
      Logic.eq (ideal_option_to_rocq (ideal_option_to_imported s)) s;
    ideal_state_roundtrip_target : forall s : ImportedIdeal.Option Job,
      Lean.eq (ideal_option_to_imported (ideal_option_to_rocq s)) s;
    ideal_core_roundtrip_source : forall c : unit,
      Logic.eq (ideal_core_to_rocq (ideal_core_to_imported c)) c;
    ideal_core_roundtrip_target : forall c : ImportedIdeal.Unit,
      Lean.eq (ideal_core_to_imported (ideal_core_to_rocq c)) c;
    ideal_scheduled_field : forall j s,
      IdealBoolRel
        (@prosa.behavior.schedule.scheduled_on Job stateR j s tt)
        (ImportedIdeal.scheduled_on0 Job (ideal_decidable_eq Job)
          stateL j (ideal_option_to_imported s) ImportedIdeal.Unit_unit);
    ideal_supply_field : forall s,
      SubNatRel
        (@prosa.behavior.schedule.supply_on Job stateR s tt)
        (ImportedIdeal.supply_on0 Job (ideal_decidable_eq Job)
          stateL (ideal_option_to_imported s) ImportedIdeal.Unit_unit);
    ideal_service_field : forall j s,
      SubNatRel
        (@prosa.behavior.schedule.service_on Job stateR j s tt)
        (ImportedIdeal.service_on0 Job (ideal_decidable_eq Job)
          stateL j (ideal_option_to_imported s) ImportedIdeal.Unit_unit);
    ideal_supply_law_field :
      PropSPropRel IdealSupplyLawR IdealSupplyLawL;
    ideal_service_law_field :
      PropSPropRel IdealServiceRuleR IdealServiceRuleL
  }.

  Definition ideal_processor_state_correspondence :
      IdealConcreteStateCertificate :=
    {| ideal_state_roundtrip_source := ideal_option_source_roundtrip;
       ideal_state_roundtrip_target := ideal_option_target_roundtrip;
       ideal_core_roundtrip_source := fun c =>
         match c with tt => Logic.eq_refl tt end;
       ideal_core_roundtrip_target := fun c =>
         match c with ImportedIdeal.PUnit_unit => @Lean.eq_refl _ _ end;
       ideal_scheduled_field := ideal_scheduled_on_correspondence;
       ideal_supply_field := ideal_supply_on_correspondence;
       ideal_service_field := ideal_service_on_correspondence;
       ideal_supply_law_field := ideal_supply_law_correspondence;
       ideal_service_law_field := ideal_service_rule_correspondence |}.

  Lemma ideal_is_idle_correspondence
      (schedR : prosa.behavior.schedule.schedule stateR)
      (schedL : ImportedIdeal.Prosa_Behavior_Schedule_schedule_inst4
        Job (ideal_decidable_eq Job) stateL)
      (tR : nat) (tL : Lean.Nat) :
    IdealScheduleRel schedR schedL ->
    SubNatRel tR tL ->
    IdealBoolRel
      (@prosa.model.processor.ideal.ideal_is_idle Job schedR tR)
      (ImportedIdeal.Prosa_Model_Processor_Ideal_ideal_is_idle
        Job (ideal_decidable_eq Job) schedL tL).
  Proof.
    intros Hsched Htime.
    have Hstate := Hsched tR tL Htime.
    unfold IdealOptionRel in Hstate.
    unfold prosa.model.processor.ideal.ideal_is_idle.
    unfold ImportedIdeal.Prosa_Model_Processor_Ideal_ideal_is_idle.
    destruct (schedR tR) as [j|] eqn:Hsource.
    - cbn in Hstate.
      destruct Hstate. cbn. exact (@Lean.eq_refl _ _).
    - cbn in Hstate.
      destruct Hstate. cbn. exact (@Lean.eq_refl _ _).
  Qed.
End ConcreteIdeal.

Print Assumptions ideal_option_source_roundtrip.
Print Assumptions ideal_option_target_surjective.
Print Assumptions ideal_option_target_roundtrip.
Print Assumptions ideal_option_some_eq_correspondence.
Print Assumptions ideal_bool_false_correspondence.
Print Assumptions ideal_scheduled_on_correspondence.
Print Assumptions ideal_supply_on_correspondence.
Print Assumptions ideal_service_on_correspondence.
Print Assumptions ideal_supply_law_correspondence.
Print Assumptions ideal_service_rule_correspondence.
Print Assumptions ideal_processor_state_correspondence.
Print Assumptions ideal_is_idle_correspondence.
