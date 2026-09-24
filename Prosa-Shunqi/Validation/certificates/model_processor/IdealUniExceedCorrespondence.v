From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.processor.ideal_uni_exceed.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdealUniExceed.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  IdealUniExceedBaseAdapter IdealUniExceedSourceOperations.

(** The source inductive and the imported Lean inductive remain distinct.
    Constructor-preserving maps carry the explicit representation relation. *)
Definition IueSource (Job : eqType) : Type :=
  @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state Job.

Definition IueTarget (Job : Type) : Type :=
  ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job.

Definition iue_to_target (Job : eqType) (x : IueSource Job) :
    IueTarget Job :=
  match x with
  | prosa.model.processor.ideal_uni_exceed.NominalExecution j =>
      ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_NominalExecution Job j
  | prosa.model.processor.ideal_uni_exceed.ExceedanceExecution j =>
      ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_ExceedanceExecution Job j
  | prosa.model.processor.ideal_uni_exceed.Idle =>
      ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_Idle Job
  end.

Definition iue_to_source (Job : eqType) (x : IueTarget Job) :
    IueSource Job :=
  match x with
  | ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_NominalExecution j =>
      @prosa.model.processor.ideal_uni_exceed.NominalExecution Job j
  | ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_ExceedanceExecution j =>
      @prosa.model.processor.ideal_uni_exceed.ExceedanceExecution Job j
  | ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_Idle =>
      @prosa.model.processor.ideal_uni_exceed.Idle Job
  end.

Definition IueRel (Job : eqType) (xR : IueSource Job)
    (xL : IueTarget Job) : SProp :=
  Lean.eq (iue_to_target Job xR) xL.

Lemma iue_source_roundtrip (Job : eqType) (x : IueSource Job) :
  Logic.eq (iue_to_source Job (iue_to_target Job x)) x.
Proof. by destruct x. Qed.

Lemma iue_target_roundtrip (Job : eqType) (x : IueTarget Job) :
  IueRel Job (iue_to_source Job x) x.
Proof. destruct x; cbn; exact (@Lean.eq_refl _ _). Qed.

Lemma iue_equality_correspondence (Job : eqType)
    (xR yR : IueSource Job) (xL yL : IueTarget Job) :
  IueRel Job xR xL -> IueRel Job yR yL ->
  PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy.
    exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits.
    destruct Hx. destruct Hy.
    have Hdecoded := f_equal (iue_to_source Job)
      (imported_eq_to_coq_eq _ _ Hxy).
    rewrite (iue_source_roundtrip Job xR)
      (iue_source_roundtrip Job yR) in Hdecoded.
    exact Hdecoded.
Qed.

Definition IueBoolRel (bR : bool)
    (bL : ImportedIdealUniExceed.Bool) : SProp :=
  Lean.eq (iue_bool_to_imported bR) bL.

Definition iue_target_false_elim (Q : SProp)
    (H : ImportedIdealUniExceed.False) : Q :=
  match H return Q with end.

Lemma iue_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedIdealUniExceed.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  IueBoolRel bR (ImportedIdealUniExceed.Decidable_decide Q d).
Proof.
  intro Hrel. unfold IueBoolRel.
  destruct d as [Hfalse | Htrue]; destruct bR; cbn.
  - exact (iue_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (iue_target_false_elim _ (iue_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Lemma iue_job_equality_truth (Job : eqType) (x y : Job) :
  PropSPropRel (is_true (x == y)) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - move/eqP=> H. exact (coq_eq_to_imported_eq x y H).
  - intro H. apply strictly_inhabits. apply/eqP.
    exact (imported_eq_to_coq_eq x y H).
Qed.

Lemma iue_eqdef_correspondence (Job : eqType)
    (xR yR : IueSource Job) (xL yL : IueTarget Job) :
  IueRel Job xR xL -> IueRel Job yR yL ->
  IueBoolRel
    (@prosa.model.processor.ideal_uni_exceed.exceedance_processor_state_eqdef
      Job xR yR)
    (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_eqdef
      Job (iue_decidable_eq Job) xL yL).
Proof.
  intros Hx Hy. destruct Hx. destruct Hy.
  destruct xR as [a|a|]; destruct yR as [b|b|]; cbn;
    try exact (@Lean.eq_refl _ _);
    apply iue_decide_bool_correspondence;
    exact (iue_job_equality_truth Job a b).
Qed.

(** The source's [Equality.axiom] is an informative [reflect] value.  These
    two maps preserve both constructors rather than merely proving an iff. *)
Definition iue_reflect_forward (PR : Prop) (PL : SProp)
    (bR : bool) (bL : ImportedIdealUniExceed.Bool)
    (HP : PropSPropRel PR PL) (Hb : IueBoolRel bR bL) :
    reflect PR bR ->
    ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_BoolReflect PL bL.
Proof.
  destruct Hb. intro HR. destruct HR as [Htrue | Hfalse].
  - exact (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_BoolReflect_isTrue
      PL (prop_to_sprop _ _ HP Htrue)).
  - exact (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_BoolReflect_isFalse
      PL (fun HL => iue_coq_false_to_target
        (Hfalse (sprop_to_prop _ _ HP HL)))).
Defined.

Definition iue_reflect_backward_at_bool (PR : Prop) (PL : SProp)
    (HP : PropSPropRel PR PL) (bL : ImportedIdealUniExceed.Bool) :
    ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_BoolReflect PL bL ->
    reflect PR (iue_bool_to_rocq bL) :=
  fun HL =>
    match HL in
      ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_BoolReflect _ b
      return reflect PR (iue_bool_to_rocq b) with
    | ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_BoolReflect_isTrue Htrue =>
        ReflectT PR (sprop_to_prop _ _ HP Htrue)
    | ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_BoolReflect_isFalse Hfalse =>
        ReflectF PR (fun HR =>
          interpret_strict Logic.False
            (iue_target_false_elim _
              (Hfalse (prop_to_sprop _ _ HP HR))))
    end.

Definition iue_reflect_backward (PR : Prop) (PL : SProp)
    (bR : bool) (bL : ImportedIdealUniExceed.Bool)
    (HP : PropSPropRel PR PL) (Hb : IueBoolRel bR bL) :
    ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_BoolReflect PL bL ->
    reflect PR bR.
Proof.
  destruct Hb. destruct bR; cbn;
    exact (iue_reflect_backward_at_bool PR PL HP _).
Defined.

Definition IueReflectTypeRel (PR : Prop) (PL : SProp)
    (bR : bool) (bL : ImportedIdealUniExceed.Bool) : Type :=
  Datatypes.prod
    (reflect PR bR ->
      ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_BoolReflect PL bL)
    (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_BoolReflect PL bL ->
      reflect PR bR).

Definition iue_eqn_statement_correspondence (Job : eqType) :
  forall xR yR xL yL,
    IueRel Job xR xL -> IueRel Job yR yL ->
    IueReflectTypeRel
      (Logic.eq xR yR) (Lean.eq xL yL)
      (@prosa.model.processor.ideal_uni_exceed.exceedance_processor_state_eqdef
        Job xR yR)
      (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_eqdef
        Job (iue_decidable_eq Job) xL yL) :=
  fun xR yR xL yL Hx Hy =>
    let Hprop := iue_equality_correspondence Job xR yR xL yL Hx Hy in
    let Hbool := iue_eqdef_correspondence Job xR yR xL yL Hx Hy in
    Datatypes.pair
      (iue_reflect_forward _ _ _ _ Hprop Hbool)
      (iue_reflect_backward _ _ _ _ Hprop Hbool).

Section ConcreteExceedance.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.ideal_uni_exceed.exceedance_proc_state Job.
  Let stateL :=
    ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state
      Job (iue_decidable_eq Job).

  Local Transparent prosa.behavior.schedule.scheduled_on
    prosa.behavior.schedule.supply_on
    prosa.behavior.schedule.service_on.

  Definition iue_core_to_imported (_ : unit) : ImportedIdealUniExceed.Unit :=
    ImportedIdealUniExceed.Unit_unit.

  Definition iue_core_to_rocq (_ : ImportedIdealUniExceed.Unit) : unit := tt.

  Lemma iue_scheduled_on_correspondence (j : Job) (s : IueSource Job) :
    IueBoolRel
      (@prosa.model.processor.ideal_uni_exceed.exceedance_scheduled_on
        Job j s tt)
      (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_scheduled_on
        Job (iue_decidable_eq Job) j (iue_to_target Job s)
        ImportedIdealUniExceed.Unit_unit).
  Proof.
    destruct s as [a|a|]; cbn;
      try exact (@Lean.eq_refl _ _);
      apply iue_decide_bool_correspondence;
      exact (iue_job_equality_truth Job a j).
  Qed.

  Lemma iue_supply_on_correspondence (s : IueSource Job) :
    SubNatRel
      (@prosa.model.processor.ideal_uni_exceed.exceedance_supply_on
        Job s tt)
      (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_supply_on
        Job (iue_decidable_eq Job) (iue_to_target Job s)
        ImportedIdealUniExceed.Unit_unit).
  Proof.
    destruct s; cbn; exact (sub_nat_rel_canonical _).
  Qed.

  Lemma iue_service_on_correspondence (j : Job) (s : IueSource Job) :
    SubNatRel
      (@prosa.model.processor.ideal_uni_exceed.exceedance_service_on
        Job j s tt)
      (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_service_on
        Job (iue_decidable_eq Job) j (iue_to_target Job s)
        ImportedIdealUniExceed.Unit_unit).
  Proof.
    destruct s as [a|a|]; cbn;
      try exact (sub_nat_rel_canonical O).
    have Hdec := iue_decide_bool_correspondence
      (a == j) (Lean.eq a j) (iue_decidable_eq Job a j)
      (iue_job_equality_truth Job a j).
    unfold IueBoolRel in Hdec. destruct Hdec.
    destruct (a == j); cbn; exact (sub_nat_rel_canonical _).
  Qed.

  Lemma iue_instance_scheduled_field (j : Job) (s : IueSource Job) :
    IueBoolRel
      (@prosa.behavior.schedule.scheduled_on Job stateR j s tt)
      (ImportedIdealUniExceed.scheduled_on0 Job (iue_decidable_eq Job)
        stateL j (iue_to_target Job s) ImportedIdealUniExceed.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (iue_scheduled_on_correspondence j s).
  Qed.

  Lemma iue_instance_supply_field (s : IueSource Job) :
    SubNatRel
      (@prosa.behavior.schedule.supply_on Job stateR s tt)
      (ImportedIdealUniExceed.supply_on0 Job (iue_decidable_eq Job)
        stateL (iue_to_target Job s) ImportedIdealUniExceed.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (iue_supply_on_correspondence s).
  Qed.

  Lemma iue_instance_service_field (j : Job) (s : IueSource Job) :
    SubNatRel
      (@prosa.behavior.schedule.service_on Job stateR j s tt)
      (ImportedIdealUniExceed.service_on0 Job (iue_decidable_eq Job)
        stateL j (iue_to_target Job s) ImportedIdealUniExceed.Unit_unit).
  Proof.
    unfold stateR, stateL. cbn.
    exact (iue_service_on_correspondence j s).
  Qed.

  Lemma iue_bool_false_correspondence (bR : bool)
      (bL : ImportedIdealUniExceed.Bool) :
    IueBoolRel bR bL ->
    PropSPropRel (is_true (~~ bR))
      (Lean.eq bL ImportedIdealUniExceed.Bool_false).
  Proof.
    intro Hb. apply prop_sprop_rel_intro.
    - intro Hfalse. destruct bR, bL; cbn in *.
      + discriminate Hfalse.
      + discriminate Hfalse.
      + exact (@Lean.eq_refl _ _).
      + exact (iue_false_elim _ (iue_false_ne_true Hb)).
    - intro Hfalse. destruct bR, bL; cbn in *.
      + exact (iue_false_elim _ (iue_false_ne_true
          (sub_imported_eq_sym _ _ Hb))).
      + exact (iue_false_elim _ (iue_false_ne_true
          (sub_imported_eq_sym _ _ Hfalse))).
      + exact (strictly_inhabits (Logic.eq_refl true)).
      + exact (iue_false_elim _ (iue_false_ne_true Hb)).
  Qed.

  Definition IueSupplyLawR : Prop :=
    forall (j : Job) (s : IueSource Job) (r : unit),
      is_true (leq
        (@prosa.model.processor.ideal_uni_exceed.exceedance_service_on Job j s r)
        (@prosa.model.processor.ideal_uni_exceed.exceedance_supply_on Job s r)).

  Definition IueSupplyLawL : SProp :=
    forall (j : Job) (s : IueTarget Job)
        (r : ImportedIdealUniExceed.Unit),
      ImportedIdealUniExceed.LE_le_inst1 Lean.Nat
        ImportedIdealUniExceed.instLENat
        (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_service_on
          Job (iue_decidable_eq Job) j s r)
        (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_supply_on
          Job (iue_decidable_eq Job) s r).

  Lemma iue_supply_law_correspondence :
    PropSPropRel IueSupplyLawR IueSupplyLawL.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL rL.
      destruct rL. destruct sL as [x|x|].
      + exact (prop_to_sprop _ _
          (sub_nat_le_correspondence _ _ _ _
            (iue_service_on_correspondence j (@prosa.model.processor.ideal_uni_exceed.NominalExecution Job x))
            (iue_supply_on_correspondence (@prosa.model.processor.ideal_uni_exceed.NominalExecution Job x)))
          (Hsource j (@prosa.model.processor.ideal_uni_exceed.NominalExecution Job x) tt)).
      + exact (prop_to_sprop _ _
          (sub_nat_le_correspondence _ _ _ _
            (iue_service_on_correspondence j (@prosa.model.processor.ideal_uni_exceed.ExceedanceExecution Job x))
            (iue_supply_on_correspondence (@prosa.model.processor.ideal_uni_exceed.ExceedanceExecution Job x)))
          (Hsource j (@prosa.model.processor.ideal_uni_exceed.ExceedanceExecution Job x) tt)).
      + exact (prop_to_sprop _ _
          (sub_nat_le_correspondence _ _ _ _
            (iue_service_on_correspondence j (@prosa.model.processor.ideal_uni_exceed.Idle Job))
            (iue_supply_on_correspondence (@prosa.model.processor.ideal_uni_exceed.Idle Job)))
          (Hsource j (@prosa.model.processor.ideal_uni_exceed.Idle Job) tt)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR rR. destruct rR.
      exact (sprop_to_prop _ _
        (sub_nat_le_correspondence _ _ _ _
          (iue_service_on_correspondence j sR)
          (iue_supply_on_correspondence sR))
        (Htarget j (iue_to_target Job sR)
          ImportedIdealUniExceed.Unit_unit)).
  Qed.

  Definition IueServiceRuleR : Prop :=
    forall (j : Job) (s : IueSource Job) (r : unit),
      is_true (~~ @prosa.model.processor.ideal_uni_exceed.exceedance_scheduled_on
        Job j s r) ->
      Logic.eq
        (@prosa.model.processor.ideal_uni_exceed.exceedance_service_on Job j s r) O.

  Definition IueServiceRuleL : SProp :=
    forall (j : Job) (s : IueTarget Job)
        (r : ImportedIdealUniExceed.Unit),
      Lean.eq
        (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_scheduled_on
          Job (iue_decidable_eq Job) j s r) ImportedIdealUniExceed.Bool_false ->
      Lean.eq
        (ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_service_on
          Job (iue_decidable_eq Job) j s r) Lean.Nat_zero.

  Lemma iue_service_rule_correspondence :
    PropSPropRel IueServiceRuleR IueServiceRuleL.
  Proof.
    apply prop_sprop_rel_intro.
    - intros Hsource j sL rL Hfalse.
      destruct rL.
      pose (sR := iue_to_source Job sL).
      have Hstate : Logic.eq (iue_to_target Job sR) sL :=
        imported_eq_to_coq_eq _ _ (iue_target_roundtrip Job sL).
      rewrite <- Hstate in Hfalse |- *.
      have Hscheduled := iue_scheduled_on_correspondence j sR.
      have Hservice := iue_service_on_correspondence j sR.
      have HsourceFalse := sprop_to_prop _ _
        (iue_bool_false_correspondence _ _ Hscheduled) Hfalse.
      exact (prop_to_sprop _ _
        (sub_nat_eq_correspondence _ _ O Lean.Nat_zero
          Hservice (sub_nat_rel_canonical O))
        (Hsource j sR tt HsourceFalse)).
    - intro Htarget. apply strictly_inhabits.
      intros j sR rR Hfalse. destruct rR.
      have Hscheduled := iue_scheduled_on_correspondence j sR.
      have Hservice := iue_service_on_correspondence j sR.
      have HtargetFalse := prop_to_sprop _ _
        (iue_bool_false_correspondence _ _ Hscheduled) Hfalse.
      exact (sprop_to_prop _ _
        (sub_nat_eq_correspondence _ _ O Lean.Nat_zero
          Hservice (sub_nat_rel_canonical O))
        (Htarget j (iue_to_target Job sR)
          ImportedIdealUniExceed.Unit_unit HtargetFalse)).
  Qed.

  Record IueConcreteStateCertificate : Type := {
    iue_state_roundtrip_source : forall s : IueSource Job,
      Logic.eq (iue_to_source Job (iue_to_target Job s)) s;
    iue_state_roundtrip_target : forall s : IueTarget Job,
      IueRel Job (iue_to_source Job s) s;
    iue_core_roundtrip_source : forall c : unit,
      Logic.eq (iue_core_to_rocq (iue_core_to_imported c)) c;
    iue_core_roundtrip_target : forall c : ImportedIdealUniExceed.Unit,
      Lean.eq (iue_core_to_imported (iue_core_to_rocq c)) c;
    iue_scheduled_field : forall j s,
      IueBoolRel
        (@prosa.behavior.schedule.scheduled_on Job stateR j s tt)
        (ImportedIdealUniExceed.scheduled_on0
          Job (iue_decidable_eq Job) stateL j (iue_to_target Job s)
          ImportedIdealUniExceed.Unit_unit);
    iue_supply_field : forall s,
      SubNatRel
        (@prosa.behavior.schedule.supply_on Job stateR s tt)
        (ImportedIdealUniExceed.supply_on0
          Job (iue_decidable_eq Job) stateL (iue_to_target Job s)
          ImportedIdealUniExceed.Unit_unit);
    iue_service_field : forall j s,
      SubNatRel
        (@prosa.behavior.schedule.service_on Job stateR j s tt)
        (ImportedIdealUniExceed.service_on0
          Job (iue_decidable_eq Job) stateL j (iue_to_target Job s)
          ImportedIdealUniExceed.Unit_unit);
    iue_supply_law_field : PropSPropRel IueSupplyLawR IueSupplyLawL;
    iue_service_law_field : PropSPropRel IueServiceRuleR IueServiceRuleL
  }.

  Definition iue_processor_state_correspondence :
      IueConcreteStateCertificate :=
    {| iue_state_roundtrip_source := iue_source_roundtrip Job;
       iue_state_roundtrip_target := iue_target_roundtrip Job;
       iue_core_roundtrip_source := fun c =>
         match c with tt => Logic.eq_refl tt end;
       iue_core_roundtrip_target := fun c =>
         match c with ImportedIdealUniExceed.PUnit_unit =>
           @Lean.eq_refl _ _ end;
       iue_scheduled_field := iue_instance_scheduled_field;
       iue_supply_field := iue_instance_supply_field;
       iue_service_field := iue_instance_service_field;
       iue_supply_law_field := iue_supply_law_correspondence;
       iue_service_law_field := iue_service_rule_correspondence |}.
End ConcreteExceedance.

Print Assumptions iue_source_roundtrip.
Print Assumptions iue_target_roundtrip.
Print Assumptions iue_equality_correspondence.
Print Assumptions iue_job_equality_truth.
Print Assumptions iue_eqdef_correspondence.
Print Assumptions iue_eqn_statement_correspondence.
Print Assumptions iue_scheduled_on_correspondence.
Print Assumptions iue_supply_on_correspondence.
Print Assumptions iue_service_on_correspondence.
Print Assumptions iue_supply_law_correspondence.
Print Assumptions iue_service_rule_correspondence.
Print Assumptions iue_processor_state_correspondence.
Print Assumptions iue_instance_scheduled_field.
Print Assumptions iue_instance_supply_field.
Print Assumptions iue_instance_service_field.
