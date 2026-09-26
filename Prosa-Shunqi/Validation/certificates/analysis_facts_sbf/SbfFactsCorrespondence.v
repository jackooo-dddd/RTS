From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import analysis.facts.SBF.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSbfFacts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalSequenceBaseAdapter ArrivalSequenceOperations ArrivalSequenceCorrespondence
  SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations
  SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence
  PredCorrespondence
  FsScheduleBaseAdapter FsScheduleFiniteOperations FsScheduleCorrespondence
  FsProcessorStateCorrespondence FactsSupplyOperationCorrespondence
  FactsSupplyPlatformPropertiesCorrespondence.

Module I := ImportedSbfFacts.

(** Statement correspondences for the three lemmas of [analysis/facts/SBF.v].
    Ingredients are the accepted facts/behavior/supply chain (two-sided
    [SchProcessorStateRel], [unit_supply_proc_model], [blackout_during],
    schedule import/export) and the accepted sbf/pred chain
    ([valid_pred_sbf], [unit_supply_bound_function], [arrives_in]).
    Binders that the source quantifies after a hypothesis are covered in both
    directions; no source or target lemma is used. *)

(** ** Generic coverage combinators *)

Lemma sf_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
    (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b)
    (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a.
    exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma sf_forall_cover_prop (A B : Type) (Rel : A -> B -> Prop)
    (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b)
    (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a.
    exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

(** ** Predicate coverage (Job -> nat -> nat -> Prop vs ... -> SProp) *)

Inductive SfBox (Q : SProp) : Prop := sf_box : Q -> SfBox Q.

Definition sf_pred_to_target (Job : Type) (PR : Job -> nat -> nat -> Prop) :
    Job -> Lean.Nat -> Lean.Nat -> SProp :=
  fun j a b => StrictlyInhabited (PR j (sub_nat_to_rocq a) (sub_nat_to_rocq b)).

Definition sf_pred_to_source (Job : Type) (PL : Job -> Lean.Nat -> Lean.Nat -> SProp) :
    Job -> nat -> nat -> Prop :=
  fun j a b => SfBox (PL j (sub_nat_to_imported a) (sub_nat_to_imported b)).

Lemma sf_subnat_to_rocq (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := imported_eq_to_coq_eq _ _ H. destruct E.
  exact (sub_nat_rocq_roundtrip nR).
Qed.

Lemma sf_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma sf_pred_to_target_rel (Job : eqType) (PR : Job -> nat -> nat -> Prop) :
  PredPredicateRel Job PR (sf_pred_to_target Job PR).
Proof.
  intros j t1R t1L t2R t2L H1 H2. unfold sf_pred_to_target.
  rewrite (sf_subnat_to_rocq _ _ H1) (sf_subnat_to_rocq _ _ H2).
  apply prop_sprop_rel_intro.
  - exact strictly_inhabits.
  - intro H. apply H.
Qed.

Lemma sf_pred_to_source_rel (Job : eqType) (PL : Job -> Lean.Nat -> Lean.Nat -> SProp) :
  PredPredicateRel Job (sf_pred_to_source Job PL) PL.
Proof.
  intros j t1R t1L t2R t2L H1 H2. unfold sf_pred_to_source.
  apply prop_sprop_rel_intro.
  - intros [Hq].
    exact (sf_lean_transport (fun b => PL j t1L b) _ _ H2
      (sf_lean_transport (fun a => PL j a (sub_nat_to_imported t2R)) _ _ H1 Hq)).
  - intro Hq. apply strictly_inhabits. apply sf_box.
    exact (sf_lean_transport (fun b => PL j (sub_nat_to_imported t1R) b) _ _
      (sub_imported_eq_sym _ _ H2)
      (sf_lean_transport (fun a => PL j a t2L) _ _ (sub_imported_eq_sym _ _ H1) Hq)).
Qed.

(** ** SupplyBoundFunction class coverage *)

Definition sf_sbf_to_target (sR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction) :
    I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction :=
  I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_mk
    (fun n => sub_nat_to_imported (sR (sub_nat_to_rocq n))).

Definition sf_sbf_to_source (sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) :
    prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction :=
  fun n => sub_nat_to_rocq
    (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL
      (sub_nat_to_imported n)).

Lemma sf_sbf_to_target_rel sR : PredSbfClassRel sR (sf_sbf_to_target sR).
Proof.
  intros nR nL Hn. unfold SubNatRel. cbn.
  rewrite (sf_subnat_to_rocq _ _ Hn). exact (@Lean.eq_refl _ _).
Qed.

Lemma sf_sbf_to_source_rel sL : PredSbfClassRel (sf_sbf_to_source sL) sL.
Proof.
  intros nR nL Hn. unfold SubNatRel, sf_sbf_to_source.
  refine (sub_imported_eq_trans _ _ _ (sub_nat_imported_roundtrip _) _).
  exact (sub_imported_eq_congr
    (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL) _ _ Hn).
Qed.

(** ** Arrival-sequence coverage *)

Definition sf_arrival_sequence_to_source (T : eqType)
    (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence T (ar_decidable_eq T)) :
    prosa.behavior.arrival_sequence.arrival_sequence T :=
  fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

Lemma sf_arrival_sequence_to_source_rel (T : eqType) arrL :
  ArArrivalSequenceRel T (sf_arrival_sequence_to_source T arrL) arrL.
Proof.
  intros tR tL Ht. unfold ArListRel, sf_arrival_sequence_to_source.
  refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
  exact (sub_imported_eq_congr arrL _ _ Ht).
Qed.

(** ** The supply observation of a two-sided processor-state relation *)

Definition sf_supply_of_sch (Job : eqType)
    (PStateR : prosa.behavior.schedule.ProcessorState Job)
    (PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job (sch_decidable_eq Job))
    (R : SchProcessorStateRel Job PStateR PStateL) :
    SupplyProcessorStateRel Job PStateR PStateL :=
  {| supply_ps_state_rel := sch_ps_state_rel Job PStateR PStateL R;
     supply_ps_core_to_target := sch_ps_core_to_target Job PStateR PStateL R;
     supply_ps_core_enumeration_rel := sch_ps_core_enumeration_rel Job PStateR PStateL R;
     supply_ps_supply_on_rel := sch_ps_supply_on_rel Job PStateR PStateL R |}.

Section SbfFacts.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    I.Prosa_Behavior_Schedule_ProcessorState Job (sch_decidable_eq Job).
  Variable R : SchProcessorStateRel Job PStateR PStateL.

  Let sbfL (s : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) :=
    I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function s.

  (** *** valid_pred_sbf_switch_predicate (all binders precede hypotheses) *)

  Section Switch.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job (sch_decidable_eq Job) PStateL.
    Hypothesis Hsched :
      SchScheduleRel Job PStateR PStateL (sch_ps_state_rel Job PStateR PStateL R) schedR schedL.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job).
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
    Variable sR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction.
    Variable sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction.
    Hypothesis Hs : PredSbfClassRel sR sL.
    Variables P1R P2R : Job -> nat -> nat -> Prop.
    Variables P1L P2L : Job -> Lean.Nat -> Lean.Nat -> SProp.
    Hypothesis HP1 : PredPredicateRel Job P1R P1L.
    Hypothesis HP2 : PredPredicateRel Job P2R P2L.

    Definition sf_switch_source : Prop :=
      (forall (j : Job) (t1 t2 : nat),
          prosa.behavior.arrival_sequence.arrives_in arrR j -> P2R j t1 t2 -> P1R j t1 t2) ->
      @prosa.analysis.definitions.sbf.pred.valid_pred_sbf Job PStateR arrR schedR P1R sR ->
      @prosa.analysis.definitions.sbf.pred.valid_pred_sbf Job PStateR arrR schedR P2R sR.

    Definition sf_switch_target : SProp :=
      (forall (j : Job) (t1 t2 : Lean.Nat),
          I.Prosa_Behavior_Arrival_sequence_arrives_in Job (sch_decidable_eq Job) arrL j ->
          P2L j t1 t2 -> P1L j t1 t2) ->
      I.Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf Job (sch_decidable_eq Job)
        PStateL arrL schedL P1L (sbfL sL) ->
      I.Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf Job (sch_decidable_eq Job)
        PStateL arrL schedL P2L (sbfL sL).

    Definition sf_switch_source_guard : sf_switch_source :=
      @valid_pred_sbf_switch_predicate Job PStateR arrR schedR sR P1R P2R.
    Definition sf_switch_target_guard : sf_switch_target :=
      @I.Prosa_Analysis_Facts_SBF_valid_pred_sbf_switch_predicate
        Job (sch_decidable_eq Job) PStateL arrL schedL sL P1L P2L.

    Theorem valid_pred_sbf_switch_predicate_correspondence :
      PropSPropRel sf_switch_source sf_switch_target.
    Proof.
      unfold sf_switch_source, sf_switch_target.
      apply ar_imp_correspondence.
      - apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros t1R t1L H1.
        apply ar_forall_nat_correspondence. intros t2R t2L H2.
        apply ar_imp_correspondence.
        + exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
        + apply ar_imp_correspondence.
          * exact (HP2 j t1R t1L t2R t2L H1 H2).
          * exact (HP1 j t1R t1L t2R t2L H1 H2).
      - apply ar_imp_correspondence.
        + exact (pred_valid_pred_sbf_correspondence Job PStateR PStateL
            (sf_supply_of_sch Job PStateR PStateL R) schedR schedL Hsched arrR arrL Harr
            P1R P1L HP1 sR (sbfL sL) Hs).
        + exact (pred_valid_pred_sbf_correspondence Job PStateR PStateL
            (sf_supply_of_sch Job PStateR PStateL R) schedR schedL Hsched arrR arrL Harr
            P2R P2L HP2 sR (sbfL sL) Hs).
    Qed.
  End Switch.
  (** *** blackout_during_bound_SBF: arr_seq, sched, P and SBF are bound after
      the unit-supply hypothesis and are covered in both directions. *)

  Definition sf_blackout_source : Prop :=
    @prosa.model.processor.platform_properties.unit_supply_proc_model Job PStateR ->
    forall (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job)
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (PR : Job -> nat -> nat -> Prop)
      (sR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction),
    @prosa.analysis.definitions.sbf.pred.valid_pred_sbf Job PStateR arrR schedR PR sR ->
    forall j : Job, prosa.behavior.arrival_sequence.arrives_in arrR j ->
    forall t1 t2 : nat, PR j t1 t2 ->
    forall d : nat, is_true (leq (addn t1 d) t2) ->
    is_true (leq (@prosa.model.processor.supply.blackout_during Job PStateR schedR t1 (addn t1 d))
      (subn d (sR d))).

  Definition sf_blackout_target : SProp :=
    I.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model
      Job (sch_decidable_eq Job) PStateL ->
    forall (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (sch_decidable_eq Job))
      (schedL : I.Prosa_Behavior_Schedule_schedule Job (sch_decidable_eq Job) PStateL)
      (PL : Job -> Lean.Nat -> Lean.Nat -> SProp)
      (sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction),
    I.Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf Job (sch_decidable_eq Job)
      PStateL arrL schedL PL (sbfL sL) ->
    forall j : Job,
    I.Prosa_Behavior_Arrival_sequence_arrives_in Job (sch_decidable_eq Job) arrL j ->
    forall t1 t2 : Lean.Nat, PL j t1 t2 ->
    forall d : Lean.Nat,
    ar_target_le (sub_imported_add t1 d) t2 ->
    ar_target_le
      (I.Prosa_Model_Processor_Supply_blackout_during Job (sch_decidable_eq Job)
        PStateL schedL t1 (sub_imported_add t1 d))
      (svc_target_sub d (sbfL sL d)).

  Definition sf_blackout_source_guard : sf_blackout_source :=
    @blackout_during_bound_SBF Job PStateR.
  Definition sf_blackout_target_guard : sf_blackout_target :=
    @I.Prosa_Analysis_Facts_SBF_blackout_during_bound_SBF Job (sch_decidable_eq Job) PStateL.

  Theorem blackout_during_bound_SBF_correspondence :
    PropSPropRel sf_blackout_source sf_blackout_target.
  Proof.
    unfold sf_blackout_source, sf_blackout_target.
    apply ar_imp_correspondence.
    { exact (fs_unit_supply_proc_model_correspondence Job PStateR PStateL R). }
    apply (sf_forall_cover_sprop _ _ (ArArrivalSequenceRel Job)
      (ar_arrival_sequence_to_imported Job) (sf_arrival_sequence_to_source Job)
      (ar_arrival_sequence_canonical Job) (sf_arrival_sequence_to_source_rel Job)).
    intros arrR arrL Harr.
    apply (sf_forall_cover_sprop _ _
      (SchScheduleRel Job PStateR PStateL (sch_ps_state_rel Job PStateR PStateL R))
      (import_schedule Job PStateR PStateL (sch_ps_state_to_target Job PStateR PStateL R))
      (export_schedule Job PStateR PStateL (sch_ps_state_to_source Job PStateR PStateL R))
      (schedule_import_certificate Job PStateR PStateL R)
      (schedule_export_certificate Job PStateR PStateL R)).
    intros schedR schedL Hsched.
    apply (sf_forall_cover_prop _ _ (PredPredicateRel Job)
      (sf_pred_to_target Job) (sf_pred_to_source Job)
      (sf_pred_to_target_rel Job) (sf_pred_to_source_rel Job)).
    intros PR PL HP.
    apply (sf_forall_cover_sprop _ _ PredSbfClassRel sf_sbf_to_target sf_sbf_to_source
      sf_sbf_to_target_rel sf_sbf_to_source_rel).
    intros sR sL Hs.
    apply ar_imp_correspondence.
    { exact (pred_valid_pred_sbf_correspondence Job PStateR PStateL
        (sf_supply_of_sch Job PStateR PStateL R) schedR schedL Hsched arrR arrL Harr
        PR PL HP sR (sbfL sL) Hs). }
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence.
    { exact (arrives_in_correspondence_certificate Job arrR arrL j Harr). }
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply ar_imp_correspondence.
    { exact (HP j t1R t1L t2R t2L H1 H2). }
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    have Hsum := sub_add_correspondence _ _ _ _ H1 Hd.
    apply ar_imp_correspondence.
    { exact (sub_nat_le_correspondence _ _ _ _ Hsum H2). }
    exact (sub_nat_le_correspondence _ _ _ _
      (fs_blackout_during_related Job PStateR PStateL R schedR schedL Hsched
        _ _ _ _ H1 Hsum)
      (svc_target_sub_related _ _ _ _ Hd (Hs dR dL Hd))).
  Qed.
End SbfFacts.

(** *** complement_SBF_monotone (only the SBF class is a parameter) *)

Section Complement.
  Variable sR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction.
  Variable sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction.
  Hypothesis Hs : PredSbfClassRel sR sL.
  Let fL := I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL.

  Definition sf_complement_source : Prop :=
    @prosa.analysis.definitions.sbf.pred.unit_supply_bound_function sR ->
    forall d1 d2 : nat, is_true (leq d1 d2) -> is_true (leq (subn d1 (sR d1)) (subn d2 (sR d2))).

  Definition sf_complement_target : SProp :=
    I.Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function fL ->
    forall d1 d2 : Lean.Nat, ar_target_le d1 d2 ->
    ar_target_le (svc_target_sub d1 (fL d1)) (svc_target_sub d2 (fL d2)).

  Definition sf_complement_source_guard : sf_complement_source :=
    @complement_SBF_monotone sR.
  Definition sf_complement_target_guard : sf_complement_target :=
    @I.Prosa_Analysis_Facts_SBF_complement_SBF_monotone sL.

  Theorem complement_SBF_monotone_correspondence :
    PropSPropRel sf_complement_source sf_complement_target.
  Proof.
    unfold sf_complement_source, sf_complement_target.
    apply ar_imp_correspondence.
    { exact (pred_unit_supply_bound_function_correspondence sR fL Hs). }
    apply ar_forall_nat_correspondence. intros d1R d1L H1.
    apply ar_forall_nat_correspondence. intros d2R d2L H2.
    apply ar_imp_correspondence.
    { exact (sub_nat_le_correspondence _ _ _ _ H1 H2). }
    exact (sub_nat_le_correspondence _ _ _ _
      (svc_target_sub_related _ _ _ _ H1 (Hs d1R d1L H1))
      (svc_target_sub_related _ _ _ _ H2 (Hs d2R d2L H2))).
  Qed.
End Complement.

Print Assumptions valid_pred_sbf_switch_predicate_correspondence.
Print Assumptions blackout_during_bound_SBF_correspondence.
Print Assumptions complement_SBF_monotone_correspondence.
