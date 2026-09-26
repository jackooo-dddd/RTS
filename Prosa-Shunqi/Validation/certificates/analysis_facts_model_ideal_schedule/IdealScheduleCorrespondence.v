From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import IdealScheduleSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdealSchedule ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedIdealSchedule.
Module S := IdealScheduleSemanticSource.IdealScheduleSemanticSource.

(** Statement correspondences for [analysis/facts/model/ideal/schedule.v].

    The processor model is fixed to the ideal uniprocessor on both sides.
    Ideal states ([option Job] / imported [Option Job]) are related by the
    constructor-preserving map [id_opt_to_imported] (with both roundtrips),
    the unit core by its unique value, and schedules functionally through
    the state map; all are covered in both directions.  Job arrivals are
    related by [ArJobArrivalRel] and covered by the accepted import/export
    totals; arrival sequences by [ArArrivalSequenceRel].

    Source-side closed forms of [scheduled_in]/[service_in]/[supply_in] on
    the ideal state are re-proved here from the definitions (not from the
    source lemmas).  Target-side closed forms come from the validation
    interface equations [production_ideal_{scheduled,service,supply}_in]
    (Lean-kernel proofs over the actual finite folds); the certified Lean
    theorems themselves are not used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators *)

Lemma id_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Lemma id_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma id_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma id_bool_eq_correspondence (bR cR : bool) (bL cL : I.Bool) :
  SvcBoolRel bR bL -> SvcBoolRel cR cL -> PropSPropRel (bR = cR) (Lean.eq bL cL).
Proof.
  intros Hb Hc. apply prop_sprop_rel_intro.
  - intro E. destruct E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hb) Hc).
  - intro E. apply strictly_inhabits.
    have EL := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hb (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hc))).
    destruct bR, cR; cbn in EL; solve [reflexivity | discriminate EL].
Qed.

Lemma id_nat_eq_correspondence (aR bR : nat) (aL bL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL -> PropSPropRel (aR = bR) (Lean.eq aL bL).
Proof. exact (sub_nat_eq_correspondence aR aL bR bL). Qed.

Lemma id_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p | q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intros [p | q]; apply strictly_inhabits.
    + left. exact (sprop_to_prop _ _ HP p).
    + right. exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma id_not_correspondence (P : Prop) (PL : SProp) :
  PropSPropRel P PL -> PropSPropRel (~ P) (I.Not PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros Hn p. exact (ar_coq_false_to_target (Hn (sprop_to_prop _ _ HP p))).
  - intro Hn. apply strictly_inhabits. intro p.
    exact (interpret_strict _ (ar_target_false_to_strict (Hn (prop_to_sprop _ _ HP p)))).
Qed.

Lemma id_exists_identity_correspondence (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x.
    exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma id_eq_identity_correspondence (T : Type) (x y : T) :
  PropSPropRel (x = y) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - exact (coq_eq_to_imported_eq x y).
  - intro H. apply strictly_inhabits. exact (imported_eq_to_coq_eq x y H).
Qed.

Lemma id_nat_of_bool_related (bR : bool) (bL : I.Bool) :
  SvcBoolRel bR bL -> SubNatRel (nat_of_bool bR) (I.Bool_toNat bL).
Proof.
  intro Hb. unfold SvcBoolRel in Hb. destruct Hb.
  destruct bR; cbn; [exact (sub_nat_rel_canonical 1) | exact (sub_nat_rel_canonical O)].
Qed.

(** ** Ideal states *)

Definition id_opt_to_imported {T : Type} (x : option T) : I.Option T :=
  match x with
  | None => I.Option_none T
  | Some j => I.Option_some T j
  end.

Definition id_opt_to_rocq {T : Type} (y : I.Option T) : option T :=
  match y with
  | I.Option_none => None
  | I.Option_some j => Some j
  end.

Definition IdOptRel {T : Type} (x : option T) (y : I.Option T) : SProp :=
  Lean.eq (id_opt_to_imported x) y.

Lemma id_opt_source_roundtrip {T : Type} (x : option T) :
  Logic.eq (id_opt_to_rocq (id_opt_to_imported x)) x.
Proof. by case: x. Qed.

Lemma id_opt_target_roundtrip {T : Type} (y : I.Option T) :
  Lean.eq (id_opt_to_imported (id_opt_to_rocq y)) y.
Proof. destruct y; cbn; exact (@Lean.eq_refl _ _). Qed.

Lemma id_opt_rel_canonical {T : Type} (x : option T) : IdOptRel x (id_opt_to_imported x).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma id_opt_rel_surjective {T : Type} (y : I.Option T) : IdOptRel (id_opt_to_rocq y) y.
Proof. exact (id_opt_target_roundtrip y). Qed.

Lemma id_opt_eq_correspondence {T : Type} (xR yR : option T) (xL yL : I.Option T) :
  IdOptRel xR xL -> IdOptRel yR yL -> PropSPropRel (xR = yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro E. destruct E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hx) Hy).
  - intro E. apply strictly_inhabits.
    have EL := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hx (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hy))).
    have ES := f_equal id_opt_to_rocq EL.
    rewrite !id_opt_source_roundtrip in ES. exact ES.
Qed.

Lemma id_option_some_eq_correspondence (T : eqType) (s : option T) (j : T) :
  PropSPropRel (is_true (s == Some j))
    (Lean.eq (id_opt_to_imported s) (I.Option_some T j)).
Proof.
  apply prop_sprop_rel_intro.
  - intro H. move/eqP: H => ->. exact (@Lean.eq_refl _ _).
  - intro H. apply strictly_inhabits.
    have Hcoq := imported_eq_to_coq_eq _ _ H.
    destruct s as [k|]; cbn in Hcoq.
    + injection Hcoq as Hkj. subst k. exact (eqxx (Some j)).
    + discriminate Hcoq.
Qed.

Lemma id_option_none_eq_related (T : eqType) (s : option T) :
  SvcBoolRel (s == None)
    (match id_opt_to_imported s with
     | I.Option_none => I.Bool_true
     | I.Option_some _ => I.Bool_false
     end).
Proof. destruct s; exact (@Lean.eq_refl _ _). Qed.

Section Ideal.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.

  Local Transparent prosa.behavior.schedule.scheduled_on prosa.behavior.schedule.service_on
    prosa.behavior.schedule.supply_on.

  (** *** Source-side closed forms, re-proved from the definitions *)

  Lemma id_src_scheduled_on (j : Job) (s : option Job) (c : unit) :
    @prosa.behavior.schedule.scheduled_on Job PSR j s c = (s == Some j).
  Proof. by []. Qed.

  Lemma id_src_scheduled_in (j : Job) (s : option Job) :
    @prosa.behavior.schedule.scheduled_in Job PSR j s = (s == Some j).
  Proof.
    rewrite /prosa.behavior.schedule.scheduled_in.
    apply/existsP/idP => [[c]|H].
    - by rewrite id_src_scheduled_on.
    - by exists tt; rewrite id_src_scheduled_on.
  Qed.

  Lemma id_src_service_in (j : Job) (s : option Job) :
    @prosa.behavior.schedule.service_in Job PSR j s = nat_of_bool (s == Some j).
  Proof.
    rewrite /prosa.behavior.schedule.service_in (big_pred1 tt) /=.
    all: try by case: (s == Some j).
    all: by case.
  Qed.

  Lemma id_src_supply_in (s : option Job) :
    @prosa.behavior.schedule.supply_in Job PSR s = S O.
  Proof.
    rewrite /prosa.behavior.schedule.supply_in (big_pred1 tt) //; by case.
  Qed.

  (** *** Target-side closed forms through the interface equations *)

  Lemma id_scheduled_in_related (j : Job) (sR : option Job) sL :
    IdOptRel sR sL ->
    SvcBoolRel (@prosa.behavior.schedule.scheduled_in Job PSR j sR)
      (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst4 Job dJ PSL j sL).
  Proof.
    intro Hs. destruct Hs. rewrite id_src_scheduled_in.
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_IdealScheduleInterface_production_ideal_scheduled_in Job dJ j _))).
    cbn. apply ar_decide_bool_correspondence.
    exact (id_option_some_eq_correspondence Job sR j).
  Qed.

  Lemma id_decide_state_related (j : Job) (sR : option Job) sL :
    IdOptRel sR sL -> forall d,
    SvcBoolRel (sR == Some j) (I.Decidable_decide (Lean.eq sL (I.Option_some Job j)) d).
  Proof.
    intros Hs d. destruct Hs. apply ar_decide_bool_correspondence.
    exact (id_option_some_eq_correspondence Job sR j).
  Qed.

  Lemma id_service_on_related (j : Job) (sR : option Job) sL cR cL :
    IdOptRel sR sL ->
    SubNatRel (@prosa.behavior.schedule.service_on Job PSR j sR cR)
      (I.Prosa_Behavior_Schedule_ProcessorState_service_on_inst2 Job dJ PSL j sL cL).
  Proof.
    intro Hs. destruct Hs. cbn.
    have Hb := id_decide_state_related j sR (id_opt_to_imported sR) (@Lean.eq_refl _ _)
      (I.Option_instDecidableEq Job dJ (id_opt_to_imported sR) (I.Option_some Job j)).
    unfold SvcBoolRel in Hb. revert Hb.
    generalize (I.Decidable_decide (Lean.eq (id_opt_to_imported sR) (I.Option_some Job j))
      (I.Option_instDecidableEq Job dJ (id_opt_to_imported sR) (I.Option_some Job j))).
    intros bL Hb. destruct Hb.
    change (opt_eq sR (Some j)) with (sR == Some j).
    destruct (sR == Some j); cbn;
      [exact (sub_nat_rel_canonical 1) | exact (sub_nat_rel_canonical O)].
  Qed.

  Lemma id_service_in_related (j : Job) (sR : option Job) sL :
    IdOptRel sR sL ->
    SubNatRel (@prosa.behavior.schedule.service_in Job PSR j sR)
      (I.Prosa_Behavior_Schedule_ProcessorState_service_in_inst4 Job dJ PSL j sL).
  Proof.
    intro Hs.
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_IdealScheduleInterface_production_ideal_service_in Job dJ j sL))).
    have H := id_service_on_related j sR sL tt I.Unit_unit Hs.
    rewrite id_src_service_in. change (nat_of_bool (sR == Some j)) with
      (@prosa.behavior.schedule.service_on Job PSR j sR tt).
    exact H.
  Qed.

  Lemma id_supply_in_related (sR : option Job) sL :
    IdOptRel sR sL ->
    SubNatRel (@prosa.behavior.schedule.supply_in Job PSR sR)
      (I.Prosa_Behavior_Schedule_ProcessorState_supply_in_inst4 Job dJ PSL sL).
  Proof.
    intro Hs.
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_IdealScheduleInterface_production_ideal_supply_in Job dJ sL))).
    rewrite id_src_supply_in. cbn. exact (sub_nat_rel_canonical 1).
  Qed.

  (** *** Covering states, cores, schedules *)

  Let cover_state :=
    id_forall_cover_sprop (option Job) (I.Option Job) IdOptRel
      id_opt_to_imported id_opt_to_rocq id_opt_rel_canonical id_opt_rel_surjective.

  Definition IdCoreRel (c : unit) (cL : I.PUnit) : SProp := Lean.eq I.Unit_unit cL.

  Lemma id_core_rel_surjective (cL : I.PUnit) : IdCoreRel tt cL.
  Proof. destruct cL. exact (@Lean.eq_refl _ _). Qed.

  Let cover_core :=
    id_forall_cover_sprop unit I.PUnit IdCoreRel (fun _ => I.Unit_unit) (fun _ => tt)
      (fun _ => @Lean.eq_refl _ _) id_core_rel_surjective.

  Definition IdScheduleRel (schedR : @prosa.behavior.schedule.schedule Job PSR)
      (schedL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL) : SProp :=
    forall tR tL, SubNatRel tR tL -> IdOptRel (schedR tR) (schedL tL).

  Definition id_schedule_to_target (schedR : @prosa.behavior.schedule.schedule Job PSR) :
      I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL :=
    fun tL => id_opt_to_imported (schedR (sub_nat_to_rocq tL)).

  Definition id_schedule_to_source (schedL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL) :
      @prosa.behavior.schedule.schedule Job PSR :=
    fun tR => id_opt_to_rocq (schedL (sub_nat_to_imported tR)).

  Lemma id_schedule_to_target_rel schedR : IdScheduleRel schedR (id_schedule_to_target schedR).
  Proof.
    intros tR tL Ht. unfold id_schedule_to_target.
    rewrite (id_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma id_schedule_to_source_rel schedL : IdScheduleRel (id_schedule_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. unfold id_schedule_to_source, IdOptRel.
    exact (sub_imported_eq_trans _ _ _ (id_opt_target_roundtrip _)
      (sub_imported_eq_congr schedL _ _ Ht)).
  Qed.

  Let cover_schedule :=
    id_forall_cover_sprop _ _ IdScheduleRel id_schedule_to_target id_schedule_to_source
      id_schedule_to_target_rel id_schedule_to_source_rel.

  (** *** Schedule-level operations *)

  Section Sched.
    Variable schedR : @prosa.behavior.schedule.schedule Job PSR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.
    Hypothesis Hsched : IdScheduleRel schedR schedL.

    Lemma id_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PSR schedR j tR)
        (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.scheduled_at.
      cbn [I.Prosa_Behavior_Service_scheduled_at_inst4].
      exact (id_scheduled_in_related j _ _ (Hsched tR tL Ht)).
    Qed.

    Lemma id_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service_at Job PSR schedR j tR)
        (I.Prosa_Behavior_Service_service_at_inst4 Job dJ PSL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.service_at.
      cbn [I.Prosa_Behavior_Service_service_at_inst4].
      exact (id_service_in_related j _ _ (Hsched tR tL Ht)).
    Qed.

    Lemma id_supply_at_related (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.model.processor.supply.supply_at Job PSR schedR tR)
        (I.Prosa_Model_Processor_Supply_supply_at_inst4 Job dJ PSL schedL tL).
    Proof.
      intro Ht. unfold prosa.model.processor.supply.supply_at.
      cbn [I.Prosa_Model_Processor_Supply_supply_at_inst4].
      exact (id_supply_in_related _ _ (Hsched tR tL Ht)).
    Qed.

    Lemma id_ideal_is_idle_related (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.model.processor.ideal.ideal_is_idle Job schedR tR)
        (I.Prosa_Model_Processor_Ideal_ideal_is_idle Job dJ schedL tL).
    Proof.
      intro Ht. have Hs := Hsched tR tL Ht. unfold IdOptRel in Hs.
      unfold prosa.model.processor.ideal.ideal_is_idle.
      unfold I.Prosa_Model_Processor_Ideal_ideal_is_idle.
      revert Hs. generalize (schedL tL). intros sL Hs.
      destruct Hs. destruct (schedR tR); cbn; exact (@Lean.eq_refl _ _).
    Qed.

    Lemma id_scheduled_at_state_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL -> forall d,
      SvcBoolRel (schedR tR == Some j)
        (I.Decidable_decide (Lean.eq (schedL tL) (I.Option_some Job j)) d).
    Proof. intros Ht d. exact (id_decide_state_related j _ _ (Hsched tR tL Ht) d). Qed.
  End Sched.

  (** *** Statements *)

  Definition src_ideal_proc_model_is_a_uniprocessor_model : Prop :=
    ltac:(body_of (fun s : S.statement_ideal_proc_model_is_a_uniprocessor_model => s Job)).
  Definition tgt_ideal_proc_model_is_a_uniprocessor_model : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_proc_model_is_a_uniprocessor_model Job dJ)).
  Theorem ideal_proc_model_is_a_uniprocessor_model_correspondence :
    PropSPropRel src_ideal_proc_model_is_a_uniprocessor_model tgt_ideal_proc_model_is_a_uniprocessor_model.
  Proof.
    unfold src_ideal_proc_model_is_a_uniprocessor_model, tgt_ideal_proc_model_is_a_uniprocessor_model.
    unfold prosa.model.processor.platform_properties.uniprocessor_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model_inst4].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply cover_schedule. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (id_scheduled_at_related sR sL Hs j1 _ _ Ht))|].
    apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (id_scheduled_at_related sR sL Hs j2 _ _ Ht))|].
    exact (id_eq_identity_correspondence Job j1 j2).
  Qed.

  Definition src_service_in_service_on : Prop :=
    ltac:(body_of (fun s : S.statement_service_in_service_on => s Job)).
  Definition tgt_service_in_service_on : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_service_in_service_on Job dJ)).
  Theorem service_in_service_on_correspondence :
    PropSPropRel src_service_in_service_on tgt_service_in_service_on.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply cover_state. intros sR sL Hs.
    exact (id_nat_eq_correspondence _ _ _ _ (id_service_in_related j _ _ Hs)
      (id_service_on_related j _ _ tt I.Unit_unit Hs)).
  Qed.

  Definition src_service_in_def : Prop :=
    ltac:(body_of (fun s : S.statement_service_in_def => s Job)).
  Definition tgt_service_in_def : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_service_in_def Job dJ)).
  Theorem service_in_def_correspondence : PropSPropRel src_service_in_def tgt_service_in_def.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply cover_state. intros sR sL Hs.
    exact (id_nat_eq_correspondence _ _ _ _ (id_service_in_related j _ _ Hs)
      (id_nat_of_bool_related _ _ (id_decide_state_related j _ _ Hs _))).
  Qed.

  Definition src_ideal_proc_model_ensures_ideal_progress : Prop :=
    ltac:(body_of (fun s : S.statement_ideal_proc_model_ensures_ideal_progress => s Job)).
  Definition tgt_ideal_proc_model_ensures_ideal_progress : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_proc_model_ensures_ideal_progress Job dJ)).
  Theorem ideal_proc_model_ensures_ideal_progress_correspondence :
    PropSPropRel src_ideal_proc_model_ensures_ideal_progress tgt_ideal_proc_model_ensures_ideal_progress.
  Proof.
    unfold src_ideal_proc_model_ensures_ideal_progress, tgt_ideal_proc_model_ensures_ideal_progress.
    unfold prosa.model.processor.platform_properties.ideal_progress_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model_inst4].
    apply ar_forall_identity_correspondence. intro j.
    apply cover_state. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (id_scheduled_in_related j _ _ Hs))|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (id_service_in_related j _ _ Hs)).
  Qed.

  Definition src_ideal_proc_model_provides_unit_service : Prop :=
    ltac:(body_of (fun s : S.statement_ideal_proc_model_provides_unit_service => s Job)).
  Definition tgt_ideal_proc_model_provides_unit_service : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_proc_model_provides_unit_service Job dJ)).
  Theorem ideal_proc_model_provides_unit_service_correspondence :
    PropSPropRel src_ideal_proc_model_provides_unit_service tgt_ideal_proc_model_provides_unit_service.
  Proof.
    unfold src_ideal_proc_model_provides_unit_service, tgt_ideal_proc_model_provides_unit_service.
    unfold prosa.model.processor.platform_properties.unit_service_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model_inst4].
    apply ar_forall_identity_correspondence. intro j.
    apply cover_state. intros sR sL Hs.
    exact (sub_nat_le_correspondence _ _ _ _ (id_service_in_related j _ _ Hs) (sub_nat_rel_canonical 1)).
  Qed.

  Definition src_ideal_proc_model_provides_unit_supply : Prop :=
    ltac:(body_of (fun s : S.statement_ideal_proc_model_provides_unit_supply => s Job)).
  Definition tgt_ideal_proc_model_provides_unit_supply : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_proc_model_provides_unit_supply Job dJ)).
  Theorem ideal_proc_model_provides_unit_supply_correspondence :
    PropSPropRel src_ideal_proc_model_provides_unit_supply tgt_ideal_proc_model_provides_unit_supply.
  Proof.
    unfold src_ideal_proc_model_provides_unit_supply, tgt_ideal_proc_model_provides_unit_supply.
    unfold prosa.model.processor.platform_properties.unit_supply_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model_inst4].
    apply cover_state. intros sR sL Hs.
    exact (sub_nat_le_correspondence _ _ _ _ (id_supply_in_related _ _ Hs) (sub_nat_rel_canonical 1)).
  Qed.

  Definition src_scheduled_in_def : Prop :=
    ltac:(body_of (fun s : S.statement_scheduled_in_def => s Job)).
  Definition tgt_scheduled_in_def : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_scheduled_in_def Job dJ)).
  Theorem scheduled_in_def_correspondence : PropSPropRel src_scheduled_in_def tgt_scheduled_in_def.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply cover_state. intros sR sL Hs.
    exact (id_bool_eq_correspondence _ _ _ _ (id_scheduled_in_related j _ _ Hs)
      (id_decide_state_related j _ _ Hs _)).
  Qed.

  Definition src_scheduled_at_def : Prop :=
    ltac:(body_of (fun s : S.statement_scheduled_at_def => s Job)).
  Definition tgt_scheduled_at_def : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_scheduled_at_def Job dJ)).
  Theorem scheduled_at_def_correspondence : PropSPropRel src_scheduled_at_def tgt_scheduled_at_def.
  Proof.
    apply cover_schedule. intros sR sL Hs.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (id_bool_eq_correspondence _ _ _ _ (id_scheduled_at_related sR sL Hs j _ _ Ht)
      (id_scheduled_at_state_related sR sL Hs j _ _ Ht _)).
  Qed.

  Definition src_service_on_def : Prop :=
    ltac:(body_of (fun s : S.statement_service_on_def => s Job)).
  Definition tgt_service_on_def : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_service_on_def Job dJ)).
  Theorem service_on_def_correspondence : PropSPropRel src_service_on_def tgt_service_on_def.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply cover_state. intros sR sL Hs.
    apply cover_core. intros cR cL _.
    have Hon := id_service_on_related j _ _ cR cL Hs.
    change (@prosa.behavior.schedule.service_on Job PSR j sR cR)
      with (if sR == Some j then S O else O) in Hon.
    have E : (if sR == Some j then S O else O) = nat_of_bool (sR == Some j) by case: (sR == Some j).
    rewrite E in Hon.
    exact (id_nat_eq_correspondence _ _ _ _ Hon
      (id_nat_of_bool_related _ _ (id_decide_state_related j _ _ Hs _))).
  Qed.

  Definition src_service_at_def : Prop :=
    ltac:(body_of (fun s : S.statement_service_at_def => s Job)).
  Definition tgt_service_at_def : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_service_at_def Job dJ)).
  Theorem service_at_def_correspondence : PropSPropRel src_service_at_def tgt_service_at_def.
  Proof.
    apply cover_schedule. intros sR sL Hs.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (id_nat_eq_correspondence _ _ _ _ (id_service_at_related sR sL Hs j _ _ Ht)
      (id_nat_of_bool_related _ _ (id_scheduled_at_state_related sR sL Hs j _ _ Ht _))).
  Qed.

  Definition src_service_in_is_scheduled_in : Prop :=
    ltac:(body_of (fun s : S.statement_service_in_is_scheduled_in => s Job)).
  Definition tgt_service_in_is_scheduled_in : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_service_in_is_scheduled_in Job dJ)).
  Theorem service_in_is_scheduled_in_correspondence :
    PropSPropRel src_service_in_is_scheduled_in tgt_service_in_is_scheduled_in.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply cover_state. intros sR sL Hs.
    exact (id_nat_eq_correspondence _ _ _ _ (id_service_in_related j _ _ Hs)
      (id_nat_of_bool_related _ _ (id_scheduled_in_related j _ _ Hs))).
  Qed.

  Definition src_service_at_is_scheduled_at : Prop :=
    ltac:(body_of (fun s : S.statement_service_at_is_scheduled_at => s Job)).
  Definition tgt_service_at_is_scheduled_at : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_service_at_is_scheduled_at Job dJ)).
  Theorem service_at_is_scheduled_at_correspondence :
    PropSPropRel src_service_at_is_scheduled_at tgt_service_at_is_scheduled_at.
  Proof.
    apply cover_schedule. intros sR sL Hs.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (id_nat_eq_correspondence _ _ _ _ (id_service_at_related sR sL Hs j _ _ Ht)
      (id_nat_of_bool_related _ _ (id_scheduled_at_related sR sL Hs j _ _ Ht))).
  Qed.

  Definition src_ideal_proc_model_fully_consuming : Prop :=
    ltac:(body_of (fun s : S.statement_ideal_proc_model_fully_consuming => s Job)).
  Definition tgt_ideal_proc_model_fully_consuming : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_proc_model_fully_consuming Job dJ)).
  Theorem ideal_proc_model_fully_consuming_correspondence :
    PropSPropRel src_ideal_proc_model_fully_consuming tgt_ideal_proc_model_fully_consuming.
  Proof.
    unfold src_ideal_proc_model_fully_consuming, tgt_ideal_proc_model_fully_consuming.
    unfold prosa.model.processor.platform_properties.fully_consuming_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model_inst4].
    apply ar_forall_identity_correspondence. intro j.
    apply cover_schedule. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (id_scheduled_at_related sR sL Hs j _ _ Ht))|].
    exact (id_nat_eq_correspondence _ _ _ _ (id_service_at_related sR sL Hs j _ _ Ht)
      (id_supply_at_related sR sL Hs _ _ Ht)).
  Qed.

  Definition src_ideal_proc_has_supply : Prop :=
    ltac:(body_of (fun s : S.statement_ideal_proc_has_supply => s Job)).
  Definition tgt_ideal_proc_has_supply : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_proc_has_supply Job dJ)).
  Theorem ideal_proc_has_supply_correspondence :
    PropSPropRel src_ideal_proc_has_supply tgt_ideal_proc_has_supply.
  Proof.
    apply cover_schedule. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    unfold prosa.model.processor.supply.has_supply.
    cbn [I.Prosa_Model_Processor_Supply_has_supply_inst4].
    exact (svc_bool_truth_correspondence _ _
      (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (id_supply_at_related sR sL Hs _ _ Ht))).
  Qed.

  Definition src_ideal_proc_model_sched_case_analysis : Prop :=
    ltac:(body_of (fun s : S.statement_ideal_proc_model_sched_case_analysis => s Job)).
  Definition tgt_ideal_proc_model_sched_case_analysis : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_proc_model_sched_case_analysis Job dJ)).
  Theorem ideal_proc_model_sched_case_analysis_correspondence :
    PropSPropRel src_ideal_proc_model_sched_case_analysis tgt_ideal_proc_model_sched_case_analysis.
  Proof.
    apply cover_schedule. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply id_or_correspondence.
    - exact (svc_bool_truth_correspondence _ _ (id_ideal_is_idle_related sR sL Hs _ _ Ht)).
    - apply id_exists_identity_correspondence. intro j.
      exact (svc_bool_truth_correspondence _ _ (id_scheduled_at_related sR sL Hs j _ _ Ht)).
  Qed.

  Definition src_ideal_sched_implies_not_idle : Prop :=
    ltac:(body_of (fun s : S.statement_ideal_sched_implies_not_idle => s Job)).
  Definition tgt_ideal_sched_implies_not_idle : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_sched_implies_not_idle Job dJ)).
  Theorem ideal_sched_implies_not_idle_correspondence :
    PropSPropRel src_ideal_sched_implies_not_idle tgt_ideal_sched_implies_not_idle.
  Proof.
    apply cover_schedule. intros sR sL Hs.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (id_scheduled_at_related sR sL Hs j _ _ Ht))|].
    apply id_not_correspondence.
    exact (svc_bool_truth_correspondence _ _ (id_ideal_is_idle_related sR sL Hs _ _ Ht)).
  Qed.

  Definition src_ideal_not_idle_implies_sched : Prop :=
    ltac:(body_of (fun s : S.statement_ideal_not_idle_implies_sched => s Job)).
  Definition tgt_ideal_not_idle_implies_sched : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_ideal_not_idle_implies_sched Job dJ)).
  Theorem ideal_not_idle_implies_sched_correspondence :
    PropSPropRel src_ideal_not_idle_implies_sched tgt_ideal_not_idle_implies_sched.
  Proof.
    apply cover_schedule. intros sR sL Hs.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (id_ideal_is_idle_related sR sL Hs _ _ Ht))|].
    exact (id_nat_eq_correspondence _ _ _ _ (id_service_at_related sR sL Hs j _ _ Ht) (sub_nat_rel_canonical O)).
  Qed.

  (** *** Relation to the generic scheduled job *)

  Section Generic.
    Variable schedR : @prosa.behavior.schedule.schedule Job PSR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.
    Hypothesis Hsched : IdScheduleRel schedR schedL.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Lemma id_scheduled_jobs_at_related (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      ArListRel (@prosa.model.schedule.scheduled.scheduled_jobs_at Job PSR arrR schedR tR)
        (I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at_inst4 Job dJ PSL arrL schedL tL).
    Proof.
      intro Ht. unfold prosa.model.schedule.scheduled.scheduled_jobs_at.
      cbn [I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at_inst4].
      apply ar_filter_related.
      - intro j. exact (id_scheduled_at_related schedR schedL Hsched j tR tL Ht).
      - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr tR tL Ht).
    Qed.

    Lemma id_scheduled_job_at_related (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      IdOptRel (@prosa.model.schedule.scheduled.scheduled_job_at Job PSR arrR schedR tR)
        (I.Prosa_Model_Schedule_Scheduled_scheduled_job_at_inst4 Job dJ PSL arrL schedL tL).
    Proof.
      intro Ht. unfold prosa.model.schedule.scheduled.scheduled_job_at.
      cbn [I.Prosa_Model_Schedule_Scheduled_scheduled_job_at_inst4].
      have Hxs := id_scheduled_jobs_at_related tR tL Ht.
      unfold IdOptRel, ArListRel in *.
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_congr (I.List_head__q Job) _ _ Hxs)).
      destruct (@prosa.model.schedule.scheduled.scheduled_jobs_at Job PSR arrR schedR tR) as [|x xs];
        cbn; exact (@Lean.eq_refl _ _).
    Qed.

    Lemma id_is_idle_related (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.model.schedule.scheduled.is_idle Job PSR arrR schedR tR)
        (I.Prosa_Model_Schedule_Scheduled_is_idle_inst4 Job dJ PSL arrL schedL tL).
    Proof.
      intro Ht. unfold prosa.model.schedule.scheduled.is_idle.
      cbn [I.Prosa_Model_Schedule_Scheduled_is_idle_inst4].
      have Hxs := id_scheduled_jobs_at_related tR tL Ht.
      unfold SvcBoolRel, ArListRel in *.
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_congr (I.List_isEmpty Job) _ _ Hxs)).
      destruct (@prosa.model.schedule.scheduled.scheduled_jobs_at Job PSR arrR schedR tR) as [|x xs].
      - exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ScheduledInterface_production_isEmpty_nil Job)).
      - exact (sub_imported_eq_sym _ _
          (I.Prosa_Validation_ScheduledInterface_production_isEmpty_cons Job x (ar_list_to_imported xs))).
    Qed.

    Section Arrival.
      Variable jaR : prosa.behavior.job.JobArrival Job.
      Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
      Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

      Lemma id_jobs_come_from_related :
        PropSPropRel (@prosa.behavior.ready.jobs_come_from_arrival_sequence Job PSR schedR arrR)
          (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job dJ PSL schedL arrL).
      Proof.
        unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
        cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (id_scheduled_at_related schedR schedL Hsched j _ _ Ht))|].
        exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      Qed.

      Lemma id_jobs_must_arrive_related :
        PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PSR schedR)
          (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job dJ jaL PSL schedL).
      Proof.
        unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
        cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (id_scheduled_at_related schedR schedL Hsched j _ _ Ht))|].
        exact (ar_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
      Qed.
    End Arrival.
  End Generic.

  Definition id_arrival_sequence_to_source
      (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ) :
      prosa.behavior.arrival_sequence.arrival_sequence Job :=
    fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

  Lemma id_arrival_sequence_to_source_rel arrL :
    ArArrivalSequenceRel Job (id_arrival_sequence_to_source arrL) arrL.
  Proof.
    intros tR tL Ht. unfold ArListRel, id_arrival_sequence_to_source.
    refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
    exact (sub_imported_eq_congr arrL _ _ Ht).
  Qed.

  Let cover_arrival_sequence :=
    id_forall_cover_sprop _ _ (ArArrivalSequenceRel Job)
      (ar_arrival_sequence_to_imported Job) id_arrival_sequence_to_source
      (ar_arrival_sequence_canonical Job) id_arrival_sequence_to_source_rel.

  Let cover_job_arrival :=
    id_forall_cover_sprop _ _ (ArJobArrivalRel Job)
      (svc_import_job_arrival Job) (svc_export_job_arrival Job)
      (svc_job_arrival_import Job) (svc_job_arrival_export Job).

  Definition src_scheduled_job_at_def : Prop :=
    ltac:(body_of (fun s : S.statement_scheduled_job_at_def => s Job)).
  Definition tgt_scheduled_job_at_def : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_scheduled_job_at_def Job dJ)).
  Theorem scheduled_job_at_def_correspondence :
    PropSPropRel src_scheduled_job_at_def tgt_scheduled_job_at_def.
  Proof.
    apply cover_arrival_sequence. intros arrR arrL Harr.
    apply cover_job_arrival. intros jaR jaL Hja.
    apply cover_schedule. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (id_jobs_come_from_related sR sL Hs arrR arrL Harr)|].
    apply ar_imp_correspondence; [exact (id_jobs_must_arrive_related sR sL Hs jaR jaL Hja)|].
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (id_opt_eq_correspondence _ _ _ _ (id_scheduled_job_at_related sR sL Hs arrR arrL Harr _ _ Ht)
      (Hs tR tL Ht)).
  Qed.

  Definition src_is_idle_def : Prop :=
    ltac:(body_of (fun s : S.statement_is_idle_def => s Job)).
  Definition tgt_is_idle_def : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_Schedule_is_idle_def Job dJ)).
  Theorem is_idle_def_correspondence : PropSPropRel src_is_idle_def tgt_is_idle_def.
  Proof.
    apply cover_arrival_sequence. intros arrR arrL Harr.
    apply cover_job_arrival. intros jaR jaL Hja.
    apply cover_schedule. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (id_jobs_come_from_related sR sL Hs arrR arrL Harr)|].
    apply ar_imp_correspondence; [exact (id_jobs_must_arrive_related sR sL Hs jaR jaL Hja)|].
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (id_bool_eq_correspondence _ _ _ _ (id_is_idle_related sR sL Hs arrR arrL Harr _ _ Ht)
      (id_ideal_is_idle_related sR sL Hs _ _ Ht)).
  Qed.
End Ideal.
