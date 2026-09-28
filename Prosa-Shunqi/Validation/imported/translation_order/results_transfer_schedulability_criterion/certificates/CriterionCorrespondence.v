From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import CriterionSemanticSource.
From prosa Require Import model.processor.ideal model.processor.supply.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedCriterion ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedCriterion.
Module S := CriterionSemanticSource.CriterionSemanticSource.

(*CRITERION_HEADER*)

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


  (** *** Service, completion and remaining cost on the ideal processor *)

  Section Service.
    Variable schedR : @prosa.behavior.schedule.schedule Job PSR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.
    Hypothesis Hsched : IdScheduleRel schedR schedL.

    Lemma cr_service_at_fun (j : Job) :
      SvcNatFunRel (fun t => @prosa.behavior.service.service_at Job PSR schedR j t)
        (fun t => I.Prosa_Validation_ServiceInterface_serviceAtProjection_inst4 Job dJ PSL schedL j t).
    Proof.
      intros tR tL Ht. unfold prosa.behavior.service.service_at.
      exact (id_service_in_related j _ _ (Hsched tR tL Ht)).
    Qed.

    Lemma cr_service_during_related (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@prosa.behavior.service.service_during Job PSR schedR j t1R t2R)
        (I.Prosa_Behavior_Service_service_during_inst4 Job dJ PSL schedL j t1L t2L).
    Proof.
      intros H1 H2.
      exact (svc_interval_sum_related t1R t2R _ _ _ _ H1 H2 (cr_service_at_fun j)).
    Qed.

    Lemma cr_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service Job PSR schedR j tR)
        (I.Prosa_Behavior_Service_service_inst4 Job dJ PSL schedL j tL).
    Proof.
      intro Ht.
      exact (svc_interval_sum_related O tR _ tL _ _ (sub_nat_rel_canonical O) Ht (cr_service_at_fun j)).
    Qed.

    Variable costR : prosa.behavior.job.JobCost Job.
    Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
    Hypothesis Hcost : SvcJobCostRel Job costR costL.

    Lemma cr_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.completed_by Job PSR schedR costR j tR)
        (I.Prosa_Behavior_Service_completed_by_inst4 Job dJ PSL schedL costL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.completed_by.
      cbn [I.Prosa_Behavior_Service_completed_by_inst4].
      exact (svc_decide_le_related _ _ _ _ (Hcost j) (cr_service_related j tR tL Ht)).
    Qed.

    Lemma cr_remaining_cost_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.remaining_cost Job PSR schedR costR j tR)
        (I.Prosa_Behavior_Service_remaining_cost_inst4 Job dJ PSL schedL costL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.remaining_cost.
      cbn [I.Prosa_Behavior_Service_remaining_cost_inst4].
      exact (svc_target_sub_related _ _ _ _ (Hcost j) (cr_service_related j tR tL Ht)).
    Qed.

    Lemma cr_cde_rel :
      PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PSR schedR costR)
        (I.Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job dJ PSL schedL costL).
    Proof.
      unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4].
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (id_scheduled_at_related schedR schedL Hsched j tR tL Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _ (cr_service_related j tR tL Ht) (Hcost j)).
    Qed.
  End Service.

End Ideal.

(** ** Sequence sums, finite quantifiers and list equality *)

Lemma cr_big_seq_as_fold {T : Type} (xs : seq T) (f : T -> nat) :
  Logic.eq (\sum_(x <- xs) f x) (foldr addn O (map f xs)).
Proof.
  elim: xs => [|x tail IH].
  - rewrite big_nil. reflexivity.
  - rewrite big_cons. cbn [map foldr]. now rewrite IH.
Qed.

Section Sums.
  Context {T : Type}.
  Variable fR : T -> nat.
  Variable fL : T -> Lean.Nat.
  Hypothesis Hf : forall x, SubNatRel (fR x) (fL x).

  Fixpoint cr_sumseq_canonical (xs : seq T) :
    SubNatRel (foldr addn O (map fR xs)) (I.Prosa_Util_Sum_sumSeq T (ar_list_to_imported xs) fL) :=
    match xs return SubNatRel (foldr addn O (map fR xs))
      (I.Prosa_Util_Sum_sumSeq T (ar_list_to_imported xs) fL) with
    | [::] => sub_nat_rel_canonical O
    | x :: tail => svc_target_add_related _ _ _ _ (Hf x) (cr_sumseq_canonical tail)
    end.

  Lemma cr_sumseq_related (xsR : seq T) (xsL : I.List T) :
    ArListRel xsR xsL ->
    SubNatRel (\sum_(x <- xsR) fR x) (I.Prosa_Util_Sum_sumSeq T xsL fL).
  Proof.
    intro Hxs. rewrite cr_big_seq_as_fold.
    exact (sub_imported_eq_trans _ _ _ (cr_sumseq_canonical xsR)
      (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq T l fL) _ _ Hxs)).
  Qed.

  Fixpoint cr_sumtrue_canonical (xs : seq T) :
    SubNatRel (foldr addn O (map fR xs))
      (I.Prosa_Util_Sum_sumFiltered T (ar_list_to_imported xs) (fun _ => I.Bool_true) fL) :=
    match xs return SubNatRel (foldr addn O (map fR xs))
      (I.Prosa_Util_Sum_sumFiltered T (ar_list_to_imported xs) (fun _ => I.Bool_true) fL) with
    | [::] => sub_nat_rel_canonical O
    | x :: tail => svc_target_add_related _ _ _ _ (Hf x) (cr_sumtrue_canonical tail)
    end.

  Lemma cr_sumtrue_related (xsR : seq T) (xsL : I.List T) :
    ArListRel xsR xsL ->
    SubNatRel (\sum_(x <- xsR | xpredT x) fR x)
      (I.Prosa_Util_Sum_sumFiltered T xsL (fun _ => I.Bool_true) fL).
  Proof.
    intro Hxs. change (\sum_(x <- xsR | xpredT x) fR x) with (\sum_(x <- xsR) fR x).
    rewrite cr_big_seq_as_fold.
    exact (sub_imported_eq_trans _ _ _ (cr_sumtrue_canonical xsR)
      (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered T l (fun _ => I.Bool_true) fL) _ _ Hxs)).
  Qed.
End Sums.

(** MathComp's finite Boolean universal over ['I_n] is [all] over [iota 0 n]. *)
Lemma cr_forall_ord_all (n : nat) (p : nat -> bool) :
  [forall t : 'I_n, p t] = all p (iota 0 n).
Proof.
  apply/idP/idP.
  - move/forallP=> H. apply/allP => t. rewrite mem_iota add0n => /andP [_ lt].
    exact: (H (Ordinal lt)).
  - move/allP=> H. apply/forallP => [[t lt]] /=. apply: H. by rewrite mem_iota add0n lt.
Qed.

Fixpoint cr_all_nat_canonical (pR : nat -> bool) (pL : Lean.Nat -> I.Bool)
    (Hp : forall x, SvcBoolRel (pR x) (pL (sub_nat_to_imported x))) (xs : seq nat) {struct xs} :
    SvcBoolRel (all pR xs) (I.List_all_inst1 Lean.Nat (svc_nat_list_to_imported xs) pL) :=
  match xs return SvcBoolRel (all pR xs) (I.List_all_inst1 Lean.Nat (svc_nat_list_to_imported xs) pL) with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => svc_bool_and_related _ _ _ _ (Hp x) (cr_all_nat_canonical pR pL Hp tail)
  end.

Lemma cr_forall_ord_related (nR : nat) (nL : Lean.Nat) (pR : nat -> bool) (pL : Lean.Nat -> I.Bool) :
  SubNatRel nR nL -> (forall xR xL, SubNatRel xR xL -> SvcBoolRel (pR xR) (pL xL)) ->
  SvcBoolRel [forall t : 'I_nR, pR t]
    (I.List_all_inst1 Lean.Nat (I.List_range' Lean.Nat_zero nL svc_target_one) pL).
Proof.
  intros Hn Hp. rewrite cr_forall_ord_all.
  have Hl := svc_range_related O nR Lean.Nat_zero nL (sub_nat_rel_canonical O) Hn.
  refine (id_lean_transport (fun l => SvcBoolRel _ (I.List_all_inst1 Lean.Nat l pL)) _ _ Hl _).
  exact (cr_all_nat_canonical pR pL (fun x => Hp x _ (sub_nat_rel_canonical x)) (iota O nR)).
Qed.

Lemma cr_list_eq_correspondence {T : Type} (xsR ysR : seq T) (xsL ysL : I.List T) :
  ArListRel xsR xsL -> ArListRel ysR ysL -> PropSPropRel (xsR = ysR) (Lean.eq xsL ysL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro E. destruct E. exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hx) Hy).
  - intro E. apply strictly_inhabits.
    have Hc := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hx (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hy))).
    have Hd := f_equal ar_list_to_rocq Hc.
    rewrite !ar_list_source_roundtrip in Hd. exact Hd.
Qed.

(** ** Covers of inner quantifiers *)

Lemma cr_forall_list {T : Type} (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xsR xsL, ArListRel xsR xsL -> PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (forall xs, PR xs) (forall xs, PL xs).
Proof.
  exact (id_forall_cover_sprop _ _ ArListRel ar_list_to_imported ar_list_to_rocq
    (fun xs => @Lean.eq_refl _ _) ar_list_target_roundtrip PR PL).
Qed.

Lemma cr_forall_cost (Job : eqType) (PR : prosa.behavior.job.JobCost Job -> Prop)
    (PL : I.Prosa_Behavior_Job_JobCost Job (ar_decidable_eq Job) -> SProp) :
  (forall cR cL, SvcJobCostRel Job cR cL -> PropSPropRel (PR cR) (PL cL)) ->
  PropSPropRel (forall c, PR c) (forall c, PL c).
Proof.
  exact (id_forall_cover_sprop _ _ (SvcJobCostRel Job) (svc_import_job_cost Job) (svc_export_job_cost Job)
    (svc_job_cost_import Job) (svc_job_cost_export Job) PR PL).
Qed.

Lemma cr_cost_le_rel (Job : eqType) aR aL bR bL :
  SvcJobCostRel Job aR aL -> SvcJobCostRel Job bR bL ->
  PropSPropRel (forall j : Job, is_true (leq (@prosa.behavior.job.job_cost Job aR j) (@prosa.behavior.job.job_cost Job bR j)))
    (forall j : Job, I.LE_le_inst1 I.Prosa_Behavior_Job_work I.instLENat
      (I.Prosa_Behavior_Job_JobCost_job_cost Job (ar_decidable_eq Job) aL j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job (ar_decidable_eq Job) bL j)).
Proof.
  intros Ha Hb. apply ar_forall_identity_correspondence => j.
  exact (sub_nat_le_correspondence _ _ _ _ (Ha j) (Hb j)).
Qed.

(** ** Arrival-side schedule hypotheses and deadlines *)

Section Arrival.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Variable sR : @prosa.behavior.schedule.schedule Job PSR.
  Variable sL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.
  Hypothesis Hs : IdScheduleRel Job sR sL.

  Lemma cr_jobs_come_from_rel :
    PropSPropRel (prosa.behavior.ready.jobs_come_from_arrival_sequence sR arrR)
      (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job dJ PSL sL arrL).
  Proof.
    unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
    cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (id_scheduled_at_related Job sR sL Hs j tR tL Ht))|].
    exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
  Qed.

  Lemma cr_jobs_must_arrive_rel :
    PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PSR sR)
      (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job dJ jaL PSL sL).
  Proof.
    unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
    cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (id_scheduled_at_related Job sR sL Hs j tR tL Ht))|].
    exact (ar_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
  Qed.
End Arrival.

Definition CrJobDeadlineRel (Job : eqType) (dlR : prosa.behavior.job.JobDeadline Job)
    (dlL : I.Prosa_Behavior_Job_JobDeadline Job (ar_decidable_eq Job)) : SProp :=
  forall j : Job, SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
    (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job (ar_decidable_eq Job) dlL j).

Lemma cr_job_meets_deadline_related (Job : eqType)
    (sR : @prosa.behavior.schedule.schedule Job (prosa.model.processor.ideal.processor_state Job))
    (sL : I.Prosa_Behavior_Schedule_schedule_inst4 Job (ar_decidable_eq Job)
      (I.Prosa_Model_Processor_Ideal_processor_state Job (ar_decidable_eq Job)))
    (Hs : IdScheduleRel Job sR sL) costR costL (Hc : SvcJobCostRel Job costR costL)
    dlR dlL (Hdl : CrJobDeadlineRel Job dlR dlL) (j : Job) :
  SvcBoolRel (@prosa.behavior.service.job_meets_deadline Job _ sR costR dlR j)
    (I.Prosa_Behavior_Service_job_meets_deadline_inst4 Job (ar_decidable_eq Job)
      (I.Prosa_Model_Processor_Ideal_processor_state Job (ar_decidable_eq Job)) sL costL dlL j).
Proof.
  unfold prosa.behavior.service.job_meets_deadline.
  cbn [I.Prosa_Behavior_Service_job_meets_deadline_inst4].
  exact (cr_completed_by_related Job sR sL Hs costR costL Hc j _ _ (Hdl j)).
Qed.

(** ** Small Nat helpers *)

Lemma cr_succ_related (tR : nat) (tL : Lean.Nat) :
  SubNatRel tR tL -> SubNatRel tR.+1 (svc_target_add tL svc_target_one).
Proof.
  intro Ht. rewrite -addn1. exact (svc_target_add_related _ _ _ _ Ht (sub_nat_rel_canonical 1)).
Qed.

Lemma cr_pred_related (tR : nat) (tL : Lean.Nat) :
  SubNatRel tR tL -> SubNatRel tR.-1 (svc_target_sub tL svc_target_one).
Proof.
  intro Ht. rewrite -subn1. exact (svc_target_sub_related _ _ _ _ Ht (sub_nat_rel_canonical 1)).
Qed.

(** ** Definition correspondences *)

Section Definitions.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.

  Variable rsR : @prosa.behavior.schedule.schedule Job PSR.
  Variable rsL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.
  Hypothesis Hrs : IdScheduleRel Job rsR rsL.
  Variable osR : @prosa.behavior.schedule.schedule Job PSR.
  Variable osL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.
  Hypothesis Hos : IdScheduleRel Job osR osL.
  Variable rcR : prosa.behavior.job.JobCost Job.
  Variable rcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hrc : SvcJobCostRel Job rcR rcL.
  Variable ocR : prosa.behavior.job.JobCost Job.
  Variable ocL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hoc : SvcJobCostRel Job ocR ocL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable cbR : prosa.behavior.job.JobCost Job.
  Variable cbL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcb : SvcJobCostRel Job cbR cbL.

  Theorem schedulability_transferred_correspondence :
    PropSPropRel (@S.schedulability_transferred Job rsR osR rcR ocR)
      (I.Prosa_Results_TransferSchedulability_Criterion_schedulability_transferred Job dJ rsL osL rcL ocL).
  Proof.
    unfold S.schedulability_transferred. cbv beta zeta.
    cbn [I.Prosa_Results_TransferSchedulability_Criterion_schedulability_transferred].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence.
    - exact (svc_bool_truth_correspondence _ _ (cr_completed_by_related Job rsR rsL Hrs rcR rcL Hrc j tR tL Ht)).
    - exact (svc_bool_truth_correspondence _ _ (cr_completed_by_related Job osR osL Hos ocR ocL Hoc j tR tL Ht)).
  Qed.

  Theorem remaining_cost_bound_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@S.remaining_cost_bound Job osR cbR j tR)
      (I.Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job dJ osL cbL j tL).
  Proof.
    intro Ht. unfold S.remaining_cost_bound. cbv beta zeta.
    cbn [I.Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound].
    exact (svc_target_sub_related _ _ _ _ (Hcb j) (cr_service_related Job osR osL Hos j tR tL Ht)).
  Qed.

  Theorem critical_jobs_correspondence (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    ArListRel (@S.critical_jobs Job rsR osR rcR ocR arrR t1R t2R)
      (I.Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job dJ rsL osL rcL ocL arrL t1L t2L).
  Proof.
    intros H1 H2. unfold S.critical_jobs. cbv beta zeta.
    cbn [I.Prosa_Results_TransferSchedulability_Criterion_critical_jobs].
    apply ar_filter_related.
    - intro j. apply svc_bool_and_related.
      + exact (cr_completed_by_related Job rsR rsL Hrs rcR rcL Hrc j _ _ H2).
      + exact (svc_bool_not_related _ _ (cr_completed_by_related Job osR osL Hos ocR ocL Hoc j _ _ H1)).
    - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr _ _ H2).
  Qed.

  Let CJ := critical_jobs_correspondence.
  Let RCB := remaining_cost_bound_correspondence.

  Lemma cr_sum_rcb_related (t1R t2R tR : nat) (t1L t2L tL : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L -> SubNatRel tR tL ->
    SubNatRel (\sum_(j <- @S.critical_jobs Job rsR osR rcR ocR arrR t1R t2R) @S.remaining_cost_bound Job osR cbR j tR)
      (I.Prosa_Util_Sum_sumSeq Job
        (I.Prosa_Results_TransferSchedulability_Criterion_critical_jobs Job dJ rsL osL rcL ocL arrL t1L t2L)
        (fun j => I.Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job dJ osL cbL j tL)).
  Proof.
    intros H1 H2 Ht.
    exact (cr_sumseq_related (fun j => @S.remaining_cost_bound Job osR cbR j tR)
      (fun j => I.Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job dJ osL cbL j tL)
      (fun j => RCB j tR tL Ht) _ _ (CJ t1R t2R t1L t2L H1 H2)).
  Qed.

  Theorem slackless_interval_correspondence (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SvcBoolRel (@S.slackless_interval Job rsR osR rcR ocR arrR cbR t1R t2R)
      (I.Prosa_Results_TransferSchedulability_Criterion_slackless_interval Job dJ rsL osL rcL ocL arrL cbL t1L t2L).
  Proof.
    intros H1 H2. unfold S.slackless_interval. cbv beta zeta.
    cbn [I.Prosa_Results_TransferSchedulability_Criterion_slackless_interval].
    apply svc_bool_and_related.
    - exact (svc_decide_lt_related _ _ _ _ H1 H2).
    - exact (svc_decide_eq_related _ _ _ _ (cr_sum_rcb_related _ _ _ _ _ _ H1 H2 H1)
        (svc_target_sub_related _ _ _ _ H2 H1)).
  Qed.

  Theorem contiguously_slackless_interval_correspondence (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SvcBoolRel (@S.contiguously_slackless_interval Job rsR osR rcR ocR arrR cbR t1R t2R)
      (I.Prosa_Results_TransferSchedulability_Criterion_contiguously_slackless_interval Job dJ rsL osL rcL ocL arrL cbL t1L t2L).
  Proof.
    intros H1 H2. unfold S.contiguously_slackless_interval. cbv beta zeta.
    cbn [I.Prosa_Results_TransferSchedulability_Criterion_contiguously_slackless_interval].
    apply svc_bool_and_related.
    - exact (slackless_interval_correspondence _ _ _ _ H1 H2).
    - apply (cr_forall_ord_related _ _
        (fun d => @S.slackless_interval Job rsR osR rcR ocR arrR cbR (t1R + d) t2R)
        (fun d => I.Prosa_Results_TransferSchedulability_Criterion_slackless_interval Job dJ rsL osL rcL ocL arrL cbL
          (svc_target_add t1L d) t2L)
        (svc_target_sub_related _ _ _ _ H2 H1)).
      intros xR xL Hx.
      exact (slackless_interval_correspondence _ _ _ _ (svc_target_add_related _ _ _ _ H1 Hx) H2).
  Qed.

  Theorem transfer_schedulability_criterion_correspondence :
    PropSPropRel (@S.transfer_schedulability_criterion Job rsR osR rcR ocR arrR cbR)
      (I.Prosa_Results_TransferSchedulability_Criterion_transfer_schedulability_criterion Job dJ rsL osL rcL ocL arrL cbL).
  Proof.
    unfold S.transfer_schedulability_criterion. cbv beta zeta.
    cbn [I.Prosa_Results_TransferSchedulability_Criterion_transfer_schedulability_criterion].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (slackless_interval_correspondence _ _ _ _ H1 H2))|].
    apply id_exists_identity_correspondence => j.
    apply svc_bool_truth_correspondence. apply svc_bool_and_related.
    - exact (id_scheduled_at_related Job osR osL Hos j _ _ H1).
    - exact (ar_decide_mem_related Job j _ _ (CJ _ _ _ _ H1 H2)).
  Qed.

  Theorem nonpositive_slack_correspondence (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SvcBoolRel (@S.nonpositive_slack Job rsR osR rcR ocR arrR cbR t1R t2R)
      (I.Prosa_Results_TransferSchedulability_Criterion_nonpositive_slack Job dJ rsL osL rcL ocL arrL cbL t1L t2L).
  Proof.
    intros H1 H2. unfold S.nonpositive_slack. cbv beta zeta.
    cbn [I.Prosa_Results_TransferSchedulability_Criterion_nonpositive_slack].
    exact (svc_decide_le_related _ _ _ _ (svc_target_sub_related _ _ _ _ H2 H1)
      (cr_sum_rcb_related _ _ _ _ _ _ H1 H2 H1)).
  Qed.

  Theorem contiguously_nps_correspondence (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SvcBoolRel (@S.contiguously_nps Job rsR osR rcR ocR arrR cbR t1R t2R)
      (I.Prosa_Results_TransferSchedulability_Criterion_contiguously_nps Job dJ rsL osL rcL ocL arrL cbL t1L t2L).
  Proof.
    intros H1 H2. unfold S.contiguously_nps. cbv beta zeta.
    cbn [I.Prosa_Results_TransferSchedulability_Criterion_contiguously_nps].
    apply (cr_forall_ord_related _ _
      (fun d => @S.nonpositive_slack Job rsR osR rcR ocR arrR cbR (t1R + d) t2R)
      (fun d => I.Prosa_Results_TransferSchedulability_Criterion_nonpositive_slack Job dJ rsL osL rcL ocL arrL cbL
        (svc_target_add t1L d) t2L)
      (svc_target_sub_related _ _ _ _ H2 H1)).
    intros xR xL Hx.
    exact (nonpositive_slack_correspondence _ _ _ _ (svc_target_add_related _ _ _ _ H1 Hx) H2).
  Qed.
End Definitions.

(** ** Statement correspondences *)

Section Statements.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable dlR : prosa.behavior.job.JobDeadline Job.
  Variable dlL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
  Hypothesis Hdl : CrJobDeadlineRel Job dlR dlL.
  Variable rsR : @prosa.behavior.schedule.schedule Job PSR.
  Variable rsL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.
  Hypothesis Hrs : IdScheduleRel Job rsR rsL.
  Variable osR : @prosa.behavior.schedule.schedule Job PSR.
  Variable osL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.
  Hypothesis Hos : IdScheduleRel Job osR osL.
  Variable rcR : prosa.behavior.job.JobCost Job.
  Variable rcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hrc : SvcJobCostRel Job rcR rcL.
  Variable ocR : prosa.behavior.job.JobCost Job.
  Variable ocL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hoc : SvcJobCostRel Job ocR ocL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable cbR : prosa.behavior.job.JobCost Job.
  Variable cbL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcb : SvcJobCostRel Job cbR cbL.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].
  Local Ltac impt H := apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ H)|].
  Local Ltac tr H := exact (svc_bool_truth_correspondence _ _ H).

  Let ST := schedulability_transferred_correspondence Job rsR rsL Hrs osR osL Hos rcR rcL Hrc ocR ocL Hoc.
  Let CJ := critical_jobs_correspondence Job rsR rsL Hrs osR osL Hos rcR rcL Hrc ocR ocL Hoc arrR arrL Harr.
  Let RCB := remaining_cost_bound_correspondence Job osR osL Hos.
  Let SUM := cr_sum_rcb_related Job rsR rsL Hrs osR osL Hos rcR rcL Hrc ocR ocL Hoc arrR arrL Harr.
  Let SL := slackless_interval_correspondence Job rsR rsL Hrs osR osL Hos rcR rcL Hrc ocR ocL Hoc arrR arrL Harr.
  Let CSL := contiguously_slackless_interval_correspondence Job rsR rsL Hrs osR osL Hos rcR rcL Hrc ocR ocL Hoc arrR arrL Harr.
  Let TSC := transfer_schedulability_criterion_correspondence Job rsR rsL Hrs osR osL Hos rcR rcL Hrc ocR ocL Hoc arrR arrL Harr.
  Let NPS := nonpositive_slack_correspondence Job rsR rsL Hrs osR osL Hos rcR rcL Hrc ocR ocL Hoc arrR arrL Harr.
  Let CNPS := contiguously_nps_correspondence Job rsR rsL Hrs osR osL Hos rcR rcL Hrc ocR ocL Hoc arrR arrL Harr.
  Let CBr := cr_completed_by_related Job rsR rsL Hrs rcR rcL Hrc.
  Let CBo := cr_completed_by_related Job osR osL Hos ocR ocL Hoc.
  Let SCHo := id_scheduled_at_related Job osR osL Hos.
  Let CDEr := cr_cde_rel Job rsR rsL Hrs rcR rcL Hrc.
  Let CDEo := cr_cde_rel Job osR osL Hos ocR ocL Hoc.
  Let VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.
  Let COME := cr_jobs_come_from_rel Job arrR arrL Harr rsR rsL Hrs.
  Let MUST := cr_jobs_must_arrive_rel Job jaR jaL Hja rsR rsL Hrs.
  Let LE := cr_cost_le_rel Job.
  Let JMDr := cr_job_meets_deadline_related Job rsR rsL Hrs rcR rcL Hrc dlR dlL Hdl.
  Let JMDo := cr_job_meets_deadline_related Job osR osL Hos ocR ocL Hoc dlR dlL Hdl.

  Lemma cr_service_of_jobs_true_related (xsR : seq Job) (xsL : I.List Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    ArListRel xsR xsL -> SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.model.aggregate.service_of_jobs.service_of_jobs Job PSR osR xpredT xsR t1R t2R)
      (I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_inst4 Job dJ PSL osL (fun _ => I.Bool_true) xsL t1L t2L).
  Proof.
    intros Hxs H1 H2. unfold prosa.model.aggregate.service_of_jobs.service_of_jobs.
    cbn [I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_inst4].
    exact (cr_sumtrue_related (fun j => @prosa.behavior.service.service_during Job PSR osR j t1R t2R)
      (fun j => I.Prosa_Behavior_Service_service_during_inst4 Job dJ PSL osL j t1L t2L)
      (fun j => cr_service_during_related Job osR osL Hos j _ _ _ _ H1 H2) _ _ Hxs).
  Qed.

  Definition src_deadlines_met : Prop :=
    ltac:(body_of (fun s : S.statement_deadlines_met => s Job dlR rsR osR rcR ocR)).
  Definition tgt_deadlines_met : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_deadlines_met Job dJ dlL rsL osL rcL ocL)).

  Theorem deadlines_met_correspondence : PropSPropRel src_deadlines_met tgt_deadlines_met.
  Proof.
    unfold src_deadlines_met, tgt_deadlines_met.
    imp ST. apply ar_forall_identity_correspondence => j.
    impt (JMDr j). tr (JMDo j).
  Qed.

  Definition src_ref_cost_bounds_online_cost : Prop :=
    ltac:(body_of (fun s : S.statement_ref_cost_bounds_online_cost => s Job rcR ocR cbR)).
  Definition tgt_ref_cost_bounds_online_cost : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_ref_cost_bounds_online_cost Job dJ rcL ocL cbL)).

  Theorem ref_cost_bounds_online_cost_correspondence : PropSPropRel src_ref_cost_bounds_online_cost tgt_ref_cost_bounds_online_cost.
  Proof.
    unfold src_ref_cost_bounds_online_cost, tgt_ref_cost_bounds_online_cost.
    imp (LE _ _ _ _ Hoc Hcb). imp (LE _ _ _ _ Hcb Hrc). exact (LE _ _ _ _ Hoc Hrc).
  Qed.

  Definition src_remcost_service : Prop :=
    ltac:(body_of (fun s : S.statement_remcost_service => s Job osR ocR)).
  Definition tgt_remcost_service : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_remcost_service Job dJ osL ocL)).

  Theorem remcost_service_correspondence : PropSPropRel src_remcost_service tgt_remcost_service.
  Proof.
    unfold src_remcost_service, tgt_remcost_service.
    imp CDEo. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hoc Hb).
    apply ar_forall_identity_correspondence => j. apply ar_forall_nat_correspondence => tR tL Ht.
    apply sub_nat_eq_correspondence; first exact (RCB bR bL Hb j tR tL Ht).
    exact (svc_target_add_related _ _ _ _ (RCB bR bL Hb j _ _ (cr_succ_related _ _ Ht))
      (id_service_at_related Job osR osL Hos j tR tL Ht)).
  Qed.

  Definition src_remcost_service_during : Prop :=
    ltac:(body_of (fun s : S.statement_remcost_service_during => s Job osR ocR)).
  Definition tgt_remcost_service_during : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_remcost_service_during Job dJ osL ocL)).

  Theorem remcost_service_during_correspondence : PropSPropRel src_remcost_service_during tgt_remcost_service_during.
  Proof.
    unfold src_remcost_service_during, tgt_remcost_service_during.
    imp CDEo. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hoc Hb).
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    imp (sub_nat_le_correspondence _ _ _ _ H1 H2).
    apply sub_nat_eq_correspondence; first exact (RCB bR bL Hb j _ _ H1).
    exact (svc_target_add_related _ _ _ _ (RCB bR bL Hb j _ _ H2)
      (cr_service_during_related Job osR osL Hos j _ _ _ _ H1 H2)).
  Qed.

  Definition src_remcost_total_service_during : Prop :=
    ltac:(body_of (fun s : S.statement_remcost_total_service_during => s Job osR ocR)).
  Definition tgt_remcost_total_service_during : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_remcost_total_service_during Job dJ osL ocL)).

  Theorem remcost_total_service_during_correspondence : PropSPropRel src_remcost_total_service_during tgt_remcost_total_service_during.
  Proof.
    unfold src_remcost_total_service_during, tgt_remcost_total_service_during.
    imp CDEo. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hoc Hb).
    apply cr_forall_list => xsR xsL Hxs.
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    imp (sub_nat_le_correspondence _ _ _ _ H1 H2).
    apply sub_nat_eq_correspondence; first exact (cr_sumseq_related (fun j => @S.remaining_cost_bound Job osR bR j t1R)
      (fun j => I.Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job dJ osL bL j t1L)
      (fun j => RCB bR bL Hb j _ _ H1) _ _ Hxs).
    exact (svc_target_add_related _ _ _ _ (cr_sumseq_related (fun j => @S.remaining_cost_bound Job osR bR j t2R)
      (fun j => I.Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job dJ osL bL j t2L)
      (fun j => RCB bR bL Hb j _ _ H2) _ _ Hxs)
      (cr_service_of_jobs_true_related _ _ _ _ _ _ Hxs H1 H2)).
  Qed.

  Definition src_remaining_cost_invariant : Prop :=
    ltac:(body_of (fun s : S.statement_remaining_cost_invariant => s Job osR ocR)).
  Definition tgt_remaining_cost_invariant : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_remaining_cost_invariant Job dJ osL ocL)).

  Theorem remaining_cost_invariant_correspondence : PropSPropRel src_remaining_cost_invariant tgt_remaining_cost_invariant.
  Proof.
    unfold src_remaining_cost_invariant, tgt_remaining_cost_invariant.
    imp CDEo. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hoc Hb).
    apply cr_forall_list => xsR xsL Hxs.
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    imp (sub_nat_le_correspondence _ _ _ _ H1 H2).
    imp (ar_uniq_correspondence Job _ _ Hxs).
    apply ar_imp_correspondence.
    - apply ar_forall_nat_correspondence => tR tL Ht.
      impt (svc_bool_and_related _ _ _ _ (svc_decide_le_related _ _ _ _ H1 Ht) (svc_decide_lt_related _ _ _ _ Ht H2)).
      apply id_exists_identity_correspondence => j.
      tr (svc_bool_and_related _ _ _ _ (ar_decide_mem_related Job j _ _ Hxs) (SCHo j _ _ Ht)).
    - apply sub_nat_eq_correspondence; first exact (cr_sumseq_related (fun j => @S.remaining_cost_bound Job osR bR j t1R)
      (fun j => I.Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job dJ osL bL j t1L)
      (fun j => RCB bR bL Hb j _ _ H1) _ _ Hxs).
      exact (svc_target_add_related _ _ _ _ (cr_sumseq_related (fun j => @S.remaining_cost_bound Job osR bR j t2R)
      (fun j => I.Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job dJ osL bL j t2L)
      (fun j => RCB bR bL Hb j _ _ H2) _ _ Hxs)
        (svc_target_sub_related _ _ _ _ H2 H1)).
  Qed.

  Definition src_online_remaining_cost_bounded : Prop :=
    ltac:(body_of (fun s : S.statement_online_remaining_cost_bounded => s Job osR ocR)).
  Definition tgt_online_remaining_cost_bounded : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_online_remaining_cost_bounded Job dJ osL ocL)).

  Theorem online_remaining_cost_bounded_correspondence : PropSPropRel src_online_remaining_cost_bounded tgt_online_remaining_cost_bounded.
  Proof.
    unfold src_online_remaining_cost_bounded, tgt_online_remaining_cost_bounded.
    imp CDEo. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hoc Hb).
    apply ar_forall_identity_correspondence => j. apply ar_forall_nat_correspondence => tR tL Ht.
    exact (sub_nat_le_correspondence _ _ _ _ (cr_remaining_cost_related Job osR osL Hos ocR ocL Hoc j _ _ Ht)
      (RCB bR bL Hb j _ _ Ht)).
  Qed.

  Definition src_remaining_cost_positive : Prop :=
    ltac:(body_of (fun s : S.statement_remaining_cost_positive => s Job osR ocR cbR)).
  Definition tgt_remaining_cost_positive : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_remaining_cost_positive Job dJ osL ocL cbL)).

  Theorem remaining_cost_positive_correspondence : PropSPropRel src_remaining_cost_positive tgt_remaining_cost_positive.
  Proof.
    unfold src_remaining_cost_positive, tgt_remaining_cost_positive.
    imp (LE _ _ _ _ Hoc Hcb).
    apply ar_forall_identity_correspondence => j. apply ar_forall_nat_correspondence => tR tL Ht.
    impt (svc_bool_not_related _ _ (CBo j _ _ Ht)).
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (RCB cbR cbL Hcb j _ _ Ht)).
  Qed.

  Definition src_remaining_cost_zero : Prop :=
    ltac:(body_of (fun s : S.statement_remaining_cost_zero => s Job osR ocR)).
  Definition tgt_remaining_cost_zero : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_remaining_cost_zero Job dJ osL ocL)).

  Theorem remaining_cost_zero_correspondence : PropSPropRel src_remaining_cost_zero tgt_remaining_cost_zero.
  Proof.
    unfold src_remaining_cost_zero, tgt_remaining_cost_zero.
    imp CDEo. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hoc Hb).
    apply cr_forall_list => xsR xsL Hxs. apply ar_forall_nat_correspondence => tR tL Ht.
    impt (svc_decide_eq_related _ _ _ _ (cr_sumseq_related (fun j => @S.remaining_cost_bound Job osR bR j tR)
      (fun j => I.Prosa_Results_TransferSchedulability_Criterion_remaining_cost_bound Job dJ osL bL j tL)
      (fun j => RCB bR bL Hb j _ _ Ht) _ _ Hxs) (sub_nat_rel_canonical O)).
    apply ar_forall_identity_correspondence => j.
    impt (ar_decide_mem_related Job j _ _ Hxs). tr (CBo j _ _ Ht).
  Qed.

  Definition src_critical_jobs_monotonicity : Prop :=
    ltac:(body_of (fun s : S.statement_critical_jobs_monotonicity => s Job rsR osR rcR ocR arrR)).
  Definition tgt_critical_jobs_monotonicity : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_critical_jobs_monotonicity Job dJ rsL osL rcL ocL arrL)).

  Theorem critical_jobs_monotonicity_correspondence : PropSPropRel src_critical_jobs_monotonicity tgt_critical_jobs_monotonicity.
  Proof.
    unfold src_critical_jobs_monotonicity, tgt_critical_jobs_monotonicity.
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_nat_correspondence => t3R t3L H3.
    impt (svc_bool_and_related _ _ _ _ (svc_decide_le_related _ _ _ _ H1 H2) (svc_decide_le_related _ _ _ _ H2 H3)).
    apply ar_forall_identity_correspondence => j.
    impt (ar_decide_mem_related Job j _ _ (CJ _ _ _ _ H2 H3)). tr (ar_decide_mem_related Job j _ _ (CJ _ _ _ _ H1 H3)).
  Qed.

  Definition src_critical_jobs_dropout : Prop :=
    ltac:(body_of (fun s : S.statement_critical_jobs_dropout => s Job rsR osR rcR ocR arrR)).
  Definition tgt_critical_jobs_dropout : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_critical_jobs_dropout Job dJ rsL osL rcL ocL arrL)).

  Theorem critical_jobs_dropout_correspondence : PropSPropRel src_critical_jobs_dropout tgt_critical_jobs_dropout.
  Proof.
    unfold src_critical_jobs_dropout, tgt_critical_jobs_dropout.
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_nat_correspondence => t3R t3L H3.
    impt (svc_bool_and_related _ _ _ _ (svc_decide_le_related _ _ _ _ H1 H2) (svc_decide_le_related _ _ _ _ H2 H3)).
    apply ar_forall_identity_correspondence => j.
    impt (ar_decide_mem_related Job j _ _ (CJ _ _ _ _ H1 H3)).
    impt (svc_bool_not_related _ _ (ar_decide_mem_related Job j _ _ (CJ _ _ _ _ H2 H3))). tr (CBo j _ _ H2).
  Qed.

  Definition src_critical_jobs_filter_complete : Prop :=
    ltac:(body_of (fun s : S.statement_critical_jobs_filter_complete => s Job rsR osR rcR ocR arrR)).
  Definition tgt_critical_jobs_filter_complete : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_critical_jobs_filter_complete Job dJ rsL osL rcL ocL arrL)).

  Theorem critical_jobs_filter_complete_correspondence : PropSPropRel src_critical_jobs_filter_complete tgt_critical_jobs_filter_complete.
  Proof.
    unfold src_critical_jobs_filter_complete, tgt_critical_jobs_filter_complete.
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_nat_correspondence => t3R t3L H3.
    imp (sub_nat_le_correspondence _ _ _ _ H1 H2).
    apply cr_list_eq_correspondence; first exact (CJ _ _ _ _ H2 H3).
    apply ar_filter_related; last exact (CJ _ _ _ _ H1 H3).
    intro j. exact (svc_bool_not_related _ _ (CBo j _ _ H2)).
  Qed.

  Definition src_critical_jobs_uniq : Prop :=
    ltac:(body_of (fun s : S.statement_critical_jobs_uniq => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_critical_jobs_uniq : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_critical_jobs_uniq Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem critical_jobs_uniq_correspondence : PropSPropRel src_critical_jobs_uniq tgt_critical_jobs_uniq.
  Proof.
    unfold src_critical_jobs_uniq, tgt_critical_jobs_uniq.
    imp VALID. apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    exact (ar_uniq_correspondence Job _ _ (CJ _ _ _ _ H1 H2)).
  Qed.

  Definition src_critical_jobs_min_completion_time : Prop :=
    ltac:(body_of (fun s : S.statement_critical_jobs_min_completion_time => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_critical_jobs_min_completion_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_critical_jobs_min_completion_time Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem critical_jobs_min_completion_time_correspondence : PropSPropRel src_critical_jobs_min_completion_time tgt_critical_jobs_min_completion_time.
  Proof.
    unfold src_critical_jobs_min_completion_time, tgt_critical_jobs_min_completion_time.
    imp VALID. imp CDEr. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hb Hrc).
    apply ar_forall_nat_correspondence => tR tL Ht.
    exact (sub_nat_le_correspondence _ _ _ _
      (cr_sumseq_related (fun j => @prosa.behavior.job.job_cost Job bR j)
        (fun j => I.Prosa_Behavior_Job_JobCost_job_cost Job dJ bL j) Hb _ _ (CJ _ _ _ _ (sub_nat_rel_canonical O) Ht)) Ht).
  Qed.

  Definition src_critical_jobs_remaining_cost_monotonic : Prop :=
    ltac:(body_of (fun s : S.statement_critical_jobs_remaining_cost_monotonic => s Job rsR osR rcR ocR arrR)).
  Definition tgt_critical_jobs_remaining_cost_monotonic : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_critical_jobs_remaining_cost_monotonic Job dJ rsL osL rcL ocL arrL)).

  Theorem critical_jobs_remaining_cost_monotonic_correspondence : PropSPropRel src_critical_jobs_remaining_cost_monotonic tgt_critical_jobs_remaining_cost_monotonic.
  Proof.
    unfold src_critical_jobs_remaining_cost_monotonic, tgt_critical_jobs_remaining_cost_monotonic.
    imp CDEo. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hoc Hb).
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_nat_correspondence => t3R t3L H3.
    impt (svc_bool_and_related _ _ _ _ (svc_decide_le_related _ _ _ _ H1 H2) (svc_decide_le_related _ _ _ _ H2 H3)).
    exact (sub_nat_le_correspondence _ _ _ _ (SUM bR bL Hb _ _ _ _ _ _ H2 H3 H2) (SUM bR bL Hb _ _ _ _ _ _ H1 H3 H1)).
  Qed.

  Definition src_late_in_critical_jobs : Prop :=
    ltac:(body_of (fun s : S.statement_late_in_critical_jobs => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_late_in_critical_jobs : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_late_in_critical_jobs Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem late_in_critical_jobs_correspondence : PropSPropRel src_late_in_critical_jobs tgt_late_in_critical_jobs.
  Proof.
    unfold src_late_in_critical_jobs, tgt_late_in_critical_jobs.
    imp VALID. imp COME. imp MUST. apply (cr_forall_cost Job) => bR bL Hb.
    imp (LE _ _ _ _ Hoc Hb). imp (LE _ _ _ _ Hb Hrc).
    apply ar_forall_identity_correspondence => j. apply ar_forall_nat_correspondence => tR tL Ht.
    impt (CBr j _ _ Ht). impt (svc_bool_not_related _ _ (CBo j _ _ Ht)).
    tr (ar_decide_mem_related Job j _ _ (CJ _ _ _ _ Ht Ht)).
  Qed.

  Definition src_late_not_at_start : Prop :=
    ltac:(body_of (fun s : S.statement_late_not_at_start => s Job rsR osR rcR ocR cbR)).
  Definition tgt_late_not_at_start : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_late_not_at_start Job dJ rsL osL rcL ocL cbL)).

  Theorem late_not_at_start_correspondence : PropSPropRel src_late_not_at_start tgt_late_not_at_start.
  Proof.
    unfold src_late_not_at_start, tgt_late_not_at_start.
    imp (LE _ _ _ _ Hoc Hcb). imp (LE _ _ _ _ Hcb Hrc).
    apply ar_forall_identity_correspondence => j. apply ar_forall_nat_correspondence => tR tL Ht.
    impt (CBr j _ _ Ht). impt (svc_bool_not_related _ _ (CBo j _ _ Ht)).
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Ht).
  Qed.

  Definition src_contiguously_nps_start : Prop :=
    ltac:(body_of (fun s : S.statement_contiguously_nps_start => s Job rsR osR rcR ocR arrR cbR)).
  Definition tgt_contiguously_nps_start : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_contiguously_nps_start Job dJ rsL osL rcL ocL arrL cbL)).

  Theorem contiguously_nps_start_correspondence : PropSPropRel src_contiguously_nps_start tgt_contiguously_nps_start.
  Proof.
    unfold src_contiguously_nps_start, tgt_contiguously_nps_start.
    apply ar_forall_nat_correspondence => t0R t0L H0. apply ar_forall_nat_correspondence => t2R t2L H2.
    impt (svc_bool_not_related _ _ (CNPS cbR cbL Hcb _ _ _ _ H0 H2)).
    impt (CNPS cbR cbL Hcb _ _ _ _ (cr_succ_related _ _ H0) H2).
    tr (svc_bool_not_related _ _ (NPS cbR cbL Hcb _ _ _ _ H0 H2)).
  Qed.

  Definition src_contiguously_nps_existence : Prop :=
    ltac:(body_of (fun s : S.statement_contiguously_nps_existence => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_contiguously_nps_existence : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_contiguously_nps_existence Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem contiguously_nps_existence_correspondence : PropSPropRel src_contiguously_nps_existence tgt_contiguously_nps_existence.
  Proof.
    unfold src_contiguously_nps_existence, tgt_contiguously_nps_existence.
    imp VALID. imp COME. imp MUST. apply (cr_forall_cost Job) => bR bL Hb.
    imp (LE _ _ _ _ Hoc Hb). imp (LE _ _ _ _ Hb Hrc).
    apply ar_forall_identity_correspondence => j. apply ar_forall_nat_correspondence => t2R t2L H2.
    impt (CBr j _ _ H2). impt (svc_bool_not_related _ _ (CBo j _ _ H2)).
    apply ar_exists_nat_correspondence => t1R t1L H1.
    apply ar_and_correspondence; first tr (CNPS bR bL Hb _ _ _ _ H1 H2).
    apply ar_and_correspondence; first exact (sub_nat_lt_correspondence _ _ _ _ H1 H2).
    apply id_or_correspondence; first exact (sub_nat_eq_correspondence _ _ _ _ H1 (sub_nat_rel_canonical O)).
    tr (svc_bool_not_related _ _ (NPS bR bL Hb _ _ _ _ (cr_pred_related _ _ H1) H2)).
  Qed.

  Definition src_slackless_interval_step_case_completed_job_rem : Prop :=
    ltac:(body_of (fun s : S.statement_slackless_interval_step_case_completed_job_rem => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_slackless_interval_step_case_completed_job_rem : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_slackless_interval_step_case_completed_job_rem Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem slackless_interval_step_case_completed_job_rem_correspondence : PropSPropRel src_slackless_interval_step_case_completed_job_rem tgt_slackless_interval_step_case_completed_job_rem.
  Proof.
    unfold src_slackless_interval_step_case_completed_job_rem, tgt_slackless_interval_step_case_completed_job_rem.
    imp VALID. imp CDEo. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hoc Hb).
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    impt (SL bR bL Hb _ _ _ _ H1 H2). impt (NPS bR bL Hb _ _ _ _ (cr_succ_related _ _ H1) H2).
    apply ar_forall_identity_correspondence => j.
    impt (SCHo j _ _ H1). impt (ar_decide_mem_related Job j _ _ (CJ _ _ _ _ H1 H2)).
    impt (CBo j _ _ (cr_succ_related _ _ H1)).
    exact (sub_nat_eq_correspondence _ _ _ _ (RCB bR bL Hb j _ _ (cr_succ_related _ _ H1)) (sub_nat_rel_canonical O)).
  Qed.

  Definition src_slackless_interval_step_case_completed_job : Prop :=
    ltac:(body_of (fun s : S.statement_slackless_interval_step_case_completed_job => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_slackless_interval_step_case_completed_job : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_slackless_interval_step_case_completed_job Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem slackless_interval_step_case_completed_job_correspondence : PropSPropRel src_slackless_interval_step_case_completed_job tgt_slackless_interval_step_case_completed_job.
  Proof.
    unfold src_slackless_interval_step_case_completed_job, tgt_slackless_interval_step_case_completed_job.
    imp VALID. imp CDEo. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hoc Hb).
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    impt (SL bR bL Hb _ _ _ _ H1 H2). imp (sub_nat_lt_correspondence _ _ _ _ (cr_succ_related _ _ H1) H2).
    impt (NPS bR bL Hb _ _ _ _ (cr_succ_related _ _ H1) H2).
    apply ar_forall_identity_correspondence => j.
    impt (SCHo j _ _ H1). impt (ar_decide_mem_related Job j _ _ (CJ _ _ _ _ H1 H2)).
    impt (CBo j _ _ (cr_succ_related _ _ H1)).
    tr (SL bR bL Hb _ _ _ _ (cr_succ_related _ _ H1) H2).
  Qed.

  Definition src_slackless_interval_step_case_incomplete_job : Prop :=
    ltac:(body_of (fun s : S.statement_slackless_interval_step_case_incomplete_job => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_slackless_interval_step_case_incomplete_job : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_slackless_interval_step_case_incomplete_job Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem slackless_interval_step_case_incomplete_job_correspondence : PropSPropRel src_slackless_interval_step_case_incomplete_job tgt_slackless_interval_step_case_incomplete_job.
  Proof.
    unfold src_slackless_interval_step_case_incomplete_job, tgt_slackless_interval_step_case_incomplete_job.
    imp VALID. imp CDEo. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hoc Hb).
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    impt (SL bR bL Hb _ _ _ _ H1 H2). imp (sub_nat_lt_correspondence _ _ _ _ (cr_succ_related _ _ H1) H2).
    impt (NPS bR bL Hb _ _ _ _ (cr_succ_related _ _ H1) H2).
    apply ar_forall_identity_correspondence => j.
    impt (SCHo j _ _ H1). impt (ar_decide_mem_related Job j _ _ (CJ _ _ _ _ H1 H2)).
    impt (svc_bool_not_related _ _ (CBo j _ _ (cr_succ_related _ _ H1))).
    tr (SL bR bL Hb _ _ _ _ (cr_succ_related _ _ H1) H2).
  Qed.

  Definition src_slackless_interval_step : Prop :=
    ltac:(body_of (fun s : S.statement_slackless_interval_step => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_slackless_interval_step : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_slackless_interval_step Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem slackless_interval_step_correspondence : PropSPropRel src_slackless_interval_step tgt_slackless_interval_step.
  Proof.
    unfold src_slackless_interval_step, tgt_slackless_interval_step.
    imp VALID. imp CDEo. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hoc Hb). imp (TSC bR bL Hb).
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    impt (SL bR bL Hb _ _ _ _ H1 H2). imp (sub_nat_lt_correspondence _ _ _ _ (cr_succ_related _ _ H1) H2).
    impt (NPS bR bL Hb _ _ _ _ (cr_succ_related _ _ H1) H2).
    tr (SL bR bL Hb _ _ _ _ (cr_succ_related _ _ H1) H2).
  Qed.

  Definition src_slackless_interval_continuation : Prop :=
    ltac:(body_of (fun s : S.statement_slackless_interval_continuation => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_slackless_interval_continuation : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_slackless_interval_continuation Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem slackless_interval_continuation_correspondence : PropSPropRel src_slackless_interval_continuation tgt_slackless_interval_continuation.
  Proof.
    unfold src_slackless_interval_continuation, tgt_slackless_interval_continuation.
    imp VALID. imp CDEo. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hoc Hb). imp (TSC bR bL Hb).
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    impt (SL bR bL Hb _ _ _ _ H1 H2). impt (CNPS bR bL Hb _ _ _ _ H1 H2).
    apply svc_bool_truth_correspondence.
    apply (cr_forall_ord_related _ _
      (fun d => @S.slackless_interval Job rsR osR rcR ocR arrR bR (t1R + d) t2R)
      (fun d => I.Prosa_Results_TransferSchedulability_Criterion_slackless_interval Job dJ rsL osL rcL ocL arrL bL
        (svc_target_add t1L d) t2L)
      (svc_target_sub_related _ _ _ _ H2 H1)).
    intros xR xL Hx. exact (SL bR bL Hb _ _ _ _ (svc_target_add_related _ _ _ _ H1 Hx) H2).
  Qed.

  Definition src_slackless_interval_existence : Prop :=
    ltac:(body_of (fun s : S.statement_slackless_interval_existence => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_slackless_interval_existence : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_slackless_interval_existence Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem slackless_interval_existence_correspondence : PropSPropRel src_slackless_interval_existence tgt_slackless_interval_existence.
  Proof.
    unfold src_slackless_interval_existence, tgt_slackless_interval_existence.
    imp VALID. imp COME. imp MUST. imp CDEr. imp CDEo. apply (cr_forall_cost Job) => bR bL Hb.
    imp (LE _ _ _ _ Hoc Hb). imp (LE _ _ _ _ Hb Hrc). imp (TSC bR bL Hb).
    apply ar_forall_identity_correspondence => j. apply ar_forall_nat_correspondence => t2R t2L H2.
    impt (CBr j _ _ H2). impt (svc_bool_not_related _ _ (CBo j _ _ H2)).
    apply ar_exists_nat_correspondence => t1R t1L H1.
    tr (svc_bool_and_related _ _ _ _ (CSL bR bL Hb _ _ _ _ H1 H2) (ar_decide_mem_related Job j _ _ (CJ _ _ _ _ H1 H2))).
  Qed.

  Definition src_slackless_interval_completion : Prop :=
    ltac:(body_of (fun s : S.statement_slackless_interval_completion => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_slackless_interval_completion : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_slackless_interval_completion Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem slackless_interval_completion_correspondence : PropSPropRel src_slackless_interval_completion tgt_slackless_interval_completion.
  Proof.
    unfold src_slackless_interval_completion, tgt_slackless_interval_completion.
    imp VALID. imp CDEo. apply (cr_forall_cost Job) => bR bL Hb. imp (LE _ _ _ _ Hoc Hb). imp (TSC bR bL Hb).
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    impt (CSL bR bL Hb _ _ _ _ H1 H2). impt (ar_decide_mem_related Job j _ _ (CJ _ _ _ _ H1 H2)).
    tr (CBo j _ _ H2).
  Qed.

  Definition src_online_transfer_schedulability_criterion_sufficiency : Prop :=
    ltac:(body_of (fun s : S.statement_online_transfer_schedulability_criterion_sufficiency => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_online_transfer_schedulability_criterion_sufficiency : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_online_transfer_schedulability_criterion_sufficiency Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem online_transfer_schedulability_criterion_sufficiency_correspondence : PropSPropRel src_online_transfer_schedulability_criterion_sufficiency tgt_online_transfer_schedulability_criterion_sufficiency.
  Proof.
    unfold src_online_transfer_schedulability_criterion_sufficiency, tgt_online_transfer_schedulability_criterion_sufficiency.
    imp VALID. imp COME. imp MUST. imp CDEr. imp CDEo. imp (LE _ _ _ _ Hoc Hrc). imp (TSC ocR ocL Hoc). exact ST.
  Qed.

  Definition src_online_transfer_schedulability_criterion_ensures_schedulability : Prop :=
    ltac:(body_of (fun s : S.statement_online_transfer_schedulability_criterion_ensures_schedulability => s Job jaR dlR rsR osR rcR ocR arrR)).
  Definition tgt_online_transfer_schedulability_criterion_ensures_schedulability : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_online_transfer_schedulability_criterion_ensures_schedulability Job dJ jaL dlL rsL osL rcL ocL arrL)).

  Theorem online_transfer_schedulability_criterion_ensures_schedulability_correspondence : PropSPropRel src_online_transfer_schedulability_criterion_ensures_schedulability tgt_online_transfer_schedulability_criterion_ensures_schedulability.
  Proof.
    unfold src_online_transfer_schedulability_criterion_ensures_schedulability, tgt_online_transfer_schedulability_criterion_ensures_schedulability.
    imp VALID. imp COME. imp MUST. imp CDEr. imp CDEo. imp (LE _ _ _ _ Hoc Hrc). imp (TSC ocR ocL Hoc).
    apply ar_forall_identity_correspondence => j. impt (JMDr j). tr (JMDo j).
  Qed.

  Definition src_delay_if_no_critical_job_is_scheduled : Prop :=
    ltac:(body_of (fun s : S.statement_delay_if_no_critical_job_is_scheduled => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_delay_if_no_critical_job_is_scheduled : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_delay_if_no_critical_job_is_scheduled Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem delay_if_no_critical_job_is_scheduled_correspondence : PropSPropRel src_delay_if_no_critical_job_is_scheduled tgt_delay_if_no_critical_job_is_scheduled.
  Proof.
    unfold src_delay_if_no_critical_job_is_scheduled, tgt_delay_if_no_critical_job_is_scheduled.
    imp VALID. imp CDEo.
    apply ar_forall_nat_correspondence => t1R t1L H1. apply ar_forall_nat_correspondence => t2R t2L H2.
    impt (SL ocR ocL Hoc _ _ _ _ H1 H2).
    apply ar_imp_correspondence.
    - unfold prop_in1. apply ar_forall_identity_correspondence => j.
      impt (ar_decide_mem_related Job j _ _ (CJ _ _ _ _ H1 H2)). tr (svc_bool_not_related _ _ (SCHo j _ _ H1)).
    - apply id_exists_identity_correspondence => j.
      apply ar_and_correspondence; first tr (ar_decide_mem_related Job j _ _ (CJ _ _ _ _ H1 H2)).
      tr (svc_bool_not_related _ _ (CBo j _ _ H2)).
  Qed.

  Definition src_online_transfer_schedulability_criterion_necessity : Prop :=
    ltac:(body_of (fun s : S.statement_online_transfer_schedulability_criterion_necessity => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_online_transfer_schedulability_criterion_necessity : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_online_transfer_schedulability_criterion_necessity Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem online_transfer_schedulability_criterion_necessity_correspondence : PropSPropRel src_online_transfer_schedulability_criterion_necessity tgt_online_transfer_schedulability_criterion_necessity.
  Proof.
    unfold src_online_transfer_schedulability_criterion_necessity, tgt_online_transfer_schedulability_criterion_necessity.
    imp VALID. imp CDEo. imp ST. exact (TSC ocR ocL Hoc).
  Qed.

  Definition src_ref_transfer_schedulability_criterion_sufficiency : Prop :=
    ltac:(body_of (fun s : S.statement_ref_transfer_schedulability_criterion_sufficiency => s Job jaR rsR osR rcR ocR arrR)).
  Definition tgt_ref_transfer_schedulability_criterion_sufficiency : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_ref_transfer_schedulability_criterion_sufficiency Job dJ jaL rsL osL rcL ocL arrL)).

  Theorem ref_transfer_schedulability_criterion_sufficiency_correspondence : PropSPropRel src_ref_transfer_schedulability_criterion_sufficiency tgt_ref_transfer_schedulability_criterion_sufficiency.
  Proof.
    unfold src_ref_transfer_schedulability_criterion_sufficiency, tgt_ref_transfer_schedulability_criterion_sufficiency.
    imp VALID. imp COME. imp MUST. imp CDEr. imp CDEo. imp (LE _ _ _ _ Hoc Hrc). imp (TSC rcR rcL Hrc). exact ST.
  Qed.

  Definition src_ref_transfer_schedulability_criterion_ensures_schedulability : Prop :=
    ltac:(body_of (fun s : S.statement_ref_transfer_schedulability_criterion_ensures_schedulability => s Job jaR dlR rsR osR rcR ocR arrR)).
  Definition tgt_ref_transfer_schedulability_criterion_ensures_schedulability : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_TransferSchedulability_Criterion_ref_transfer_schedulability_criterion_ensures_schedulability Job dJ jaL dlL rsL osL rcL ocL arrL)).

  Theorem ref_transfer_schedulability_criterion_ensures_schedulability_correspondence : PropSPropRel src_ref_transfer_schedulability_criterion_ensures_schedulability tgt_ref_transfer_schedulability_criterion_ensures_schedulability.
  Proof.
    unfold src_ref_transfer_schedulability_criterion_ensures_schedulability, tgt_ref_transfer_schedulability_criterion_ensures_schedulability.
    imp VALID. imp COME. imp MUST. imp CDEr. imp CDEo. imp (LE _ _ _ _ Hoc Hrc). imp (TSC rcR rcL Hrc).
    apply ar_forall_identity_correspondence => j. impt (JMDr j). tr (JMDo j).
  Qed.

End Statements.
