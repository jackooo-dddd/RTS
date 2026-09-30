From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsWcCorrectnessSemanticSource.
From prosa Require Import model.processor.ideal model.schedule.work_conserving model.readiness.basic
  analysis.transform.swap.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsWcCorrectness ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  WcTransCorrespondence.

Module I := ImportedFactsWcCorrectness.
Module S := FactsWcCorrectnessSemanticSource.FactsWcCorrectnessSemanticSource.
Module WT := WcTransSemanticSource.WcTransSemanticSource.
Module G := GeneratedSearchArgSource.GeneratedSearchArgSource.
Module SC := SchedulabilitySemanticSource.SchedulabilitySemanticSource.

(** Definition and statement correspondences for
    [analysis/facts/transform/wc_correctness.v].

    Source side: the extracted byte-identical definition blocks and the
    extracted statements [S.statement_X] specialised at their leading inputs
    (the instances and the arrival sequence); target side: the compiled Lean
    definitions and the imported Lean theorem types.  The processor model is
    fixed to the ideal uniprocessor on both sides: states are related by the
    accepted constructor-preserving Option map ([IdOptRel]) and schedules
    pointwise ([IdScheduleRel]) of the accepted wc-trans certificate, covered
    in both directions; [scheduled_at], [service_in] and [service] are related
    through the accepted kernel-checked ideal-state equations of the
    ideal-schedule export root (the accepted ideal-schedule closed forms,
    restated here as [wcc_*] helpers); [job_cost] by [SvcJobCostRel],
    [job_deadline] pointwise by [SubNatRel], [job_arrival] by
    [ArJobArrivalRel], arrival sequences by [ArArrivalSequenceRel]; the
    transformation definitions by the accepted wc-trans definition
    certificates ([search_arg] results through the accepted [FetOptNatRel]).
    The readiness model is the source's local basic instance on both sides,
    related through [pending].  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators *)

Lemma wcc_forall_cover (A B : Type) (Rel : A -> B -> SProp)
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

Lemma wcc_exists_identity_correspondence (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x.
    exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma wcc_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

(** ** Ideal states *)

Definition wcc_opt_to_rocq {T : Type} (y : I.Option T) : option T :=
  match y with
  | I.Option_none => None
  | I.Option_some j => Some j
  end.

Lemma wcc_opt_source_roundtrip {T : Type} (x : option T) :
  wcc_opt_to_rocq (id_opt_to_imported x) = x.
Proof. by case: x. Qed.

Lemma wcc_opt_target_roundtrip {T : Type} (y : I.Option T) :
  Lean.eq (id_opt_to_imported (wcc_opt_to_rocq y)) y.
Proof. destruct y; exact (@Lean.eq_refl _ _). Qed.

Lemma wcc_opt_rel_canonical {T : Type} (x : option T) : IdOptRel x (id_opt_to_imported x).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma wcc_opt_eq_correspondence {T : Type} (xR yR : option T) (xL yL : I.Option T) :
  IdOptRel xR xL -> IdOptRel yR yL -> PropSPropRel (xR = yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro E. destruct E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hx) Hy).
  - intro E. apply strictly_inhabits.
    have EL := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hx (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hy))).
    have ES := f_equal wcc_opt_to_rocq EL.
    rewrite !wcc_opt_source_roundtrip in ES. exact ES.
Qed.

Lemma wcc_option_some_eq_correspondence (T : eqType) (s : option T) (j : T) :
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

Lemma wcc_option_some_eq_rel (T : eqType) (sR : option T) (sL : I.Option T) (j : T) :
  IdOptRel sR sL -> PropSPropRel (is_true (sR == Some j)) (Lean.eq sL (I.Option_some T j)).
Proof.
  intro Hs. have E := imported_eq_to_coq_eq _ _ Hs. rewrite <- E.
  exact (wcc_option_some_eq_correspondence T sR j).
Qed.

Lemma wcc_option_none_eq_related (T : eqType) (s : option T) :
  SvcBoolRel (s == None)
    (match id_opt_to_imported s with
     | I.Option_none => I.Bool_true
     | I.Option_some _ => I.Bool_false
     end).
Proof. destruct s; exact (@Lean.eq_refl _ _). Qed.

(** ** Options of naturals ([search_arg] results) *)

Definition wcc_optnat_to_rocq (o : I.Option_inst1 Lean.Nat) : option nat :=
  match o with
  | I.Option_none_inst1 => None
  | I.Option_some_inst1 n => Some (sub_nat_to_rocq n)
  end.

Lemma wcc_optnat_roundtrip (o : option nat) : wcc_optnat_to_rocq (fet_optnat_to_imported o) = o.
Proof. destruct o as [n|]; cbn; [by rewrite sub_nat_rocq_roundtrip | reflexivity]. Qed.

Lemma wcc_optnat_some_eq (oR : option nat) (oL : I.Option_inst1 Lean.Nat) (tR : nat) (tL : Lean.Nat) :
  FetOptNatRel oR oL -> SubNatRel tR tL ->
  PropSPropRel (oR = Some tR) (Lean.eq oL (I.Option_some_inst1 Lean.Nat tL)).
Proof.
  intros Ho Ht. apply prop_sprop_rel_intro.
  - intro E. rewrite E in Ho.
    refine (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Ho) _).
    exact (sub_imported_eq_congr (I.Option_some_inst1 Lean.Nat) _ _ Ht).
  - intro E. apply strictly_inhabits.
    have EL := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Ho (sub_imported_eq_trans _ _ _ E
        (sub_imported_eq_sym _ _ (sub_imported_eq_congr (I.Option_some_inst1 Lean.Nat) _ _ Ht)))).
    have ES := f_equal wcc_optnat_to_rocq EL.
    rewrite wcc_optnat_roundtrip in ES. cbn in ES. rewrite sub_nat_rocq_roundtrip in ES. exact ES.
Qed.

Lemma wcc_optnat_none_eq (oR : option nat) (oL : I.Option_inst1 Lean.Nat) :
  FetOptNatRel oR oL -> PropSPropRel (oR = None) (Lean.eq oL (I.Option_none_inst1 Lean.Nat)).
Proof.
  intros Ho. apply prop_sprop_rel_intro.
  - intro E. rewrite E in Ho. exact (sub_imported_eq_sym _ _ Ho).
  - intro E. apply strictly_inhabits.
    have EL := imported_eq_to_coq_eq _ _ (sub_imported_eq_trans _ _ _ Ho E).
    have ES := f_equal wcc_optnat_to_rocq EL.
    rewrite wcc_optnat_roundtrip in ES. exact ES.
Qed.

Section WcCorrectness.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.
  Let SchedR := @prosa.behavior.schedule.schedule Job PSR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.

  Local Transparent prosa.behavior.schedule.scheduled_on prosa.behavior.schedule.service_on
    prosa.behavior.schedule.supply_on.

  (** *** Ideal-state closed forms (the accepted ideal-schedule blocks, restated) *)

  Lemma wcc_src_scheduled_on (j : Job) (s : option Job) (c : unit) :
    @prosa.behavior.schedule.scheduled_on Job PSR j s c = (s == Some j).
  Proof. by []. Qed.

  Lemma wcc_src_scheduled_in (j : Job) (s : option Job) :
    @prosa.behavior.schedule.scheduled_in Job PSR j s = (s == Some j).
  Proof.
    rewrite /prosa.behavior.schedule.scheduled_in.
    apply/existsP/idP => [[c]|H].
    - by rewrite wcc_src_scheduled_on.
    - by exists tt; rewrite wcc_src_scheduled_on.
  Qed.

  Lemma wcc_src_service_in (j : Job) (s : option Job) :
    @prosa.behavior.schedule.service_in Job PSR j s = nat_of_bool (s == Some j).
  Proof.
    rewrite /prosa.behavior.schedule.service_in (big_pred1 tt) /=.
    all: try by case: (s == Some j).
    all: by case.
  Qed.

  Lemma wcc_scheduled_in_related (j : Job) (sR : option Job) sL :
    IdOptRel sR sL ->
    SvcBoolRel (@prosa.behavior.schedule.scheduled_in Job PSR j sR)
      (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst4 Job dJ PSL j sL).
  Proof.
    intro Hs. destruct Hs. rewrite wcc_src_scheduled_in.
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_IdealScheduleInterface_production_ideal_scheduled_in Job dJ j _))).
    cbn. apply ar_decide_bool_correspondence.
    exact (wcc_option_some_eq_correspondence Job sR j).
  Qed.

  Lemma wcc_decide_state_related (j : Job) (sR : option Job) sL :
    IdOptRel sR sL -> forall d,
    SvcBoolRel (sR == Some j) (I.Decidable_decide (Lean.eq sL (I.Option_some Job j)) d).
  Proof.
    intros Hs d. destruct Hs. apply ar_decide_bool_correspondence.
    exact (wcc_option_some_eq_correspondence Job sR j).
  Qed.

  Lemma wcc_service_on_related (j : Job) (sR : option Job) sL cR cL :
    IdOptRel sR sL ->
    SubNatRel (@prosa.behavior.schedule.service_on Job PSR j sR cR)
      (I.Prosa_Behavior_Schedule_ProcessorState_service_on_inst2 Job dJ PSL j sL cL).
  Proof.
    intro Hs. destruct Hs. cbn.
    have Hb := wcc_decide_state_related j sR (id_opt_to_imported sR) (@Lean.eq_refl _ _)
      (I.Option_instDecidableEq Job dJ (id_opt_to_imported sR) (I.Option_some Job j)).
    unfold SvcBoolRel in Hb. revert Hb.
    generalize (I.Decidable_decide (Lean.eq (id_opt_to_imported sR) (I.Option_some Job j))
      (I.Option_instDecidableEq Job dJ (id_opt_to_imported sR) (I.Option_some Job j))).
    intros bL Hb. destruct Hb.
    change (opt_eq sR (Some j)) with (sR == Some j).
    destruct (sR == Some j); cbn;
      [exact (sub_nat_rel_canonical 1) | exact (sub_nat_rel_canonical O)].
  Qed.

  Lemma wcc_service_in_related (j : Job) (sR : option Job) sL :
    IdOptRel sR sL ->
    SubNatRel (@prosa.behavior.schedule.service_in Job PSR j sR)
      (I.Prosa_Behavior_Schedule_ProcessorState_service_in_inst4 Job dJ PSL j sL).
  Proof.
    intro Hs.
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_IdealScheduleInterface_production_ideal_service_in Job dJ j sL))).
    have H := wcc_service_on_related j sR sL tt I.Unit_unit Hs.
    rewrite wcc_src_service_in. change (nat_of_bool (sR == Some j)) with
      (@prosa.behavior.schedule.service_on Job PSR j sR tt).
    exact H.
  Qed.

  (** *** Schedule covers and observations *)

  Definition wcc_sched_to_target (sR : SchedR) : SchedL :=
    fun tL => id_opt_to_imported (sR (sub_nat_to_rocq tL)).

  Definition wcc_sched_to_source (sL : SchedL) : SchedR :=
    fun tR => wcc_opt_to_rocq (sL (sub_nat_to_imported tR)).

  Lemma wcc_sched_to_target_rel sR : IdScheduleRel Job sR (wcc_sched_to_target sR).
  Proof.
    intros tR tL Ht. unfold IdOptRel, wcc_sched_to_target.
    rewrite (id_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma wcc_sched_to_source_rel sL : IdScheduleRel Job (wcc_sched_to_source sL) sL.
  Proof.
    intros tR tL Ht.
    exact (sub_imported_eq_trans _ _ _ (wcc_opt_target_roundtrip _) (sub_imported_eq_congr sL _ _ Ht)).
  Qed.

  Lemma wcc_forall_sched (PR : SchedR -> Prop) (PL : SchedL -> SProp) :
    (forall sR sL, IdScheduleRel Job sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    exact (wcc_forall_cover _ _ (IdScheduleRel Job) wcc_sched_to_target wcc_sched_to_source
      wcc_sched_to_target_rel wcc_sched_to_source_rel PR PL).
  Qed.

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : IdScheduleRel Job sR sL.

    Lemma wcc_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PSR sR j tR)
        (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL sL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.scheduled_at.
      cbn [I.Prosa_Behavior_Service_scheduled_at_inst4].
      exact (wcc_scheduled_in_related j _ _ (Hs tR tL Ht)).
    Qed.

    Lemma wcc_sched_at (j : Job) (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
      PropSPropRel (is_true (@prosa.behavior.service.scheduled_at Job PSR sR j tR))
        (Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL sL j tL) I.Bool_true).
    Proof. exact (svc_bool_truth_correspondence _ _ (wcc_scheduled_at_related j tR tL Ht)). Qed.

    Lemma wcc_service_at_fun (j : Job) :
      SvcNatFunRel (fun t => @prosa.behavior.service.service_at Job PSR sR j t)
        (fun t => I.Prosa_Validation_ServiceInterface_serviceAtProjection_inst4 Job dJ PSL sL j t).
    Proof.
      intros tR tL Ht. unfold prosa.behavior.service.service_at.
      exact (wcc_service_in_related j _ _ (Hs tR tL Ht)).
    Qed.

    Lemma wcc_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service Job PSR sR j tR)
        (I.Prosa_Behavior_Service_service_inst4 Job dJ PSL sL j tL).
    Proof.
      intro Ht.
      exact (svc_interval_sum_related O tR _ tL _ _ (sub_nat_rel_canonical O) Ht (wcc_service_at_fun j)).
    Qed.

    Lemma wcc_idle_related (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
      SvcBoolRel (@prosa.model.processor.ideal.ideal_is_idle Job sR tR)
        (I.Prosa_Model_Processor_Ideal_ideal_is_idle Job dJ sL tL).
    Proof.
      unfold prosa.model.processor.ideal.ideal_is_idle.
      unfold I.Prosa_Model_Processor_Ideal_ideal_is_idle.
      have E := imported_eq_to_coq_eq _ _ (Hs tR tL Ht). rewrite <- E.
      destruct (sR tR); exact (@Lean.eq_refl _ _).
    Qed.
  End Sched.

  Variable jcR : prosa.behavior.job.JobCost Job.
  Variable jcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hjc : SvcJobCostRel Job jcR jcL.
  Variable dlR : prosa.behavior.job.JobDeadline Job.
  Variable dlL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
  Hypothesis Hdl : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
      (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let RMR := @prosa.model.readiness.basic.basic_ready_instance Job PSR jaR jcR.
  Let RML := I.Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job dJ PSL jaL jcL.

  (** *** Transformation definitions (accepted wc-trans certificates) *)

  Lemma wcc_maxdl (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
    SubNatRel (@WT.max_deadline_for_jobs_arrived_before Job dlR arrR tR)
      (I.Prosa_Analysis_Transform_WcTrans_max_deadline_for_jobs_arrived_before Job dJ dlL arrL tL).
  Proof. exact (max_deadline_for_jobs_arrived_before_correspondence Job dlR dlL Hdl arrR arrL Harr tR tL Ht). Qed.

  Lemma wcc_fsc (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL) (tR : nat) (tL : Lean.Nat)
      (Ht : SubNatRel tR tL) :
    SubNatRel (@WT.find_swap_candidate Job jaR dlR arrR sR tR)
      (I.Prosa_Analysis_Transform_WcTrans_find_swap_candidate Job dJ jaL dlL arrL sL tL).
  Proof.
    exact (find_swap_candidate_correspondence Job jaR jaL Hja dlR dlL Hdl arrR arrL Harr sR sL tR tL Hs Ht).
  Qed.

  Lemma wcc_mwa (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL) (tR : nat) (tL : Lean.Nat)
      (Ht : SubNatRel tR tL) :
    IdScheduleRel Job (@WT.make_wc_at Job jaR dlR arrR sR tR)
      (I.Prosa_Analysis_Transform_WcTrans_make_wc_at Job dJ jaL dlL arrL sL tL).
  Proof. exact (make_wc_at_correspondence Job jaR jaL Hja dlR dlL Hdl arrR arrL Harr sR sL tR tL Hs Ht). Qed.

  Lemma wcc_prefix (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL) (hR : nat) (hL : Lean.Nat)
      (Hh : SubNatRel hR hL) :
    IdScheduleRel Job (@WT.wc_transform_prefix Job jaR dlR arrR sR hR)
      (I.Prosa_Analysis_Transform_WcTrans_wc_transform_prefix Job dJ jaL dlL arrL sL hL).
  Proof.
    exact (wc_transform_prefix_correspondence Job jaR jaL Hja dlR dlL Hdl arrR arrL Harr sR sL hR hL Hs Hh).
  Qed.

  Lemma wcc_transform (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL) :
    IdScheduleRel Job (@WT.wc_transform Job jaR dlR arrR sR)
      (I.Prosa_Analysis_Transform_WcTrans_wc_transform Job dJ jaL dlL arrL sL).
  Proof.
    intros tR tL Ht.
    exact (wc_transform_correspondence Job jaR jaL Hja dlR dlL Hdl arrR arrL Harr sR sL tR tL Hs Ht).
  Qed.

  Lemma wcc_swapped (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
    IdScheduleRel Job (@prosa.analysis.transform.swap.swapped Job PSR sR t1R t2R)
      (I.Prosa_Analysis_Transform_Swap_swapped_inst4 Job dJ PSL sL t1L t2L).
  Proof. exact (wct_swapped_related Job sR sL t1R t2R t1L t2L Hs H1 H2). Qed.

  (** *** Definition correspondences *)

  Theorem order_correspondence (aR bR : nat) (aL bL : Lean.Nat) :
    SubNatRel aR aL -> SubNatRel bR bL ->
    SvcBoolRel (S.order aR bR) (I.Prosa_Analysis_Facts_Transform_WcCorrectness_order aL bL).
  Proof. intros _ _. exact (@Lean.eq_refl _ _). Qed.

  Theorem search_result_correspondence (sR : SchedR) (sL : SchedL) (tR : nat) (tL : Lean.Nat) :
    IdScheduleRel Job sR sL -> SubNatRel tR tL ->
    FetOptNatRel (@S.search_result Job jaR dlR arrR sR tR)
      (I.Prosa_Analysis_Facts_Transform_WcCorrectness_search_result Job dJ jaL dlL arrL sL tL).
  Proof.
    intros Hs Ht.
    unfold S.search_result.
    cbn [I.Prosa_Analysis_Facts_Transform_WcCorrectness_search_result].
    refine (wct_search_arg_related Job sR sL Hs
      (@WT.relevant_pstate Job jaR tR) (I.Prosa_Analysis_Transform_WcTrans_relevant_pstate Job dJ jaL tL)
      (fun sR' sL' H => relevant_pstate_correspondence Job jaR jaL Hja tR tL sR' sL' Ht H)
      _ _ _ tR tL Ht _ _ (wcc_maxdl tR tL Ht)).
    intros; exact (@Lean.eq_refl _ _).
  Qed.

  Section Obs.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : IdScheduleRel Job sR sL.

    Lemma wcc_pending_related (j : Job) (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
      SvcBoolRel (@prosa.behavior.service.pending Job PSR sR jcR jaR j tR)
        (I.Prosa_Behavior_Service_pending_inst4 Job dJ PSL sL jcL jaL j tL).
    Proof.
      unfold prosa.behavior.service.pending, prosa.behavior.service.completed_by.
      cbn [I.Prosa_Behavior_Service_pending_inst4
        I.Prosa_Validation_ServiceInterface_completedByProjection_inst4].
      exact (ar_bool_and_related _ _ _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)
        (svc_bool_not_related _ _ (svc_decide_le_related _ _ _ _ (Hjc j)
          (wcc_service_related sR sL Hs j tR tL Ht)))).
    Qed.

    Lemma wcc_ready_related (j : Job) (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
      SvcBoolRel (@prosa.behavior.ready.job_ready Job PSR jcR jaR RMR sR j tR)
        (I.Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job dJ PSL jcL jaL RML sL j tL).
    Proof. exact (wcc_pending_related j tR tL Ht). Qed.

    Lemma wcc_ready (j : Job) (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
      PropSPropRel (is_true (@prosa.behavior.ready.job_ready Job PSR jcR jaR RMR sR j tR))
        (Lean.eq (I.Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job dJ PSL jcL jaL RML sL j tL) I.Bool_true).
    Proof. exact (svc_bool_truth_correspondence _ _ (wcc_ready_related j tR tL Ht)). Qed.

    Lemma wcc_jmae_rel :
      PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PSR sR)
        (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job dJ jaL PSL sL).
    Proof.
      unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (wcc_sched_at sR sL Hs j tR tL Ht)|].
      exact (ar_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
    Qed.

    Lemma wcc_jmbr_rel :
      PropSPropRel (@prosa.behavior.ready.jobs_must_be_ready_to_execute Job jaR PSR sR jcR RMR)
        (I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst4 Job dJ jaL PSL sL jcL RML).
    Proof.
      unfold prosa.behavior.ready.jobs_must_be_ready_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (wcc_sched_at sR sL Hs j tR tL Ht)|].
      exact (wcc_ready j tR tL Ht).
    Qed.

    Lemma wcc_jcf_rel :
      PropSPropRel (prosa.behavior.ready.jobs_come_from_arrival_sequence sR arrR)
        (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job dJ PSL sL arrL).
    Proof.
      unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
      cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (wcc_sched_at sR sL Hs j tR tL Ht)|].
      exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    Qed.

    Lemma wcc_valid_rel :
      PropSPropRel (@prosa.behavior.ready.valid_schedule Job jaR PSR sR jcR RMR arrR)
        (I.Prosa_Behavior_Ready_valid_schedule_inst4 Job dJ jaL PSL sL jcL RML arrL).
    Proof.
      unfold prosa.behavior.ready.valid_schedule.
      cbn [I.Prosa_Behavior_Ready_valid_schedule_inst4].
      exact (ar_and_correspondence _ _ _ _ wcc_jcf_rel wcc_jmbr_rel).
    Qed.

    Lemma wcc_meets_rel (j : Job) :
      PropSPropRel (is_true (@prosa.behavior.service.job_meets_deadline Job PSR sR jcR dlR j))
        (Lean.eq (I.Prosa_Behavior_Service_job_meets_deadline_inst4 Job dJ PSL sL jcL dlL j) I.Bool_true).
    Proof.
      unfold prosa.behavior.service.job_meets_deadline, prosa.behavior.service.completed_by.
      exact (svc_bool_truth_correspondence _ _
        (svc_decide_le_related _ _ _ _ (Hjc j) (wcc_service_related sR sL Hs j _ _ (Hdl j)))).
    Qed.

    Lemma wcc_doa_rel :
      PropSPropRel (@SC.all_deadlines_of_arrivals_met Job jcR dlR PSR arrR sR)
        (I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job dJ jcL dlL PSL arrL sL).
    Proof.
      unfold SC.all_deadlines_of_arrivals_met.
      cbn [I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      exact (wcc_meets_rel j).
    Qed.

    Lemma wcc_wc_rel :
      PropSPropRel (@prosa.model.schedule.work_conserving.work_conserving Job jaR jcR PSR RMR arrR sR)
        (I.Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job dJ jaL jcL PSL RML arrL sL).
    Proof.
      unfold prosa.model.schedule.work_conserving.work_conserving.
      cbn [I.Prosa_Model_Schedule_WorkConserving_work_conserving_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      apply ar_imp_correspondence.
      { unfold prosa.behavior.ready.backlogged.
        cbn [I.Prosa_Behavior_Ready_backlogged_inst4].
        exact (svc_bool_truth_correspondence _ _ (svc_bool_and_related _ _ _ _ (wcc_ready_related j tR tL Ht)
          (svc_bool_not_related _ _ (wcc_scheduled_at_related sR sL Hs j tR tL Ht)))). }
      apply wcc_exists_identity_correspondence. intro j'.
      exact (wcc_sched_at sR sL Hs j' tR tL Ht).
    Qed.

    Theorem is_work_conserving_at_correspondence (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
      PropSPropRel (@S.is_work_conserving_at Job jaR jcR arrR sR tR)
        (I.Prosa_Analysis_Facts_Transform_WcCorrectness_is_work_conserving_at Job dJ jaL jcL arrL sL tL).
    Proof.
      unfold S.is_work_conserving_at.
      cbn [I.Prosa_Analysis_Facts_Transform_WcCorrectness_is_work_conserving_at].
      apply ar_imp_correspondence.
      { apply wcc_exists_identity_correspondence. intro j.
        apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
        exact (wcc_ready j tR tL Ht). }
      apply wcc_exists_identity_correspondence. intro j.
      exact (wcc_opt_eq_correspondence _ _ _ _ (Hs tR tL Ht) (wcc_opt_rel_canonical (Some j))).
    Qed.
  End Obs.

  (** ** Statement correspondences *)

  Ltac sat Hs j Ht := exact (wcc_sched_at _ _ Hs j _ _ Ht).

  Definition src_swap_candidate_is_in_future : Prop :=
    ltac:(body_of (fun s : S.statement_swap_candidate_is_in_future => s Job jaR dlR arrR)).
  Definition tgt_swap_candidate_is_in_future : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_swap_candidate_is_in_future Job dJ jaL dlL arrL)).

  Theorem swap_candidate_is_in_future_correspondence :
    PropSPropRel src_swap_candidate_is_in_future tgt_swap_candidate_is_in_future.
  Proof.
    unfold src_swap_candidate_is_in_future, tgt_swap_candidate_is_in_future.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (sub_nat_le_correspondence _ _ _ _ Ht (wcc_fsc _ _ Hs _ _ Ht)).
  Qed.

  Definition src_fsc_respects_has_arrived : Prop :=
    ltac:(body_of (fun s : S.statement_fsc_respects_has_arrived => s Job jaR jcR dlR arrR)).
  Definition tgt_fsc_respects_has_arrived : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_fsc_respects_has_arrived Job dJ jaL jcL dlL arrL)).

  Theorem fsc_respects_has_arrived_correspondence :
    PropSPropRel src_fsc_respects_has_arrived tgt_fsc_respects_has_arrived.
  Proof.
    unfold src_fsc_respects_has_arrived, tgt_fsc_respects_has_arrived.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (wcc_jmbr_rel _ _ Hs)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (wcc_option_some_eq_rel Job _ _ j (Hs _ _ (wcc_fsc _ _ Hs _ _ Ht)))|].
    exact (ar_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
  Qed.

  Definition src_swap_jobs_must_arrive_to_execute : Prop :=
    ltac:(body_of (fun s : S.statement_swap_jobs_must_arrive_to_execute => s Job jaR jcR dlR arrR)).
  Definition tgt_swap_jobs_must_arrive_to_execute : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_swap_jobs_must_arrive_to_execute Job dJ jaL jcL dlL arrL)).

  Theorem swap_jobs_must_arrive_to_execute_correspondence :
    PropSPropRel src_swap_jobs_must_arrive_to_execute tgt_swap_jobs_must_arrive_to_execute.
  Proof.
    unfold src_swap_jobs_must_arrive_to_execute, tgt_swap_jobs_must_arrive_to_execute.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (wcc_jmbr_rel _ _ Hs)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (wcc_jmae_rel _ _ (wcc_swapped _ _ Hs _ _ _ _ Ht (wcc_fsc _ _ Hs _ _ Ht))).
  Qed.

  Definition src_fsc_jobs_must_be_ready_to_execute : Prop :=
    ltac:(body_of (fun s : S.statement_fsc_jobs_must_be_ready_to_execute => s Job jaR jcR dlR arrR)).
  Definition tgt_fsc_jobs_must_be_ready_to_execute : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_fsc_jobs_must_be_ready_to_execute Job dJ jaL jcL dlL arrL)).

  Theorem fsc_jobs_must_be_ready_to_execute_correspondence :
    PropSPropRel src_fsc_jobs_must_be_ready_to_execute tgt_fsc_jobs_must_be_ready_to_execute.
  Proof.
    unfold src_fsc_jobs_must_be_ready_to_execute, tgt_fsc_jobs_must_be_ready_to_execute.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (wcc_jmbr_rel _ _ Hs)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (wcc_jmbr_rel _ _ (wcc_swapped _ _ Hs _ _ _ _ Ht (wcc_fsc _ _ Hs _ _ Ht))).
  Qed.

  Definition src_mwa_service_bound : Prop :=
    ltac:(body_of (fun s : S.statement_mwa_service_bound => s Job jaR dlR arrR)).
  Definition tgt_mwa_service_bound : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_mwa_service_bound Job dJ jaL dlL arrL)).

  Theorem mwa_service_bound_correspondence : PropSPropRel src_mwa_service_bound tgt_mwa_service_bound.
  Proof.
    unfold src_mwa_service_bound, tgt_mwa_service_bound.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t0R t0L Ht0.
    exact (sub_nat_le_correspondence _ _ _ _ (wcc_service_related _ _ Hs j _ _ Ht0)
      (wcc_service_related _ _ (wcc_mwa _ _ Hs _ _ Ht) j _ _ Ht0)).
  Qed.

  Definition src_mwa_ready_job_also_ready_in_original_schedule : Prop :=
    ltac:(body_of (fun s : S.statement_mwa_ready_job_also_ready_in_original_schedule => s Job jaR jcR dlR arrR)).
  Definition tgt_mwa_ready_job_also_ready_in_original_schedule : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_mwa_ready_job_also_ready_in_original_schedule
        Job dJ jaL jcL dlL arrL)).

  Theorem mwa_ready_job_also_ready_in_original_schedule_correspondence :
    PropSPropRel src_mwa_ready_job_also_ready_in_original_schedule tgt_mwa_ready_job_also_ready_in_original_schedule.
  Proof.
    unfold src_mwa_ready_job_also_ready_in_original_schedule, tgt_mwa_ready_job_also_ready_in_original_schedule.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t0R t0L Ht0.
    apply ar_imp_correspondence; [exact (wcc_ready _ _ (wcc_mwa _ _ Hs _ _ Ht) j _ _ Ht0)|].
    exact (wcc_ready _ _ Hs j _ _ Ht0).
  Qed.

  Definition src_max_dl_is_greatest_dl : Prop :=
    ltac:(body_of (fun s : S.statement_max_dl_is_greatest_dl => s Job jaR dlR arrR)).
  Definition tgt_max_dl_is_greatest_dl : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_max_dl_is_greatest_dl Job dJ jaL dlL arrL)).

  Theorem max_dl_is_greatest_dl_correspondence : PropSPropRel src_max_dl_is_greatest_dl tgt_max_dl_is_greatest_dl.
  Proof.
    unfold src_max_dl_is_greatest_dl, tgt_max_dl_is_greatest_dl.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ (Hja j) Ht)|].
    exact (sub_nat_le_correspondence _ _ _ _ (Hdl j) (wcc_maxdl _ _ Ht)).
  Qed.

  Definition src_make_wc_at_case_result_found : Prop :=
    ltac:(body_of (fun s : S.statement_make_wc_at_case_result_found => s Job jaR dlR arrR)).
  Definition tgt_make_wc_at_case_result_found : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_make_wc_at_case_result_found Job dJ jaL dlL arrL)).

  Theorem make_wc_at_case_result_found_correspondence :
    PropSPropRel src_make_wc_at_case_result_found tgt_make_wc_at_case_result_found.
  Proof.
    unfold src_make_wc_at_case_result_found, tgt_make_wc_at_case_result_found.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (wcc_idle_related _ _ Hs _ _ Ht))|].
    apply ar_forall_nat_correspondence. intros tsR tsL Hts.
    apply ar_imp_correspondence;
      [exact (wcc_optnat_some_eq _ _ _ _ (search_result_correspondence _ _ _ _ Hs Ht) Hts)|].
    apply wcc_exists_identity_correspondence. intro j.
    exact (wcc_opt_eq_correspondence _ _ _ _ (wcc_swapped _ _ Hs _ _ _ _ Ht Hts _ _ Ht)
      (wcc_opt_rel_canonical (Some j))).
  Qed.

  Definition src_no_relevant_state_in_range : Prop :=
    ltac:(body_of (fun s : S.statement_no_relevant_state_in_range => s Job jaR dlR arrR)).
  Definition tgt_no_relevant_state_in_range : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_no_relevant_state_in_range Job dJ jaL dlL arrL)).

  Theorem no_relevant_state_in_range_correspondence :
    PropSPropRel src_no_relevant_state_in_range tgt_no_relevant_state_in_range.
  Proof.
    unfold src_no_relevant_state_in_range, tgt_no_relevant_state_in_range.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (wcc_optnat_none_eq _ _ (search_result_correspondence _ _ _ _ Hs Ht))|].
    apply ar_forall_nat_correspondence. intros t'R t'L Ht'.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _
        (svc_bool_and_related _ _ _ _ (svc_decide_le_related _ _ _ _ Ht Ht')
          (svc_decide_lt_related _ _ _ _ Ht' (wcc_maxdl _ _ Ht))))|].
    exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _
      (relevant_pstate_correspondence Job jaR jaL Hja tR tL _ _ Ht (Hs _ _ Ht')))).
  Qed.

  Definition src_service_of_j_is_less_than_cost : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_j_is_less_than_cost => s Job jaR jcR dlR arrR)).
  Definition tgt_service_of_j_is_less_than_cost : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_service_of_j_is_less_than_cost Job dJ jaL jcL dlL arrL)).

  Theorem service_of_j_is_less_than_cost_correspondence :
    PropSPropRel src_service_of_j_is_less_than_cost tgt_service_of_j_is_less_than_cost.
  Proof.
    unfold src_service_of_j_is_less_than_cost, tgt_service_of_j_is_less_than_cost.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (wcc_ready _ _ (wcc_mwa _ _ Hs _ _ Ht) j _ _ Ht)|].
    exact (sub_nat_lt_correspondence _ _ _ _ (wcc_service_related _ _ Hs j _ _ Ht) (Hjc j)).
  Qed.

  (** The common prefix of the case-analysis statements. *)
  Lemma wcc_case_prefix (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL) (tR : nat) (tL : Lean.Nat)
      (Ht : SubNatRel tR tL) (PR : Job -> Prop) (PL : Job -> SProp) :
    (forall j, PropSPropRel (PR j) (PL j)) ->
    PropSPropRel
      (forall j : Job, prosa.behavior.arrival_sequence.arrives_in arrR j ->
        @prosa.behavior.ready.job_ready Job PSR jcR jaR RMR (@WT.make_wc_at Job jaR dlR arrR sR tR) j tR ->
        PR j)
      (forall j : Job, I.Prosa_Behavior_Arrival_sequence_arrives_in Job dJ arrL j ->
        Lean.eq (I.Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job dJ PSL jcL jaL RML
          (I.Prosa_Analysis_Transform_WcTrans_make_wc_at Job dJ jaL dlL arrL sL tL) j tL) I.Bool_true ->
        PL j).
  Proof.
    intro H.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence; [exact (wcc_ready _ _ (wcc_mwa _ _ Hs _ _ Ht) j _ _ Ht)|].
    exact (H j).
  Qed.

  Definition src_t_is_less_than_deadline_of_j : Prop :=
    ltac:(body_of (fun s : S.statement_t_is_less_than_deadline_of_j => s Job jaR jcR dlR arrR)).
  Definition tgt_t_is_less_than_deadline_of_j : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_t_is_less_than_deadline_of_j Job dJ jaL jcL dlL arrL)).

  Theorem t_is_less_than_deadline_of_j_correspondence :
    PropSPropRel src_t_is_less_than_deadline_of_j tgt_t_is_less_than_deadline_of_j.
  Proof.
    unfold src_t_is_less_than_deadline_of_j, tgt_t_is_less_than_deadline_of_j.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (wcc_doa_rel _ _ Hs)|].
    apply (wcc_case_prefix _ _ Hs _ _ Ht). intro j.
    exact (sub_nat_le_correspondence _ _ _ _ Ht (Hdl j)).
  Qed.

  (** The common prefix of the statements with the valid arrival sequence and the met deadlines. *)
  Lemma wcc_none_prefix (PR : SchedR -> nat -> Job -> Prop) (PL : SchedL -> Lean.Nat -> Job -> SProp) :
    (forall sR sL, IdScheduleRel Job sR sL -> forall tR tL, SubNatRel tR tL -> forall j,
      PropSPropRel (PR sR tR j) (PL sL tL j)) ->
    PropSPropRel
      (prosa.behavior.arrival_sequence.valid_arrival_sequence arrR ->
       forall (sched : SchedR) (t : nat), @SC.all_deadlines_of_arrivals_met Job jcR dlR PSR arrR sched ->
       forall j : Job, prosa.behavior.arrival_sequence.arrives_in arrR j ->
         @prosa.behavior.ready.job_ready Job PSR jcR jaR RMR (@WT.make_wc_at Job jaR dlR arrR sched t) j t ->
         @S.search_result Job jaR dlR arrR sched t = None -> PR sched t j)
      (I.Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job dJ jaL arrL ->
       forall (sched : SchedL) (t : Lean.Nat),
         I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job dJ jcL dlL PSL arrL sched ->
       forall j : Job, I.Prosa_Behavior_Arrival_sequence_arrives_in Job dJ arrL j ->
         Lean.eq (I.Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job dJ PSL jcL jaL RML
           (I.Prosa_Analysis_Transform_WcTrans_make_wc_at Job dJ jaL dlL arrL sched t) j t) I.Bool_true ->
         Lean.eq (I.Prosa_Analysis_Facts_Transform_WcCorrectness_search_result Job dJ jaL dlL arrL sched t)
           (I.Option_none_inst1 Lean.Nat) ->
         PL sched t j).
  Proof.
    intro H.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (wcc_doa_rel _ _ Hs)|].
    apply (wcc_case_prefix _ _ Hs _ _ Ht). intro j.
    apply ar_imp_correspondence; [exact (wcc_optnat_none_eq _ _ (search_result_correspondence _ _ _ _ Hs Ht))|].
    exact (H _ _ Hs _ _ Ht j).
  Qed.

  Definition src_equal_service_t_max_dl : Prop :=
    ltac:(body_of (fun s : S.statement_equal_service_t_max_dl => s Job jaR jcR dlR arrR)).
  Definition tgt_equal_service_t_max_dl : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_equal_service_t_max_dl Job dJ jaL jcL dlL arrL)).

  Theorem equal_service_t_max_dl_correspondence :
    PropSPropRel src_equal_service_t_max_dl tgt_equal_service_t_max_dl.
  Proof.
    unfold src_equal_service_t_max_dl, tgt_equal_service_t_max_dl.
    apply wcc_none_prefix. intros sR sL Hs tR tL Ht j.
    exact (sub_nat_eq_correspondence _ _ _ _ (wcc_service_related _ _ Hs j _ _ Ht)
      (wcc_service_related _ _ Hs j _ _ (wcc_maxdl _ _ Ht))).
  Qed.

  Definition src_j_misses_deadline : Prop :=
    ltac:(body_of (fun s : S.statement_j_misses_deadline => s Job jaR jcR dlR arrR)).
  Definition tgt_j_misses_deadline : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_j_misses_deadline Job dJ jaL jcL dlL arrL)).

  Theorem j_misses_deadline_correspondence : PropSPropRel src_j_misses_deadline tgt_j_misses_deadline.
  Proof.
    unfold src_j_misses_deadline, tgt_j_misses_deadline.
    apply wcc_none_prefix. intros sR sL Hs tR tL Ht j.
    exact (sub_nat_lt_correspondence _ _ _ _ (wcc_service_related _ _ Hs j _ _ (Hdl j)) (Hjc j)).
  Qed.

  Definition src_make_wc_at_case_result_none : Prop :=
    ltac:(body_of (fun s : S.statement_make_wc_at_case_result_none => s Job jaR jcR dlR arrR)).
  Definition tgt_make_wc_at_case_result_none : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_make_wc_at_case_result_none Job dJ jaL jcL dlL arrL)).

  Theorem make_wc_at_case_result_none_correspondence :
    PropSPropRel src_make_wc_at_case_result_none tgt_make_wc_at_case_result_none.
  Proof.
    unfold src_make_wc_at_case_result_none, tgt_make_wc_at_case_result_none.
    apply wcc_none_prefix. intros sR sL Hs tR tL Ht j.
    exact wcc_false_correspondence.
  Qed.

  Definition src_mwa_finds_ready_jobs : Prop :=
    ltac:(body_of (fun s : S.statement_mwa_finds_ready_jobs => s Job jaR jcR dlR arrR)).
  Definition tgt_mwa_finds_ready_jobs : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_mwa_finds_ready_jobs Job dJ jaL jcL dlL arrL)).

  Theorem mwa_finds_ready_jobs_correspondence : PropSPropRel src_mwa_finds_ready_jobs tgt_mwa_finds_ready_jobs.
  Proof.
    unfold src_mwa_finds_ready_jobs, tgt_mwa_finds_ready_jobs.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (wcc_doa_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (wcc_doa_rel _ _ Hs)|].
    exact (is_work_conserving_at_correspondence _ _ (wcc_mwa _ _ Hs _ _ Ht) _ _ Ht).
  Qed.

  Definition src_mwa_establishes_wc : Prop :=
    ltac:(body_of (fun s : S.statement_mwa_establishes_wc => s Job jaR jcR dlR arrR)).
  Definition tgt_mwa_establishes_wc : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_mwa_establishes_wc Job dJ jaL jcL dlL arrL)).

  Theorem mwa_establishes_wc_correspondence : PropSPropRel src_mwa_establishes_wc tgt_mwa_establishes_wc.
  Proof.
    unfold src_mwa_establishes_wc, tgt_mwa_establishes_wc.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (wcc_doa_rel _ _ Hs)|].
    apply ar_imp_correspondence.
    { apply ar_forall_nat_correspondence. intros lR lL Hl.
      apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Hl Ht)|].
      exact (is_work_conserving_at_correspondence _ _ Hs _ _ Hl). }
    apply ar_forall_nat_correspondence. intros lR lL Hl.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hl Ht)|].
    exact (is_work_conserving_at_correspondence _ _ (wcc_mwa _ _ Hs _ _ Ht) _ _ Hl).
  Qed.

  Definition src_mwa_jobs_come_from_arrival_sequence : Prop :=
    ltac:(body_of (fun s : S.statement_mwa_jobs_come_from_arrival_sequence => s Job jaR dlR arrR)).
  Definition tgt_mwa_jobs_come_from_arrival_sequence : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_mwa_jobs_come_from_arrival_sequence Job dJ jaL dlL arrL)).

  Theorem mwa_jobs_come_from_arrival_sequence_correspondence :
    PropSPropRel src_mwa_jobs_come_from_arrival_sequence tgt_mwa_jobs_come_from_arrival_sequence.
  Proof.
    unfold src_mwa_jobs_come_from_arrival_sequence, tgt_mwa_jobs_come_from_arrival_sequence.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (wcc_jcf_rel _ _ Hs)|].
    exact (wcc_jcf_rel _ _ (wcc_mwa _ _ Hs _ _ Ht)).
  Qed.

  Definition src_mwa_jobs_must_be_ready_to_execute : Prop :=
    ltac:(body_of (fun s : S.statement_mwa_jobs_must_be_ready_to_execute => s Job jaR jcR dlR arrR)).
  Definition tgt_mwa_jobs_must_be_ready_to_execute : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_mwa_jobs_must_be_ready_to_execute Job dJ jaL jcL dlL arrL)).

  Theorem mwa_jobs_must_be_ready_to_execute_correspondence :
    PropSPropRel src_mwa_jobs_must_be_ready_to_execute tgt_mwa_jobs_must_be_ready_to_execute.
  Proof.
    unfold src_mwa_jobs_must_be_ready_to_execute, tgt_mwa_jobs_must_be_ready_to_execute.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (wcc_jmbr_rel _ _ Hs)|].
    exact (wcc_jmbr_rel _ _ (wcc_mwa _ _ Hs _ _ Ht)).
  Qed.

  Definition src_mwa_all_deadlines_of_arrivals_met : Prop :=
    ltac:(body_of (fun s : S.statement_mwa_all_deadlines_of_arrivals_met => s Job jaR jcR dlR arrR)).
  Definition tgt_mwa_all_deadlines_of_arrivals_met : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_mwa_all_deadlines_of_arrivals_met Job dJ jaL jcL dlL arrL)).

  Theorem mwa_all_deadlines_of_arrivals_met_correspondence :
    PropSPropRel src_mwa_all_deadlines_of_arrivals_met tgt_mwa_all_deadlines_of_arrivals_met.
  Proof.
    unfold src_mwa_all_deadlines_of_arrivals_met, tgt_mwa_all_deadlines_of_arrivals_met.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (wcc_doa_rel _ _ Hs)|].
    exact (wcc_doa_rel _ _ (wcc_mwa _ _ Hs _ _ Ht)).
  Qed.

  Definition src_wc_transform_prefix_inclusion : Prop :=
    ltac:(body_of (fun s : S.statement_wc_transform_prefix_inclusion => s Job jaR dlR arrR)).
  Definition tgt_wc_transform_prefix_inclusion : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_wc_transform_prefix_inclusion Job dJ jaL dlL arrL)).

  Theorem wc_transform_prefix_inclusion_correspondence :
    PropSPropRel src_wc_transform_prefix_inclusion tgt_wc_transform_prefix_inclusion.
  Proof.
    unfold src_wc_transform_prefix_inclusion, tgt_wc_transform_prefix_inclusion.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros h1R h1L Hh1.
    apply ar_forall_nat_correspondence. intros h2R h2L Hh2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hh1 Hh2)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Ht Hh1)|].
    exact (wcc_opt_eq_correspondence _ _ _ _ (wcc_prefix _ _ Hs _ _ Hh1 _ _ Ht) (wcc_prefix _ _ Hs _ _ Hh2 _ _ Ht)).
  Qed.

  Definition src_wc_prefix_service_bound : Prop :=
    ltac:(body_of (fun s : S.statement_wc_prefix_service_bound => s Job jaR dlR arrR)).
  Definition tgt_wc_prefix_service_bound : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_wc_prefix_service_bound Job dJ jaL dlL arrL)).

  Theorem wc_prefix_service_bound_correspondence :
    PropSPropRel src_wc_prefix_service_bound tgt_wc_prefix_service_bound.
  Proof.
    unfold src_wc_prefix_service_bound, tgt_wc_prefix_service_bound.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (sub_nat_le_correspondence _ _ _ _ (wcc_service_related _ _ Hs j _ _ Ht)
      (wcc_service_related _ _ (wcc_transform _ _ Hs) j _ _ Ht)).
  Qed.

  Definition src_wc_prefix_job_meets_deadline : Prop :=
    ltac:(body_of (fun s : S.statement_wc_prefix_job_meets_deadline => s Job jaR jcR dlR arrR)).
  Definition tgt_wc_prefix_job_meets_deadline : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_wc_prefix_job_meets_deadline Job dJ jaL jcL dlL arrL)).

  Theorem wc_prefix_job_meets_deadline_correspondence :
    PropSPropRel src_wc_prefix_job_meets_deadline tgt_wc_prefix_job_meets_deadline.
  Proof.
    unfold src_wc_prefix_job_meets_deadline, tgt_wc_prefix_job_meets_deadline.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (wcc_doa_rel _ _ Hs)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (wcc_meets_rel _ _ (wcc_transform _ _ Hs) j).
  Qed.

  Definition src_wc_prefix_jobs_come_from_arrival_sequence : Prop :=
    ltac:(body_of (fun s : S.statement_wc_prefix_jobs_come_from_arrival_sequence => s Job jaR dlR arrR)).
  Definition tgt_wc_prefix_jobs_come_from_arrival_sequence : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_wc_prefix_jobs_come_from_arrival_sequence Job dJ jaL dlL arrL)).

  Theorem wc_prefix_jobs_come_from_arrival_sequence_correspondence :
    PropSPropRel src_wc_prefix_jobs_come_from_arrival_sequence tgt_wc_prefix_jobs_come_from_arrival_sequence.
  Proof.
    unfold src_wc_prefix_jobs_come_from_arrival_sequence, tgt_wc_prefix_jobs_come_from_arrival_sequence.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_imp_correspondence; [exact (wcc_jcf_rel _ _ Hs)|].
    exact (wcc_jcf_rel _ _ (wcc_prefix _ _ Hs _ _ Hh)).
  Qed.

  Definition src_wc_prefix_jobs_must_be_ready_to_execute : Prop :=
    ltac:(body_of (fun s : S.statement_wc_prefix_jobs_must_be_ready_to_execute => s Job jaR jcR dlR arrR)).
  Definition tgt_wc_prefix_jobs_must_be_ready_to_execute : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_wc_prefix_jobs_must_be_ready_to_execute
        Job dJ jaL jcL dlL arrL)).

  Theorem wc_prefix_jobs_must_be_ready_to_execute_correspondence :
    PropSPropRel src_wc_prefix_jobs_must_be_ready_to_execute tgt_wc_prefix_jobs_must_be_ready_to_execute.
  Proof.
    unfold src_wc_prefix_jobs_must_be_ready_to_execute, tgt_wc_prefix_jobs_must_be_ready_to_execute.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_imp_correspondence; [exact (wcc_jmbr_rel _ _ Hs)|].
    exact (wcc_jmbr_rel _ _ (wcc_prefix _ _ Hs _ _ Hh)).
  Qed.

  Definition src_wc_jobs_come_from_arrival_sequence : Prop :=
    ltac:(body_of (fun s : S.statement_wc_jobs_come_from_arrival_sequence => s Job jaR jcR dlR arrR)).
  Definition tgt_wc_jobs_come_from_arrival_sequence : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_wc_jobs_come_from_arrival_sequence Job dJ jaL jcL dlL arrL)).

  Theorem wc_jobs_come_from_arrival_sequence_correspondence :
    PropSPropRel src_wc_jobs_come_from_arrival_sequence tgt_wc_jobs_come_from_arrival_sequence.
  Proof.
    unfold src_wc_jobs_come_from_arrival_sequence, tgt_wc_jobs_come_from_arrival_sequence.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (wcc_valid_rel _ _ Hs)|].
    exact (wcc_jcf_rel _ _ (wcc_transform _ _ Hs)).
  Qed.

  Definition src_wc_jobs_must_be_ready_to_execute : Prop :=
    ltac:(body_of (fun s : S.statement_wc_jobs_must_be_ready_to_execute => s Job jaR jcR dlR arrR)).
  Definition tgt_wc_jobs_must_be_ready_to_execute : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_wc_jobs_must_be_ready_to_execute Job dJ jaL jcL dlL arrL)).

  Theorem wc_jobs_must_be_ready_to_execute_correspondence :
    PropSPropRel src_wc_jobs_must_be_ready_to_execute tgt_wc_jobs_must_be_ready_to_execute.
  Proof.
    unfold src_wc_jobs_must_be_ready_to_execute, tgt_wc_jobs_must_be_ready_to_execute.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (wcc_valid_rel _ _ Hs)|].
    exact (wcc_jmbr_rel _ _ (wcc_transform _ _ Hs)).
  Qed.

  Definition src_wc_all_deadlines_of_arrivals_met : Prop :=
    ltac:(body_of (fun s : S.statement_wc_all_deadlines_of_arrivals_met => s Job jaR jcR dlR arrR)).
  Definition tgt_wc_all_deadlines_of_arrivals_met : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_wc_all_deadlines_of_arrivals_met Job dJ jaL jcL dlL arrL)).

  Theorem wc_all_deadlines_of_arrivals_met_correspondence :
    PropSPropRel src_wc_all_deadlines_of_arrivals_met tgt_wc_all_deadlines_of_arrivals_met.
  Proof.
    unfold src_wc_all_deadlines_of_arrivals_met, tgt_wc_all_deadlines_of_arrivals_met.
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (wcc_doa_rel _ _ Hs)|].
    exact (wcc_doa_rel _ _ (wcc_transform _ _ Hs)).
  Qed.

  Definition src_wc_is_work_conserving_at : Prop :=
    ltac:(body_of (fun s : S.statement_wc_is_work_conserving_at => s Job jaR jcR dlR arrR)).
  Definition tgt_wc_is_work_conserving_at : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_wc_is_work_conserving_at Job dJ jaL jcL dlL arrL)).

  Theorem wc_is_work_conserving_at_correspondence :
    PropSPropRel src_wc_is_work_conserving_at tgt_wc_is_work_conserving_at.
  Proof.
    unfold src_wc_is_work_conserving_at, tgt_wc_is_work_conserving_at.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (wcc_doa_rel _ _ Hs)|].
    have Hw := wcc_transform _ _ Hs.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (wcc_ready _ _ Hw j _ _ Ht)|].
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply wcc_exists_identity_correspondence. intro j'.
    exact (wcc_opt_eq_correspondence _ _ _ _ (Hw _ _ Ht) (wcc_opt_rel_canonical (Some j'))).
  Qed.

  Definition src_wc_is_work_conserving : Prop :=
    ltac:(body_of (fun s : S.statement_wc_is_work_conserving => s Job jaR jcR dlR arrR)).
  Definition tgt_wc_is_work_conserving : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_wc_is_work_conserving Job dJ jaL jcL dlL arrL)).

  Theorem wc_is_work_conserving_correspondence :
    PropSPropRel src_wc_is_work_conserving tgt_wc_is_work_conserving.
  Proof.
    unfold src_wc_is_work_conserving, tgt_wc_is_work_conserving.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (wcc_doa_rel _ _ Hs)|].
    exact (wcc_wc_rel _ _ (wcc_transform _ _ Hs)).
  Qed.

  Definition src_wc_transform_correctness : Prop :=
    ltac:(body_of (fun s : S.statement_wc_transform_correctness => s Job jaR jcR dlR arrR)).
  Definition tgt_wc_transform_correctness : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_WcCorrectness_wc_transform_correctness Job dJ jaL jcL dlL arrL)).

  Theorem wc_transform_correctness_correspondence :
    PropSPropRel src_wc_transform_correctness tgt_wc_transform_correctness.
  Proof.
    unfold src_wc_transform_correctness, tgt_wc_transform_correctness.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply wcc_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (wcc_valid_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (wcc_doa_rel _ _ Hs)|].
    have Hw := wcc_transform _ _ Hs.
    apply ar_and_correspondence; [exact (wcc_valid_rel _ _ Hw)|].
    apply ar_and_correspondence; [exact (wcc_doa_rel _ _ Hw)|].
    exact (wcc_wc_rel _ _ Hw).
  Qed.
End WcCorrectness.
