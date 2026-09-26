From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import PreemptionAwareSemanticSource.
From prosa Require Import model.processor.ideal model.schedule.work_conserving
  implementation.definitions.generic_scheduler.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPrioAware ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  IdealUniSchedulerCorrespondence.

Module I := ImportedPrioAware.
Module S := PreemptionAwareSemanticSource.PreemptionAwareSemanticSource.
Module U := IdealUniSchedulerSemanticSource.IdealUniSchedulerSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module RS := ReadinessSemanticSource.ReadinessSemanticSource.
Module LP := ScheduleLimitedPreemptiveSemanticSource.ScheduleLimitedPreemptiveSemanticSource.
Module PT := PreemptionTimeSemanticSource.PreemptionTimeSemanticSource.

(** Helper certificates of [implementation/facts/ideal_uni/preemption_aware.v] (its accepted
    PreemptionAwareCorrespondence up to, and excluding, its statement correspondences, whose
    target statements are not part of this export), re-bound to this export.

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.  The
    processor model is fixed to the ideal uniprocessor on both sides: states
    are related by the constructor-preserving Option map and schedules
    pointwise ([IdScheduleRel] of the accepted scheduler certificate);
    [job_cost] by [SvcJobCostRel], [job_arrival] by [ArJobArrivalRel], arrival
    sequences by [ArArrivalSequenceRel]; the readiness model by its
    [job_ready] on related schedules and instants, the preemption model
    pointwise ([PpJobPreemptableRel]), [choose_job] on related instants and
    job lists.  Inputs quantified inside a statement are covered in both
    directions: schedules, job lists, preemption models and [choose_job]
    functions by explicit conversions; readiness models (always quantified
    together with the [nonclairvoyant_readiness] hypothesis) among
    nonclairvoyant models, whose [job_ready] respects pointwise-equal
    schedules, by readiness models built from the other side's [job_ready]
    with the pending obligation transported through the related [pending]
    (so no functional extensionality is needed).  The scheduler definitions
    are related by the accepted scheduler certificate; [preemption_time] and
    [scheduled_job_at] through the accepted filter and [arrivals_up_to]
    certificates.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators *)

Lemma pa_forall_cover (A B : Type) (Rel : A -> B -> SProp)
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

(** A cover restricted to the inputs satisfying a related side condition. *)
Lemma pa_forall_cond_cover (A B : Type) (Rel : A -> B -> SProp)
    (PA : A -> Prop) (PB : B -> SProp) (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, PA a -> Rel a (toB a)) (HtoA : forall b, PB b -> Rel (toA b) b)
    (QA : A -> Prop) (QB : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PA a) (PB b)) ->
  (forall a b, Rel a b -> PropSPropRel (QA a) (QB b)) ->
  PropSPropRel (forall a, PA a -> QA a) (forall b, PB b -> QB b).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros HR b pb.
    have Hr := HtoA b pb.
    exact (prop_to_sprop _ _ (HQ _ _ Hr) (HR (toA b) (sprop_to_prop _ _ (HP _ _ Hr) pb))).
  - intro HL. apply strictly_inhabits. intros a pa.
    have Hr := HtoB a pa.
    exact (sprop_to_prop _ _ (HQ _ _ Hr) (HL (toB a) (prop_to_sprop _ _ (HP _ _ Hr) pa))).
Qed.

Lemma pa_exists_identity_correspondence (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x.
    exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma pa_bool_eq_correspondence (bR cR : bool) (bL cL : I.Bool) :
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

Lemma pa_bool_true_elim (b : bool) (G : SProp) :
  Lean.eq (svc_bool_to_imported b) I.Bool_true -> (b = true -> G) -> G.
Proof.
  destruct b; intros H K; first exact (K (erefl true)).
  exact (id_lean_transport
    (fun x => match x with
              | I.Bool_true => G
              | I.Bool_false => Lean.eq I.Bool_false I.Bool_false
              end) _ _ H (@Lean.eq_refl _ _)).
Qed.

Lemma pa_true_of_rocq (bL : I.Bool) : svc_bool_to_rocq bL = true -> Lean.eq bL I.Bool_true.
Proof. destruct bL; cbn; intro H; solve [discriminate H | exact (@Lean.eq_refl _ _)]. Qed.

Lemma pa_list_input {T : Type} (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL -> Logic.eq (ar_list_to_rocq xsL) xsR.
Proof.
  intro H. have E := f_equal ar_list_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite ar_list_source_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma pa_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xsR xsL, ArListRel xsR xsL -> PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (forall xs, PR xs) (forall xs, PL xs).
Proof.
  exact (pa_forall_cover _ _ ArListRel ar_list_to_imported ar_list_to_rocq
    (fun xs => @Lean.eq_refl _ _) ar_list_target_roundtrip PR PL).
Qed.

(** ** The ideal uniprocessor *)

Section PreemptionAware.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.
  Let SchedR := @prosa.behavior.schedule.schedule Job PSR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.

  (** *** Schedule covers *)

  Definition pa_sched_to_target (sR : SchedR) : SchedL :=
    fun tL => id_opt_to_imported (sR (sub_nat_to_rocq tL)).

  Definition pa_sched_to_source (sL : SchedL) : SchedR :=
    fun tR => id_opt_to_rocq (sL (sub_nat_to_imported tR)).

  Lemma pa_sched_to_target_rel sR : IdScheduleRel Job sR (pa_sched_to_target sR).
  Proof.
    intros tR tL Ht. unfold IdOptRel, pa_sched_to_target.
    rewrite (id_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma pa_sched_to_source_rel sL : IdScheduleRel Job (pa_sched_to_source sL) sL.
  Proof.
    intros tR tL Ht.
    exact (sub_imported_eq_trans _ _ _ (id_opt_target_roundtrip _) (sub_imported_eq_congr sL _ _ Ht)).
  Qed.

  Lemma pa_forall_sched (PR : SchedR -> Prop) (PL : SchedL -> SProp) :
    (forall sR sL, IdScheduleRel Job sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    exact (pa_forall_cover _ _ (IdScheduleRel Job) pa_sched_to_target pa_sched_to_source
      pa_sched_to_target_rel pa_sched_to_source_rel PR PL).
  Qed.

  Lemma pa_pointwise (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL) (t : nat) :
    sR t = pa_sched_to_source sL t.
  Proof.
    have E := f_equal id_opt_to_rocq (imported_eq_to_coq_eq _ _ (Hs t _ (sub_nat_rel_canonical t))).
    rewrite id_opt_source_roundtrip in E. exact E.
  Qed.

  Lemma pa_ideal_is_idle_related (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL)
      (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
    SvcBoolRel (prosa.model.processor.ideal.ideal_is_idle sR tR)
      (I.Prosa_Model_Processor_Ideal_ideal_is_idle Job dJ sL tL).
  Proof.
    unfold prosa.model.processor.ideal.ideal_is_idle.
    cbn [I.Prosa_Model_Processor_Ideal_ideal_is_idle].
    refine (id_lean_transport (fun y => SvcBoolRel (sR tR == None)
      (I.Prosa_Model_Processor_Ideal_ideal_is_idle_match_1 Job dJ (fun _ => I.Bool) y
        (fun _ => I.Bool_true) (fun _ => I.Bool_false))) _ _ (Hs tR tL Ht) _).
    destruct (sR tR); exact (@Lean.eq_refl _ _).
  Qed.

  Lemma pa_identical_prefix_rel (s1R s2R : SchedR) (s1L s2L : SchedL)
      (H1 : IdScheduleRel Job s1R s1L) (H2 : IdScheduleRel Job s2R s2L)
      (hR : nat) (hL : Lean.Nat) (Hh : SubNatRel hR hL) :
    PropSPropRel (prosa.analysis.definitions.schedule_prefix.identical_prefix s1R s2R hR)
      (I.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix_inst4 Job dJ PSL s1L s2L hL).
  Proof.
    unfold prosa.analysis.definitions.schedule_prefix.identical_prefix.
    cbn [I.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix_inst4].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Ht Hh)|].
    exact (id_opt_eq_correspondence _ _ _ _ (H1 _ _ Ht) (H2 _ _ Ht)).
  Qed.

  (** *** Job parameters and the arrival sequence *)

  Variable jcR : prosa.behavior.job.JobCost Job.
  Variable jcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hjc : SvcJobCostRel Job jcR jcL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let RMR := @prosa.behavior.ready.JobReady Job PSR jcR jaR.
  Let RML := I.Prosa_Behavior_Ready_JobReady_inst4 Job dJ PSL jcL jaL.

  Definition PaReadyRel (rmR : RMR) (rmL : RML) : SProp :=
    forall sR sL, IdScheduleRel Job sR sL -> forall (j : Job) tR tL, SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.ready.job_ready Job PSR jcR jaR rmR sR j tR)
        (I.Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job dJ PSL jcL jaL rmL sL j tL).

  Definition PaChooseRel (cjR : nat -> seq Job -> option Job)
      (cjL : I.Prosa_Behavior_Time_instant -> I.List Job -> I.Option Job) : SProp :=
    forall tR tL, SubNatRel tR tL -> forall xsR xsL, ArListRel xsR xsL ->
      IdOptRel (cjR tR xsR) (cjL tL xsL).

  Lemma pa_pending_related (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL)
      (j : Job) (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
    SvcBoolRel (@prosa.behavior.service.pending Job PSR sR jcR jaR j tR)
      (I.Prosa_Behavior_Service_pending_inst4 Job dJ PSL sL jcL jaL j tL).
  Proof.
    unfold prosa.behavior.service.pending, prosa.behavior.service.completed_by.
    cbn [I.Prosa_Behavior_Service_pending_inst4
      I.Prosa_Validation_ServiceInterface_completedByProjection_inst4].
    exact (ar_bool_and_related _ _ _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)
      (svc_bool_not_related _ _ (svc_decide_le_related _ _ _ _ (Hjc j)
        (iu_service_related Job sR sL Hs j tR tL Ht)))).
  Qed.

  (** *** Readiness-model covers among nonclairvoyant models *)

  Definition pa_ready_pending (rm : RMR) :
    forall s j t, @prosa.behavior.ready.job_ready Job PSR jcR jaR rm s j t ->
      @prosa.behavior.service.pending Job PSR s jcR jaR j t :=
    match rm as r return
      (forall s j t, @prosa.behavior.ready.job_ready Job PSR jcR jaR r s j t ->
        @prosa.behavior.service.pending Job PSR s jcR jaR j t) with
    | prosa.behavior.ready.Build_JobReady _ H => H
    end.

  Definition pa_ready_to_target (rmR : RMR) : RML.
  Proof.
    refine (I.Prosa_Behavior_Ready_JobReady_mk_inst4 Job dJ PSL jcL jaL
      (fun sL j tL => svc_bool_to_imported
        (@prosa.behavior.ready.job_ready Job PSR jcR jaR rmR (pa_sched_to_source sL) j (sub_nat_to_rocq tL))) _).
    intros sL j tL H.
    apply (pa_bool_true_elim _ _ H). intro E.
    exact (prop_to_sprop _ _ (svc_bool_truth_correspondence _ _
      (pa_pending_related _ _ (pa_sched_to_source_rel sL) j _ _ (sub_nat_rel_surjective tL)))
      (pa_ready_pending rmR _ _ _ E)).
  Defined.

  Definition pa_ready_to_source (rmL : RML) : RMR.
  Proof.
    refine (@prosa.behavior.ready.Build_JobReady Job PSR jcR jaR
      (fun sR j tR => svc_bool_to_rocq
        (I.Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job dJ PSL jcL jaL rmL
          (pa_sched_to_target sR) j (sub_nat_to_imported tR))) _).
    intros sR j tR H.
    have P := I.ready_implies_pending0 _ _ _ _ _ rmL (pa_sched_to_target sR) j (sub_nat_to_imported tR)
      (pa_true_of_rocq _ H).
    exact (sprop_to_prop _ _ (svc_bool_truth_correspondence _ _
      (pa_pending_related _ _ (pa_sched_to_target_rel sR) j _ _ (sub_nat_rel_canonical tR))) P).
  Defined.

  Let NCR (rmR : RMR) : Prop := @RS.nonclairvoyant_readiness Job jcR jaR PSR rmR.
  Let NCL (rmL : RML) : SProp :=
    I.Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness_inst4 Job dJ jcL jaL PSL rmL.

  Lemma pa_ready_to_target_rel (rmR : RMR) : NCR rmR -> PaReadyRel rmR (pa_ready_to_target rmR).
  Proof.
    intros NC sR sL Hs j tR tL Ht.
    change (Lean.eq (svc_bool_to_imported (@prosa.behavior.ready.job_ready Job PSR jcR jaR rmR sR j tR))
      (svc_bool_to_imported (@prosa.behavior.ready.job_ready Job PSR jcR jaR rmR
        (pa_sched_to_source sL) j (sub_nat_to_rocq tL)))).
    rewrite (id_nat_input _ _ Ht).
    rewrite (NC sR (pa_sched_to_source sL) j tR (fun t _ => pa_pointwise sR sL Hs t) tR (leqnn tR)).
    exact (@Lean.eq_refl _ _).
  Qed.

  Lemma pa_ready_to_source_rel (rmL : RML) : NCL rmL -> PaReadyRel (pa_ready_to_source rmL) rmL.
  Proof.
    intros NC sR sL Hs j tR tL Ht.
    refine (sub_imported_eq_trans _ _ _ (svc_bool_target_roundtrip _) _).
    destruct Ht.
    exact (NC (pa_sched_to_target sR) sL j (sub_nat_to_imported tR)
      (fun t _ => Hs _ t (sub_nat_rel_surjective t)) (sub_nat_to_imported tR)
      (prop_to_sprop _ _ (sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical tR)
        (sub_nat_rel_canonical tR)) (leqnn tR))).
  Qed.

  Lemma pa_nonclair_rel (rmR : RMR) (rmL : RML) (Hrm : PaReadyRel rmR rmL) :
    PropSPropRel (NCR rmR) (NCL rmL).
  Proof.
    unfold NCR, NCL, RS.nonclairvoyant_readiness.
    cbn [I.Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness_inst4].
    apply pa_forall_sched. intros s1R s1L H1.
    apply pa_forall_sched. intros s2R s2L H2.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_imp_correspondence; [exact (pa_identical_prefix_rel _ _ _ _ H1 H2 _ _ Hh)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Hh)|].
    exact (pa_bool_eq_correspondence _ _ _ _ (Hrm _ _ H1 j _ _ Ht) (Hrm _ _ H2 j _ _ Ht)).
  Qed.

  Lemma pa_forall_nonclair_ready (QA : RMR -> Prop) (QB : RML -> SProp) :
    (forall rmR rmL, PaReadyRel rmR rmL -> PropSPropRel (QA rmR) (QB rmL)) ->
    PropSPropRel (forall rmR, NCR rmR -> QA rmR) (forall rmL, NCL rmL -> QB rmL).
  Proof.
    exact (pa_forall_cond_cover _ _ PaReadyRel NCR NCL pa_ready_to_target pa_ready_to_source
      pa_ready_to_target_rel pa_ready_to_source_rel QA QB pa_nonclair_rel).
  Qed.

  (** *** Preemption-model and [choose_job] covers *)

  Lemma pa_forall_preemptable (QA : PP.JobPreemptable Job -> Prop)
      (QB : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ -> SProp) :
    (forall jpR jpL, PpJobPreemptableRel Job jpR jpL -> PropSPropRel (QA jpR) (QB jpL)) ->
    PropSPropRel (forall jp, QA jp) (forall jp, QB jp).
  Proof.
    exact (pa_forall_cover _ _ (PpJobPreemptableRel Job)
      (fun jpR => I.Prosa_Model_Preemption_Parameter_JobPreemptable_mk Job dJ
        (fun j nL => ar_bool_to_imported (jpR j (sub_nat_to_rocq nL))))
      (fun jpL => (fun j n => ar_bool_to_rocq
        (I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job dJ jpL j
          (sub_nat_to_imported n))) : PP.JobPreemptable Job)
      (JobPreemptable_source_total Job) (JobPreemptable_target_total Job) QA QB).
  Qed.

  Definition pa_choose_to_target (cjR : nat -> seq Job -> option Job) :
      I.Prosa_Behavior_Time_instant -> I.List Job -> I.Option Job :=
    fun tL xsL => id_opt_to_imported (cjR (sub_nat_to_rocq tL) (ar_list_to_rocq xsL)).

  Definition pa_choose_to_source
      (cjL : I.Prosa_Behavior_Time_instant -> I.List Job -> I.Option Job) :
      nat -> seq Job -> option Job :=
    fun tR xsR => id_opt_to_rocq (cjL (sub_nat_to_imported tR) (ar_list_to_imported xsR)).

  Lemma pa_choose_to_target_rel cjR : PaChooseRel cjR (pa_choose_to_target cjR).
  Proof.
    intros tR tL Ht xsR xsL Hxs. unfold IdOptRel, pa_choose_to_target.
    rewrite (id_nat_input _ _ Ht) (pa_list_input _ _ Hxs). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma pa_choose_to_source_rel cjL : PaChooseRel (pa_choose_to_source cjL) cjL.
  Proof.
    intros tR tL Ht xsR xsL Hxs.
    refine (sub_imported_eq_trans _ _ _ (id_opt_target_roundtrip _) _).
    destruct Ht. destruct Hxs. exact (@Lean.eq_refl _ _).
  Qed.

  Lemma pa_forall_choose (QA : (nat -> seq Job -> option Job) -> Prop)
      (QB : (I.Prosa_Behavior_Time_instant -> I.List Job -> I.Option Job) -> SProp) :
    (forall cjR cjL, PaChooseRel cjR cjL -> PropSPropRel (QA cjR) (QB cjL)) ->
    PropSPropRel (forall cj, QA cj) (forall cj, QB cj).
  Proof.
    exact (pa_forall_cover _ _ PaChooseRel pa_choose_to_target pa_choose_to_source
      pa_choose_to_target_rel pa_choose_to_source_rel QA QB).
  Qed.

  (** *** Hypotheses on [choose_job] *)

  Lemma pa_non_idling_rel cjR cjL (Hcj : PaChooseRel cjR cjL) :
    PropSPropRel (forall (t : nat) (s : seq Job), cjR t s = None <-> s = [::])
      (forall tL sL, I.Iff (Lean.eq (cjL tL sL) (I.Option_none Job)) (Lean.eq sL (I.List_nil Job))).
  Proof.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply pa_forall_list. intros xsR xsL Hxs.
    apply pp_iff_correspondence.
    - exact (id_opt_eq_correspondence _ _ _ _ (Hcj _ _ Ht _ _ Hxs) (@Lean.eq_refl _ _)).
    - exact (ar_list_eq_correspondence _ _ _ _ _ Hxs (@Lean.eq_refl _ _)).
  Qed.

  Lemma pa_chooses_from_rel cjR cjL (Hcj : PaChooseRel cjR cjL) :
    PropSPropRel (forall (t : nat) (s : seq Job) (j : Job), cjR t s = Some j -> j \in s)
      (forall tL sL (j : Job), Lean.eq (cjL tL sL) (I.Option_some Job j) ->
        Lean.eq (ar_target_decide_mem Job j sL) I.Bool_true).
  Proof.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply pa_forall_list. intros xsR xsL Hxs.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence.
    - exact (id_opt_eq_correspondence _ _ _ _ (Hcj _ _ Ht _ _ Hxs) (@Lean.eq_refl _ _)).
    - exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Job j _ _ Hxs)).
  Qed.

  (** *** The scheduler at related inputs *)

  Section Scheduler.
    Variable rmR : RMR.
    Variable rmL : RML.
    Hypothesis Hrm : PaReadyRel rmR rmL.
    Variable jpR : PP.JobPreemptable Job.
    Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
    Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.
    Variable cjR : nat -> seq Job -> option Job.
    Variable cjL : I.Prosa_Behavior_Time_instant -> I.List Job -> I.Option Job.
    Hypothesis Hcj : PaChooseRel cjR cjL.

    Let PMCR := @U.pmc_uni_schedule Job jcR jaR arrR rmR jpR cjR.
    Let PMCL := I.Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule Job dJ jcL jaL arrL rmL jpL cjL.

    Lemma pa_pmc_related : IdScheduleRel Job PMCR PMCL.
    Proof.
      exact (pmc_uni_schedule_correspondence Job jcR jcL jaR jaL rmR rmL Hrm jpR jpL Hjp
        arrR arrL Harr cjR cjL Hcj).
    Qed.

    Lemma pa_alloc_related sR sL (Hs : IdScheduleRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
      IdOptRel (@U.allocation_at Job jcR jaR arrR rmR jpR cjR sR tR)
        (I.Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at Job dJ jcL jaL arrL rmL jpL cjL sL tL).
    Proof.
      exact (allocation_at_correspondence Job jcR jcL jaR jaL rmR rmL Hrm jpR jpL Hjp
        arrR arrL Harr cjR cjL Hcj sR sL tR tL Hs Ht).
    Qed.

    Lemma pa_sut_related (hR : nat) (hL : Lean.Nat) (Hh : SubNatRel hR hL) :
      IdScheduleRel Job
        (prosa.implementation.definitions.generic_scheduler.schedule_up_to
          (@U.allocation_at Job jcR jaR arrR rmR jpR cjR) None hR)
        (I.Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to_inst2 Job dJ PSL
          (I.Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at Job dJ jcL jaL arrL rmL jpL cjL)
          (I.Option_none Job) hL).
    Proof.
      destruct Hh. exact (iu_sut_canonical Job _ _ pa_alloc_related hR).
    Qed.

    Lemma pa_preemption_time_related sR sL (Hs : IdScheduleRel Job sR sL)
        (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
      SvcBoolRel (@PT.preemption_time Job jpR arrR PSR sR tR)
        (I.Prosa_Model_Schedule_PreemptionTime_preemption_time_inst4 Job dJ jpL arrL PSL sL tL).
    Proof.
      have Hl : ArListRel (prosa.model.schedule.scheduled.scheduled_jobs_at arrR sR tR)
          (I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at_inst4 Job dJ PSL arrL sL tL) :=
        ar_filter_related Job (fun j => prosa.behavior.service.scheduled_at sR j tR)
          (fun j => I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL sL j tL) _ _
          (fun j => iu_scheduled_at_related Job sR sL Hs j tR tL Ht)
          (arrivals_up_to_correspondence_certificate Job arrR arrL Harr tR tL Ht).
      assert (Hsj : IdOptRel (prosa.model.schedule.scheduled.scheduled_job_at arrR sR tR)
          (I.Prosa_Model_Schedule_Scheduled_scheduled_job_at_inst4 Job dJ PSL arrL sL tL)).
      { unfold prosa.model.schedule.scheduled.scheduled_job_at.
        cbn [I.Prosa_Model_Schedule_Scheduled_scheduled_job_at_inst4].
        refine (id_lean_transport (fun y => IdOptRel
          (ohead (prosa.model.schedule.scheduled.scheduled_jobs_at arrR sR tR)) (I.List_head__q Job y))
          _ _ Hl _).
        destruct (prosa.model.schedule.scheduled.scheduled_jobs_at arrR sR tR);
          exact (@Lean.eq_refl _ _). }
      unfold PT.preemption_time.
      cbn [I.Prosa_Model_Schedule_PreemptionTime_preemption_time_inst4].
      refine (id_lean_transport (fun y => SvcBoolRel
        (if prosa.model.schedule.scheduled.scheduled_job_at arrR sR tR is Some j then
           @PP.job_preemptable Job jpR j (prosa.behavior.service.service sR j tR)
         else true)
        (I.Prosa_Model_Schedule_PreemptionTime_preemption_time_match_1 Job (fun _ => I.Bool) y
          (fun j => I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job dJ jpL j
            (I.Prosa_Behavior_Service_service_inst4 Job dJ PSL sL j tL))
          (fun _ => I.Bool_true))) _ _ Hsj _).
      destruct (prosa.model.schedule.scheduled.scheduled_job_at arrR sR tR) as [j|].
      - exact (Hjp j _ _ (iu_service_related Job sR sL Hs j tR tL Ht)).
      - exact (@Lean.eq_refl _ _).
    Qed.

    Lemma pa_jobs_come_from_rel sR sL (Hs : IdScheduleRel Job sR sL) :
      PropSPropRel (prosa.behavior.ready.jobs_come_from_arrival_sequence sR arrR)
        (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job dJ PSL sL arrL).
    Proof.
      unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
      cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job sR sL Hs j tR tL Ht))|].
      exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    Qed.

    Lemma pa_must_be_ready_rel sR sL (Hs : IdScheduleRel Job sR sL) :
      PropSPropRel (@prosa.behavior.ready.jobs_must_be_ready_to_execute Job jaR PSR sR jcR rmR)
        (I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst4 Job dJ jaL PSL sL jcL rmL).
    Proof.
      unfold prosa.behavior.ready.jobs_must_be_ready_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job sR sL Hs j tR tL Ht))|].
      exact (svc_bool_truth_correspondence _ _ (Hrm _ _ Hs j _ _ Ht)).
    Qed.
  End Scheduler.

  (** The inlined prefix [match t with 0 => empty_schedule None | t'.+1 => schedule_up_to _ None t' end]:
      the target matcher reduces on the canonical constructors. *)
  Ltac pa_prefix Ht Hrm Hjp Hcj :=
    destruct Ht;
    match goal with
    | |- IdScheduleRel _ (match ?t with _ => _ end) _ =>
        destruct t as [|t'];
        [ exact (iu_empty_related Job)
        | exact (iu_sut_canonical Job _ _ (pa_alloc_related _ _ Hrm _ _ Hjp _ _ Hcj) t') ]
    end.

End PreemptionAware.
