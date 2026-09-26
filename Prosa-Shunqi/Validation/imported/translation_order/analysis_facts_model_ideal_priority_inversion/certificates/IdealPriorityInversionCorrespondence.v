From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import IdealPriorityInversionSemanticSource.
From prosa Require Import model.processor.ideal model.schedule.scheduled.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdealPriorityInversion ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PriorityInversionCorrespondence.

Module I := ImportedIdealPriorityInversion.
Module S := IdealPriorityInversionSemanticSource.IdealPriorityInversionSemanticSource.
Module PI := PriorityInversionSemanticSource.PriorityInversionSemanticSource.

(** Statement correspondences for [analysis/facts/model/ideal/priority_inversion.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.  The
    processor model is fixed to the ideal uniprocessor on both sides: states
    are related by the constructor-preserving Option map, schedules pointwise
    (covered in both directions); [job_arrival] by [ArJobArrivalRel], arrival
    sequences by [ArArrivalSequenceRel]; JLFP policies pointwise on Booleans
    (covered in both directions).  The source-side closed form of
    [scheduled_in] on the ideal state is re-proved from the definitions; the
    target side uses the accepted kernel-checked Lean equation
    [production_ideal_scheduled_in] of the ideal-schedule interface.
    [priority_inversion] is related through the accepted filter,
    [arrivals_up_to], membership and [has] certificates.  No source or target
    theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators *)

Lemma ipi_forall_cover (A B : Type) (Rel : A -> B -> SProp)
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

Lemma ipi_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma ipi_bool_eq_correspondence (bR cR : bool) (bL cL : I.Bool) :
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

(** ** Ideal states *)

Definition ipi_opt_to_imported {T : Type} (x : option T) : I.Option T :=
  match x with
  | None => I.Option_none T
  | Some j => I.Option_some T j
  end.

Definition ipi_opt_to_rocq {T : Type} (y : I.Option T) : option T :=
  match y with
  | I.Option_none => None
  | I.Option_some j => Some j
  end.

Definition IpiOptRel {T : Type} (x : option T) (y : I.Option T) : SProp :=
  Lean.eq (ipi_opt_to_imported x) y.

Lemma ipi_opt_target_roundtrip {T : Type} (y : I.Option T) :
  Lean.eq (ipi_opt_to_imported (ipi_opt_to_rocq y)) y.
Proof. destruct y; cbn; exact (@Lean.eq_refl _ _). Qed.

Lemma ipi_option_some_eq_correspondence (T : eqType) (s : option T) (j : T) :
  PropSPropRel (is_true (s == Some j))
    (Lean.eq (ipi_opt_to_imported s) (I.Option_some T j)).
Proof.
  apply prop_sprop_rel_intro.
  - intro H. move/eqP: H => ->. exact (@Lean.eq_refl _ _).
  - intro H. apply strictly_inhabits.
    have Hcoq := imported_eq_to_coq_eq _ _ H.
    destruct s as [k|]; cbn in Hcoq.
    + injection Hcoq as Hkj. subst k. exact (eqxx (Some j)).
    + discriminate Hcoq.
Qed.

Section Ideal.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.
  Let SchedR := @prosa.behavior.schedule.schedule Job PSR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.

  Local Transparent prosa.behavior.schedule.scheduled_on.

  Lemma ipi_src_scheduled_on (j : Job) (s : option Job) (c : unit) :
    @prosa.behavior.schedule.scheduled_on Job PSR j s c = (s == Some j).
  Proof. by []. Qed.

  Lemma ipi_src_scheduled_in (j : Job) (s : option Job) :
    @prosa.behavior.schedule.scheduled_in Job PSR j s = (s == Some j).
  Proof.
    rewrite /prosa.behavior.schedule.scheduled_in.
    apply/existsP/idP => [[c]|H].
    - by rewrite ipi_src_scheduled_on.
    - by exists tt; rewrite ipi_src_scheduled_on.
  Qed.

  Lemma ipi_scheduled_in_related (j : Job) (sR : option Job) sL :
    IpiOptRel sR sL ->
    SvcBoolRel (@prosa.behavior.schedule.scheduled_in Job PSR j sR)
      (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst4 Job dJ PSL j sL).
  Proof.
    intro Hs. destruct Hs. rewrite ipi_src_scheduled_in.
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_IdealScheduleInterface_production_ideal_scheduled_in Job dJ j _))).
    cbn. apply ar_decide_bool_correspondence.
    exact (ipi_option_some_eq_correspondence Job sR j).
  Qed.

  (** *** Schedules *)

  Definition IpiScheduleRel (sR : SchedR) (sL : SchedL) : SProp :=
    forall tR tL, SubNatRel tR tL -> IpiOptRel (sR tR) (sL tL).

  Definition ipi_sched_to_target (sR : SchedR) : SchedL :=
    fun tL => ipi_opt_to_imported (sR (sub_nat_to_rocq tL)).

  Definition ipi_sched_to_source (sL : SchedL) : SchedR :=
    fun tR => ipi_opt_to_rocq (sL (sub_nat_to_imported tR)).

  Lemma ipi_sched_to_target_rel sR : IpiScheduleRel sR (ipi_sched_to_target sR).
  Proof.
    intros tR tL Ht. unfold IpiOptRel, ipi_sched_to_target.
    rewrite (ipi_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma ipi_sched_to_source_rel sL : IpiScheduleRel (ipi_sched_to_source sL) sL.
  Proof.
    intros tR tL Ht.
    exact (sub_imported_eq_trans _ _ _ (ipi_opt_target_roundtrip _) (sub_imported_eq_congr sL _ _ Ht)).
  Qed.

  Lemma ipi_forall_sched (PR : SchedR -> Prop) (PL : SchedL -> SProp) :
    (forall sR sL, IpiScheduleRel sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    exact (ipi_forall_cover _ _ IpiScheduleRel ipi_sched_to_target ipi_sched_to_source
      ipi_sched_to_target_rel ipi_sched_to_source_rel PR PL).
  Qed.

  (** *** JLFP policies *)

  Definition IpiJlfpRel (pR : prosa.model.priority.definitions.JLFP_policy Job)
      (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ) : SProp :=
    forall x y : Job,
      SvcBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
        (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Definition ipi_jlfp_to_target (pR : prosa.model.priority.definitions.JLFP_policy Job) :
      I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ :=
    I.Prosa_Model_Priority_Definitions_JLFP_policy_mk Job dJ
      (fun x y => svc_bool_to_imported (@prosa.model.priority.definitions.hep_job Job pR x y)).

  Definition ipi_jlfp_to_source (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ) :
      prosa.model.priority.definitions.JLFP_policy Job :=
    ((fun x y => svc_bool_to_rocq (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y))
      : prosa.model.priority.definitions.JLFP_policy Job).

  Lemma ipi_jlfp_to_target_rel pR : IpiJlfpRel pR (ipi_jlfp_to_target pR).
  Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

  Lemma ipi_jlfp_to_source_rel pL : IpiJlfpRel (ipi_jlfp_to_source pL) pL.
  Proof. intros x y. exact (svc_bool_target_roundtrip _). Qed.

  Lemma ipi_forall_jlfp (QA : prosa.model.priority.definitions.JLFP_policy Job -> Prop)
      (QB : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ -> SProp) :
    (forall pR pL, IpiJlfpRel pR pL -> PropSPropRel (QA pR) (QB pL)) ->
    PropSPropRel (forall p, QA p) (forall p, QB p).
  Proof.
    exact (ipi_forall_cover _ _ IpiJlfpRel ipi_jlfp_to_target ipi_jlfp_to_source
      ipi_jlfp_to_target_rel ipi_jlfp_to_source_rel QA QB).
  Qed.

  Lemma ipi_reflexive_rel pR pL (Hp : IpiJlfpRel pR pL) :
    PropSPropRel (prosa.model.priority.definitions.reflexive_job_priorities pR)
      (I.Prosa_Model_Priority_Definitions_reflexive_job_priorities Job dJ pL).
  Proof.
    unfold prosa.model.priority.definitions.reflexive_job_priorities, ssrbool.reflexive.
    cbn [I.Prosa_Model_Priority_Definitions_reflexive_job_priorities].
    apply ar_forall_identity_correspondence. intro x.
    exact (svc_bool_truth_correspondence _ _ (Hp x x)).
  Qed.

  (** *** Job arrivals, the arrival sequence and related schedules *)

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : IpiScheduleRel sR sL.

    Lemma ipi_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PSR sR j tR)
        (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL sL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.scheduled_at.
      cbn [I.Prosa_Behavior_Service_scheduled_at_inst4].
      exact (ipi_scheduled_in_related j _ _ (Hs tR tL Ht)).
    Qed.

    Lemma ipi_ideal_is_idle_related (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.model.processor.ideal.ideal_is_idle Job sR tR)
        (I.Prosa_Model_Processor_Ideal_ideal_is_idle Job dJ sL tL).
    Proof.
      intro Ht. have H := Hs tR tL Ht. unfold IpiOptRel in H.
      unfold prosa.model.processor.ideal.ideal_is_idle.
      unfold I.Prosa_Model_Processor_Ideal_ideal_is_idle.
      revert H. generalize (sL tL). intros x H.
      destruct H. destruct (sR tR); cbn; exact (@Lean.eq_refl _ _).
    Qed.

    Lemma ipi_jobs_come_from_rel :
      PropSPropRel (prosa.behavior.ready.jobs_come_from_arrival_sequence sR arrR)
        (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job dJ PSL sL arrL).
    Proof.
      unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
      cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (ipi_scheduled_at_related j tR tL Ht))|].
      exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    Qed.

    Lemma ipi_jobs_must_arrive_rel :
      PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PSR sR)
        (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job dJ jaL PSL sL).
    Proof.
      unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (ipi_scheduled_at_related j tR tL Ht))|].
      exact (ar_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
    Qed.

    Lemma ipi_scheduled_jobs_at_related (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      ArListRel (@prosa.model.schedule.scheduled.scheduled_jobs_at Job PSR arrR sR tR)
        (I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at_inst4 Job dJ PSL arrL sL tL).
    Proof.
      intro Ht. unfold prosa.model.schedule.scheduled.scheduled_jobs_at.
      cbn [I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at_inst4].
      apply ar_filter_related.
      - intro j. exact (ipi_scheduled_at_related j tR tL Ht).
      - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr _ _ Ht).
    Qed.

    Lemma ipi_priority_inversion_related pR pL (Hp : IpiJlfpRel pR pL) (j : Job)
        (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
      SvcBoolRel (@PI.priority_inversion Job PSR arrR sR pR j tR)
        (I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_inst4 Job dJ PSL arrL sL pL j tL).
    Proof.
      unfold PI.priority_inversion.
      cbn [I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_inst4].
      have Hl := ipi_scheduled_jobs_at_related tR tL Ht.
      apply ar_bool_and_related.
      - exact (svc_bool_not_related _ _ (ar_decide_mem_related Job j _ _ Hl)).
      - apply pi_has_related; [|exact Hl].
        intro jlp. exact (svc_bool_not_related _ _ (Hp jlp j)).
    Qed.
  End Sched.

  (** ** Statement correspondences *)

  (** Common prefix: [valid_arrival_sequence -> forall sched, jobs_come_from -> jobs_must_arrive -> _]. *)
  Lemma ipi_prefix_rel (QA : SchedR -> Prop) (QB : SchedL -> SProp) :
    (forall sR sL, IpiScheduleRel sR sL -> PropSPropRel (QA sR) (QB sL)) ->
    PropSPropRel
      (prosa.behavior.arrival_sequence.valid_arrival_sequence arrR ->
        forall sR, prosa.behavior.ready.jobs_come_from_arrival_sequence sR arrR ->
          @prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PSR sR -> QA sR)
      (I.Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job dJ jaL arrL ->
        forall sL, I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job dJ PSL sL arrL ->
          I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job dJ jaL PSL sL -> QB sL).
  Proof.
    intro HQ.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ipi_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (ipi_jobs_come_from_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (ipi_jobs_must_arrive_rel _ _ Hs)|].
    exact (HQ _ _ Hs).
  Qed.

  (** *** idle_implies_no_priority_inversion *)

  Definition src_idle_implies_no_priority_inversion : Prop :=
    ltac:(body_of (fun s : S.statement_idle_implies_no_priority_inversion => s Job jaR arrR)).
  Definition tgt_idle_implies_no_priority_inversion : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_PriorityInversion_idle_implies_no_priority_inversion
      Job dJ jaL arrL)).

  Theorem idle_implies_no_priority_inversion_correspondence :
    PropSPropRel src_idle_implies_no_priority_inversion tgt_idle_implies_no_priority_inversion.
  Proof.
    unfold src_idle_implies_no_priority_inversion, tgt_idle_implies_no_priority_inversion.
    apply ipi_prefix_rel. intros sR sL Hs.
    apply ipi_forall_jlfp. intros pR pL Hp.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (ipi_ideal_is_idle_related _ _ Hs tR tL Ht))|].
    exact (svc_bool_truth_correspondence _ _
      (svc_bool_not_related _ _ (ipi_priority_inversion_related _ _ Hs _ _ Hp j tR tL Ht))).
  Qed.

  (** *** priority_inversion_equiv_sched_lower_priority *)

  Definition src_priority_inversion_equiv_sched_lower_priority : Prop :=
    ltac:(body_of (fun s : S.statement_priority_inversion_equiv_sched_lower_priority => s Job jaR arrR)).
  Definition tgt_priority_inversion_equiv_sched_lower_priority : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Model_Ideal_PriorityInversion_priority_inversion_equiv_sched_lower_priority
        Job dJ jaL arrL)).

  Theorem priority_inversion_equiv_sched_lower_priority_correspondence :
    PropSPropRel src_priority_inversion_equiv_sched_lower_priority
      tgt_priority_inversion_equiv_sched_lower_priority.
  Proof.
    unfold src_priority_inversion_equiv_sched_lower_priority, tgt_priority_inversion_equiv_sched_lower_priority.
    apply ipi_prefix_rel. intros sR sL Hs.
    apply ipi_forall_jlfp. intros pR pL Hp.
    apply ar_imp_correspondence; [exact (ipi_reflexive_rel _ _ Hp)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (ipi_scheduled_at_related _ _ Hs j' tR tL Ht))|].
    exact (ipi_bool_eq_correspondence _ _ _ _ (ipi_priority_inversion_related _ _ Hs _ _ Hp j tR tL Ht)
      (svc_bool_not_related _ _ (Hp j' j))).
  Qed.

  (** *** sched_hep_implies_no_priority_inversion *)

  Definition src_sched_hep_implies_no_priority_inversion : Prop :=
    ltac:(body_of (fun s : S.statement_sched_hep_implies_no_priority_inversion => s Job jaR arrR)).
  Definition tgt_sched_hep_implies_no_priority_inversion : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Model_Ideal_PriorityInversion_sched_hep_implies_no_priority_inversion
        Job dJ jaL arrL)).

  Theorem sched_hep_implies_no_priority_inversion_correspondence :
    PropSPropRel src_sched_hep_implies_no_priority_inversion tgt_sched_hep_implies_no_priority_inversion.
  Proof.
    unfold src_sched_hep_implies_no_priority_inversion, tgt_sched_hep_implies_no_priority_inversion.
    apply ipi_prefix_rel. intros sR sL Hs.
    apply ipi_forall_jlfp. intros pR pL Hp.
    apply ar_imp_correspondence; [exact (ipi_reflexive_rel _ _ Hp)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (ipi_scheduled_at_related _ _ Hs j' tR tL Ht))|].
    apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (Hp j' j))|].
    exact (ipi_bool_eq_correspondence _ _ _ _ (ipi_priority_inversion_related _ _ Hs _ _ Hp j tR tL Ht)
      (@Lean.eq_refl _ _)).
  Qed.

  (** *** sched_lp_implies_priority_inversion *)

  Definition src_sched_lp_implies_priority_inversion : Prop :=
    ltac:(body_of (fun s : S.statement_sched_lp_implies_priority_inversion => s Job jaR arrR)).
  Definition tgt_sched_lp_implies_priority_inversion : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Model_Ideal_PriorityInversion_sched_lp_implies_priority_inversion
        Job dJ jaL arrL)).

  Theorem sched_lp_implies_priority_inversion_correspondence :
    PropSPropRel src_sched_lp_implies_priority_inversion tgt_sched_lp_implies_priority_inversion.
  Proof.
    unfold src_sched_lp_implies_priority_inversion, tgt_sched_lp_implies_priority_inversion.
    apply ipi_prefix_rel. intros sR sL Hs.
    apply ipi_forall_jlfp. intros pR pL Hp.
    apply ar_imp_correspondence; [exact (ipi_reflexive_rel _ _ Hp)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (ipi_scheduled_at_related _ _ Hs j' tR tL Ht))|].
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hp j' j)))|].
    exact (svc_bool_truth_correspondence _ _ (ipi_priority_inversion_related _ _ Hs _ _ Hp j tR tL Ht)).
  Qed.
End Ideal.
