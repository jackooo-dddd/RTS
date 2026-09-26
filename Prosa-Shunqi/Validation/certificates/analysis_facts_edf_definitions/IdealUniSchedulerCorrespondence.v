From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import IdealUniSchedulerSemanticSource.
From prosa Require Import model.processor.ideal model.schedule.work_conserving implementation.definitions.generic_scheduler util.supremum.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedEdfDefinitions ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence.

Module I := ImportedEdfDefinitions.
Module S := IdealUniSchedulerSemanticSource.IdealUniSchedulerSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.

(** Definition certificates for [implementation/definitions/ideal_uni_scheduler.v].

    Source side: the extracted byte-identical definition blocks (over the
    pinned ideal processor, generic scheduler, work-conserving backlog,
    priority classes and supremum, the accepted extracted preemption-parameter
    and readiness sources); target side: the compiled Lean definitions.  The
    processor model is fixed to the ideal uniprocessor on both sides: states
    are related by the constructor-preserving Option map ([IdOptRel]),
    schedules pointwise ([IdScheduleRel]); [job_cost] by [SvcJobCostRel],
    [job_arrival] by [ArJobArrivalRel], arrival sequences by
    [ArArrivalSequenceRel]; the readiness model is related by its
    [job_ready] on related schedules and instants, the preemption model
    pointwise, the JLDP policy pointwise on Booleans, [choose_job] on related
    instants and job lists; jobs are identity carriers.  The ideal-state
    observations are the accepted ideal-schedule closed forms, re-proved over
    kernel-checked Lean unit-core equations exported with the artifact;
    [service] is closed by the accepted interval-sum certificate, the backlog
    by the accepted filter and arrival-prefix certificates; the structurally
    recursive [schedule_up_to] and the [replace_at] it uses are related by
    induction and case analysis closed by kernel-checked Lean equations at the
    ideal processor.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.

Lemma id_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma id_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.


Lemma iu_src_transport {A : Type} (P : A -> SProp) (x y : A) :
  Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

Lemma iu_eq_identity_correspondence (T : Type) (x y : T) :
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
  Let StL := I.Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job dJ PSL.
  Let SchedR := @prosa.behavior.schedule.schedule Job PSR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.

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

  (** *** Target-side closed forms through the interface equations *)

  Lemma id_scheduled_in_related (j : Job) (sR : option Job) sL :
    IdOptRel sR sL ->
    SvcBoolRel (@prosa.behavior.schedule.scheduled_in Job PSR j sR)
      (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst4 Job dJ PSL j sL).
  Proof.
    intro Hs. destruct Hs. rewrite id_src_scheduled_in.
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_IdealUniSchedulerInterface_production_ideal_scheduled_in Job dJ j _))).
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
      (I.Prosa_Validation_IdealUniSchedulerInterface_production_ideal_service_in Job dJ j sL))).
    have H := id_service_on_related j sR sL tt I.Unit_unit Hs.
    rewrite id_src_service_in. change (nat_of_bool (sR == Some j)) with
      (@prosa.behavior.schedule.service_on Job PSR j sR tt).
    exact H.
  Qed.


  Definition IdScheduleRel (schedR : SchedR) (schedL : SchedL) : SProp :=
    forall tR tL, SubNatRel tR tL -> IdOptRel (schedR tR) (schedL tL).

  Let ONE := sub_nat_rel_canonical (S O).

  (** *** Schedule observations *)

  Section Sched.
    Variable schedR : SchedR.
    Variable schedL : SchedL.
    Hypothesis Hsched : IdScheduleRel schedR schedL.

    Lemma iu_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PSR schedR j tR)
        (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.scheduled_at.
      cbn [I.Prosa_Behavior_Service_scheduled_at_inst4].
      exact (id_scheduled_in_related j _ _ (Hsched tR tL Ht)).
    Qed.

    Lemma iu_service_at_fun (j : Job) :
      SvcNatFunRel (fun t => @prosa.behavior.service.service_at Job PSR schedR j t)
        (fun t => I.Prosa_Validation_ServiceInterface_serviceAtProjection_inst4 Job dJ PSL schedL j t).
    Proof.
      intros tR tL Ht. unfold prosa.behavior.service.service_at.
      exact (id_service_in_related j _ _ (Hsched tR tL Ht)).
    Qed.

    Lemma iu_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service Job PSR schedR j tR)
        (I.Prosa_Behavior_Service_service_inst4 Job dJ PSL schedL j tL).
    Proof.
      intro Ht.
      exact (svc_interval_sum_related O tR _ tL _ _ (sub_nat_rel_canonical O) Ht (iu_service_at_fun j)).
    Qed.
  End Sched.

  Variable jcR : prosa.behavior.job.JobCost Job.
  Variable jcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hjc : SvcJobCostRel Job jcR jcL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable rmR : @prosa.behavior.ready.JobReady Job PSR jcR jaR.
  Variable rmL : I.Prosa_Behavior_Ready_JobReady_inst4 Job dJ PSL jcL jaL.
  Hypothesis Hrm : forall sR sL, IdScheduleRel sR sL -> forall (j : Job) tR tL, SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.ready.job_ready Job PSR jcR jaR rmR sR j tR)
      (I.Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job dJ PSL jcL jaL rmL sL j tL).
  Variable jpR : PP.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : forall (j : Job) nR nL, SubNatRel nR nL ->
    SvcBoolRel (@PP.job_preemptable Job jpR j nR)
      (I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job dJ jpL j nL).

  (** *** prev_job_nonpreemptive *)

  Lemma iu_prev_inner (o : option Job) (bR : Job -> bool) (bL : Job -> I.Bool) :
    (forall j, SvcBoolRel (bR j) (bL j)) ->
    SvcBoolRel (if o is Some j then bR j else false)
      (I.Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive_match_1 Job dJ
        (fun _ : StL => I.Bool) (id_opt_to_imported o) bL (fun _ : I.Unit => I.Bool_false)).
  Proof.
    intro Hb. destruct o as [j|].
    - exact (Hb j).
    - exact (@Lean.eq_refl _ _).
  Qed.

  Theorem prev_job_nonpreemptive_correspondence (sR : SchedR) (sL : SchedL) (tR : nat) (tL : Lean.Nat) :
    IdScheduleRel sR sL -> SubNatRel tR tL ->
    SvcBoolRel (@S.prev_job_nonpreemptive Job jcR jaR rmR jpR sR tR)
      (I.Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive Job dJ jcL jaL rmL jpL sL tL).
  Proof.
    intros Hs Ht.
    refine (id_lean_transport (fun y => SvcBoolRel (@S.prev_job_nonpreemptive Job jcR jaR rmR jpR sR tR)
      (I.Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive Job dJ jcL jaL rmL jpL sL y))
      _ _ Ht _).
    destruct tR as [|t].
    - exact (@Lean.eq_refl _ _).
    - have Ht1 := sub_nat_rel_canonical t.+1.
      refine (id_lean_transport (fun y => SvcBoolRel
        (if sR t is Some j then
           @prosa.behavior.ready.job_ready Job PSR jcR jaR rmR sR j t.+1
           && ~~ @PP.job_preemptable Job jpR j (@prosa.behavior.service.service Job PSR sR j t.+1)
         else false)
        (I.Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive_match_1 Job dJ
          (fun _ : StL => I.Bool) y
          (fun j : Job => I.Bool_and
            (I.Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job dJ PSL jcL jaL rmL sL j (sub_nat_to_imported t.+1))
            (I.Bool_not (I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job dJ jpL j
              (I.Prosa_Behavior_Service_service_inst4 Job dJ PSL sL j (sub_nat_to_imported t.+1)))))
          (fun _ : I.Unit => I.Bool_false))) _ _ (Hs _ _ (sub_nat_rel_canonical t)) _).
      apply iu_prev_inner. intro j.
      exact (ar_bool_and_related _ _ _ _ (Hrm _ _ Hs j _ _ Ht1)
        (svc_bool_not_related _ _ (Hjp j _ _ (iu_service_related _ _ Hs j _ _ Ht1)))).
  Qed.

  (** *** allocation_at *)

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma iu_backlogged_related (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel sR sL) (tR : nat) (tL : Lean.Nat)
      (Ht : SubNatRel tR tL) :
    ArPredRel (fun j => @prosa.behavior.ready.backlogged Job PSR jcR jaR rmR sR j tR)
      (fun j => I.Prosa_Behavior_Ready_backlogged_inst4 Job dJ PSL jcL jaL rmL sL j tL).
  Proof.
    intro j. unfold prosa.behavior.ready.backlogged.
    exact (ar_bool_and_related _ _ _ _ (Hrm _ _ Hs j _ _ Ht)
      (svc_bool_not_related _ _ (iu_scheduled_at_related _ _ Hs j _ _ Ht))).
  Qed.

  Lemma iu_jobs_backlogged_at_related (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel sR sL)
      (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
    ArListRel (@prosa.model.schedule.work_conserving.jobs_backlogged_at Job jaR jcR PSR rmR arrR sR tR)
      (I.Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at_inst4 Job dJ jaL jcL PSL rmL arrL sL tL).
  Proof.
    exact (ar_filter_related Job _ _ _ _ (iu_backlogged_related _ _ Hs _ _ Ht)
      (arrivals_up_to_correspondence_certificate Job arrR arrL Harr _ _ Ht)).
  Qed.

  Lemma iu_cond_related (b : bool) (xR yR : option Job) (xL yL : I.Option Job) :
    IdOptRel xR xL -> IdOptRel yR yL ->
    IdOptRel (if b then xR else yR) (I.cond (I.Option Job) (svc_bool_to_imported b) xL yL).
  Proof. intros Hx Hy. destruct b; [exact Hx | exact Hy]. Qed.

  Variable cjR : nat -> seq Job -> option Job.
  Variable cjL : I.Prosa_Behavior_Time_instant -> I.List Job -> I.Option Job.
  Hypothesis Hcj : forall tR tL, SubNatRel tR tL -> forall xsR xsL, ArListRel xsR xsL ->
    IdOptRel (cjR tR xsR) (cjL tL xsL).

  Theorem allocation_at_correspondence (sR : SchedR) (sL : SchedL) (tR : nat) (tL : Lean.Nat) :
    IdScheduleRel sR sL -> SubNatRel tR tL ->
    IdOptRel (@S.allocation_at Job jcR jaR arrR rmR jpR cjR sR tR)
      (I.Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at Job dJ jcL jaL arrL rmL jpL cjL sL tL).
  Proof.
    intros Hs Ht.
    have Hprev := prev_job_nonpreemptive_correspondence _ _ _ _ Hs Ht.
    have Hpred : SubNatRel tR.-1 (I.HSub_hSub_inst7 I.Prosa_Behavior_Time_instant I.Prosa_Behavior_Time_instant
        I.Prosa_Behavior_Time_instant (I.instHSub_inst1 I.Prosa_Behavior_Time_instant I.instSubNat) tL
        (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Time_instant 1 (I.instOfNatNat 1))) :=
      iu_src_transport (fun x => SubNatRel x _) _ _ (subn1 tR)
        (svc_target_sub_related _ _ _ _ Ht ONE).
    unfold S.allocation_at.
    cbn [I.Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at].
    refine (id_lean_transport (fun y => IdOptRel
      (if @S.prev_job_nonpreemptive Job jcR jaR rmR jpR sR tR then sR tR.-1
       else cjR tR (@prosa.model.schedule.work_conserving.jobs_backlogged_at Job jaR jcR PSR rmR arrR sR tR))
      (I.cond (I.Option Job) y (sL _) (cjL tL
        (I.Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at_inst4 Job dJ jaL jcL PSL rmL arrL sL tL))))
      _ _ Hprev _).
    exact (iu_cond_related _ _ _ _ _ (Hs _ _ Hpred) (Hcj _ _ Ht _ _ (iu_jobs_backlogged_at_related _ _ Hs _ _ Ht))).
  Qed.

  (** *** The generic scheduler at the ideal processor *)

  Section Generic.
    Variable polR : SchedR -> nat -> option Job.
    Variable polL : I.Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy_inst2 Job dJ PSL.
    Hypothesis Hpol : forall sR sL, IdScheduleRel sR sL -> forall tR tL, SubNatRel tR tL ->
      IdOptRel (polR sR tR) (polL sL tL).

    Let emptyR := @prosa.implementation.definitions.generic_scheduler.empty_schedule Job PSR None.
    Let emptyL := I.Prosa_Implementation_Definitions_GenericScheduler_empty_schedule_inst2 Job dJ PSL
      (I.Option_none Job).
    Let sutR h := @prosa.implementation.definitions.generic_scheduler.schedule_up_to Job PSR polR None h.
    Let sutL h := I.Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to_inst2 Job dJ PSL polL
      (I.Option_none Job) h.

    Lemma iu_empty_related : IdScheduleRel emptyR emptyL.
    Proof.
      intros tR tL Ht.
      exact (sub_imported_eq_sym _ _
        (I.Prosa_Validation_IdealUniSchedulerInterface_production_empty_schedule Job dJ (I.Option_none Job) tL)).
    Qed.

    Lemma iu_nat_not_eq (tR t'R : nat) (tL t'L : Lean.Nat) :
      SubNatRel tR tL -> SubNatRel t'R t'L -> t'R <> tR -> I.Not (Lean.eq tL t'L).
    Proof.
      intros Ht Ht' NE. unfold I.Not. intro EL.
      refine (match NE _ return I.False with end).
      rewrite -(id_nat_input _ _ Ht) -(id_nat_input _ _ Ht').
      exact (Logic.eq_sym (f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ EL))).
    Qed.

    Lemma iu_replace_at_related (sR : SchedR) (sL : SchedL) (t'R : nat) (t'L : Lean.Nat)
        (nsR : option Job) (nsL : StL) :
      IdScheduleRel sR sL -> SubNatRel t'R t'L -> IdOptRel nsR nsL ->
      IdScheduleRel (@prosa.analysis.transform.swap.replace_at Job PSR sR t'R nsR)
        (I.Prosa_Analysis_Transform_Swap_replace_at_inst4 Job dJ PSL sL t'L nsL).
    Proof.
      intros Hs Ht' Hns tR tL Ht.
      destruct (@eqP nat t'R tR) as [E|NE].
      - refine (iu_src_transport (fun o => IdOptRel o _) nsR _ _ _).
        + subst tR. rewrite /prosa.analysis.transform.swap.replace_at eqxx; reflexivity.
        + subst tR.
          exact (sub_imported_eq_trans _ _ _ Hns (sub_imported_eq_sym _ _
            (I.Prosa_Validation_IdealUniSchedulerInterface_production_replace_at_same Job dJ sL t'L nsL tL
              (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Ht) Ht')))).
      - refine (iu_src_transport (fun o => IdOptRel o _) (sR tR) _ _ _).
        + move/eqP: NE => NE. rewrite /prosa.analysis.transform.swap.replace_at (negbTE NE); reflexivity.
        + exact (sub_imported_eq_trans _ _ _ (Hs tR tL Ht) (sub_imported_eq_sym _ _
            (I.Prosa_Validation_IdealUniSchedulerInterface_production_replace_at_other Job dJ sL t'L nsL tL
              (iu_nat_not_eq _ _ _ _ Ht Ht' NE)))).
    Qed.

    Lemma iu_succ_related (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel tR.+1 (I.HAdd_hAdd_inst7 Lean.Nat I.Prosa_Behavior_Time_instant Lean.Nat
        (I.instHAdd_inst1 Lean.Nat I.instAddNat) tL
        (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Time_instant 1 (I.instOfNatNat 1))).
    Proof.
      intro Ht.
      exact (iu_src_transport (fun x => SubNatRel x _) _ _ (addn1 tR)
        (sub_add_correspondence _ _ _ _ Ht (@Lean.eq_refl _ _))).
    Qed.

    Lemma iu_sut_canonical (hR : nat) : IdScheduleRel (sutR hR) (sutL (sub_nat_to_imported hR)).
    Proof.
      induction hR as [|h IH].
      - have H0 := sub_nat_rel_canonical O.
        exact (id_lean_transport (fun y => IdScheduleRel (sutR O) y) _ _
          (sub_imported_eq_sym _ _
            (I.Prosa_Validation_IdealUniSchedulerInterface_production_schedule_up_to_zero Job dJ polL (I.Option_none Job)))
          (iu_replace_at_related _ _ _ _ _ _ iu_empty_related H0 (Hpol _ _ iu_empty_related _ _ H0))).
      - have Hh := sub_nat_rel_canonical h.
        have Hh1 := iu_succ_related _ _ Hh.
        refine (id_lean_transport (fun y => IdScheduleRel (sutR h.+1) (sutL y)) _ _
          (sub_imported_eq_sym _ _ Hh1) _).
        exact (id_lean_transport (fun y => IdScheduleRel (sutR h.+1) y) _ _
          (sub_imported_eq_sym _ _
            (I.Prosa_Validation_IdealUniSchedulerInterface_production_schedule_up_to_succ Job dJ polL (I.Option_none Job)
              (sub_nat_to_imported h)))
          (iu_replace_at_related _ _ _ _ _ _ IH Hh1 (Hpol _ _ IH _ _ Hh1))).
    Qed.

    Lemma iu_generic_schedule_related :
      IdScheduleRel (@prosa.implementation.definitions.generic_scheduler.generic_schedule Job PSR polR None)
        (I.Prosa_Implementation_Definitions_GenericScheduler_generic_schedule_inst2 Job dJ PSL polL (I.Option_none Job)).
    Proof.
      intros tR tL Ht.
      have H := id_lean_transport (fun y => IdScheduleRel (sutR tR) (sutL y)) _ _ Ht (iu_sut_canonical tR).
      exact (H tR tL Ht).
    Qed.
  End Generic.

  Theorem pmc_uni_schedule_correspondence :
    IdScheduleRel (@S.pmc_uni_schedule Job jcR jaR arrR rmR jpR cjR)
      (I.Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule Job dJ jcL jaL arrL rmL jpL cjL).
  Proof.
    exact (iu_generic_schedule_related _ _
      (fun sR sL Hs tR tL Ht => allocation_at_correspondence sR sL tR tL Hs Ht)).
  Qed.
End Ideal.

(** ** Supremum and the priority-aware scheduler *)

Section Supremum.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable hpR : prosa.model.priority.definitions.JLDP_policy Job.
  Variable hpL : I.Prosa_Model_Priority_Definitions_JLDP_policy Job dJ.
  Hypothesis Hhp : forall (tR : nat) (tL : Lean.Nat), SubNatRel tR tL -> forall x y : Job,
    SvcBoolRel (@prosa.model.priority.definitions.hep_job_at Job hpR tR x y)
      (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job dJ hpL tL x y).

  Lemma iu_choose_superior_related (R : Job -> Job -> bool) (RL : Job -> Job -> I.Bool)
      (HR : forall x y, SvcBoolRel (R x y) (RL x y)) (x : Job) (oR : option Job) (oL : I.Option Job) :
    IdOptRel oR oL ->
    IdOptRel (@prosa.util.supremum.choose_superior Job R x oR) (I.Prosa_Util_Supremum_choose_superior Job RL x oL).
  Proof.
    intro Ho.
    refine (id_lean_transport (fun y => IdOptRel (@prosa.util.supremum.choose_superior Job R x oR)
      (I.Prosa_Util_Supremum_choose_superior Job RL x y)) _ _ Ho _).
    destruct oR as [y|].
    - unfold prosa.util.supremum.choose_superior.
      refine (id_lean_transport (fun b => IdOptRel (if R x y then Some x else Some y)
        (I.ite (I.Option Job) (Lean.eq b I.Bool_true) (I.instDecidableEqBool b I.Bool_true)
          (I.Option_some Job x) (I.Option_some Job y))) _ _ (HR x y) _).
      destruct (R x y); exact (@Lean.eq_refl _ _).
    - exact (@Lean.eq_refl _ _).
  Qed.

  Lemma iu_supremum_canonical (R : Job -> Job -> bool) (RL : Job -> Job -> I.Bool)
      (HR : forall x y, SvcBoolRel (R x y) (RL x y)) (xs : seq Job) :
    IdOptRel (@prosa.util.supremum.supremum Job R xs) (I.Prosa_Util_Supremum_supremum Job RL (ar_list_to_imported xs)).
  Proof.
    induction xs as [|x xs IH].
    - exact (@Lean.eq_refl _ _).
    - exact (iu_choose_superior_related R RL HR x _ _ IH).
  Qed.

  Theorem choose_highest_prio_job_correspondence (tR : nat) (tL : Lean.Nat) (xsR : seq Job) (xsL : I.List Job) :
    SubNatRel tR tL -> ArListRel xsR xsL ->
    IdOptRel (@S.choose_highest_prio_job Job hpR tR xsR)
      (I.Prosa_Implementation_Definitions_IdealUniScheduler_choose_highest_prio_job Job dJ hpL tL xsL).
  Proof.
    intros Ht Hxs.
    unfold S.choose_highest_prio_job.
    cbn [I.Prosa_Implementation_Definitions_IdealUniScheduler_choose_highest_prio_job].
    exact (id_lean_transport (fun y => IdOptRel _ (I.Prosa_Util_Supremum_supremum Job _ y)) _ _ Hxs
      (iu_supremum_canonical _ _ (Hhp tR tL Ht) xsR)).
  Qed.
End Supremum.

Section Uni.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.
  Variable jcR : prosa.behavior.job.JobCost Job.
  Variable jcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hjc : SvcJobCostRel Job jcR jcL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable rmR : @prosa.behavior.ready.JobReady Job PSR jcR jaR.
  Variable rmL : I.Prosa_Behavior_Ready_JobReady_inst4 Job dJ PSL jcL jaL.
  Hypothesis Hrm : forall sR sL, IdScheduleRel Job sR sL -> forall (j : Job) tR tL, SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.ready.job_ready Job PSR jcR jaR rmR sR j tR)
      (I.Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job dJ PSL jcL jaL rmL sL j tL).
  Variable jpR : PP.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : forall (j : Job) nR nL, SubNatRel nR nL ->
    SvcBoolRel (@PP.job_preemptable Job jpR j nR)
      (I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job dJ jpL j nL).
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable hpR : prosa.model.priority.definitions.JLDP_policy Job.
  Variable hpL : I.Prosa_Model_Priority_Definitions_JLDP_policy Job dJ.
  Hypothesis Hhp : forall (tR : nat) (tL : Lean.Nat), SubNatRel tR tL -> forall x y : Job,
    SvcBoolRel (@prosa.model.priority.definitions.hep_job_at Job hpR tR x y)
      (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job dJ hpL tL x y).

  Theorem uni_schedule_correspondence :
    IdScheduleRel Job (@S.uni_schedule Job jcR jaR arrR rmR jpR hpR)
      (I.Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule Job dJ jcL jaL arrL rmL jpL hpL).
  Proof.
    unfold S.uni_schedule.
    cbn [I.Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule].
    exact (pmc_uni_schedule_correspondence Job jcR jcL jaR jaL rmR rmL Hrm jpR jpL Hjp arrR arrL Harr _ _
      (fun tR tL Ht xsR xsL Hxs => choose_highest_prio_job_correspondence Job hpR hpL Hhp tR tL xsR xsL Ht Hxs)).
  Qed.
End Uni.
