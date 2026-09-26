From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import IdealServiceOfJobsSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdealServiceOfJobs ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedIdealServiceOfJobs.
Module S := IdealServiceOfJobsSemanticSource.IdealServiceOfJobsSemanticSource.

(** Statement correspondences for [analysis/facts/model/ideal/service_of_jobs.v].

    Source side: the extracted statement [S.statement_X] specialised at its
    leading inputs (job type, job arrivals, processor state or arrival
    sequence, as they occur); target side: the type of the imported Lean
    theorem at related inputs.  The processor state is related by the
    two-sided [SvcProcessorStateRel]; the fully-consuming statement also
    relates the [supply_on] field ([IsjSupplyRel], exactly as the accepted
    facts/behavior/service certificate extends the relation).  Arrival
    sequences, schedules (functionally through the state conversion, with its
    roundtrips), processor states, jobs and instants bound later are covered
    in both directions.  Service, service of jobs, supply, blackout and
    scheduled-job operations are the accepted proofs replayed at this
    artifact (supply/blackout through the kernel-guarded supply projections,
    idleness through the scheduled-job interface equations).  No source or
    target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators *)

Lemma isj_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Lemma isj_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma isj_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma isj_eq_identity_correspondence (T : Type) (x y : T) :
  PropSPropRel (x = y) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - exact (coq_eq_to_imported_eq x y).
  - intro H. apply strictly_inhabits. exact (imported_eq_to_coq_eq x y H).
Qed.

Lemma isj_bool_to_nat_related (bR : bool) (bL : I.Bool) :
  SvcBoolRel bR bL -> SubNatRel (nat_of_bool bR) (I.Bool_toNat bL).
Proof.
  intro Hb. unfold SvcBoolRel in Hb. destruct Hb.
  destruct bR; cbn; [exact (sub_nat_rel_canonical 1) | exact (sub_nat_rel_canonical O)].
Qed.

(** Replayed from the accepted service-of-jobs certificate. *)
Lemma isj_sum_filter_related (T : Type) (PR : T -> bool) (PL : T -> I.Bool)
    (FR : T -> nat) (FL : T -> Lean.Nat) xsR xsL :
  ArPredRel PR PL -> (forall x, SubNatRel (FR x) (FL x)) -> ArListRel xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (ari_list_sum T FL (ar_target_filter PL xsL)).
Proof.
  intros HP HF Hxs. rewrite -big_filter.
  exact (ari_sum_related T FR FL _ _ HF (ar_filter_related T PR PL xsR xsL HP Hxs)).
Qed.

Section Generic.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let StateR := @prosa.behavior.schedule.State Job PStateR.
  Let StateL := I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PStateL.

  Let cover_state :=
    isj_forall_cover_sprop _ _ (svc_ps_state_rel Job PStateR PStateL R)
      (svc_ps_state_to_target Job PStateR PStateL R) (svc_ps_state_to_source Job PStateR PStateL R)
      (svc_ps_state_rel_canonical Job PStateR PStateL R) (svc_ps_state_rel_surjective Job PStateR PStateL R).

  (** *** Schedules, functionally through the state conversion *)

  Definition IsjScheduleFunRel (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      Lean.eq (svc_ps_state_to_target Job PStateR PStateL R (schedR tR)) (schedL tL).

  Lemma isj_schedule_fun_to_svc schedR schedL :
    IsjScheduleFunRel schedR schedL -> SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Proof.
    intros Hf tR tL Ht.
    exact (isj_lean_transport (fun sL => svc_ps_state_rel Job PStateR PStateL R (schedR tR) sL)
      _ _ (Hf tR tL Ht) (svc_ps_state_rel_canonical Job PStateR PStateL R (schedR tR))).
  Qed.

  Definition isj_schedule_to_target (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
      I.Prosa_Behavior_Schedule_schedule Job dJ PStateL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq tL)).

  Definition isj_schedule_to_source (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) :
      @prosa.behavior.schedule.schedule Job PStateR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)).

  Lemma isj_schedule_to_target_rel schedR : IsjScheduleFunRel schedR (isj_schedule_to_target schedR).
  Proof.
    intros tR tL Ht. unfold isj_schedule_to_target.
    rewrite (isj_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma isj_schedule_to_source_rel schedL : IsjScheduleFunRel (isj_schedule_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. unfold isj_schedule_to_source.
    exact (sub_imported_eq_trans _ _ _
      (svc_ps_state_target_roundtrip Job PStateR PStateL R _)
      (sub_imported_eq_congr schedL _ _ Ht)).
  Qed.

  Let cover_schedule :=
    isj_forall_cover_sprop _ _ IsjScheduleFunRel isj_schedule_to_target isj_schedule_to_source
      isj_schedule_to_target_rel isj_schedule_to_source_rel.

  (** *** Schedule-level operations *)

  Section Sched.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Lemma isj_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.scheduled_at.
      cbn [I.Prosa_Behavior_Service_scheduled_at].
      exact (svc_scheduled_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
    Qed.

    Lemma isj_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.service_at.
      cbn [I.Prosa_Behavior_Service_service_at].
      exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
    Qed.

    Lemma isj_service_during_related (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
        (I.Prosa_Behavior_Service_service_during Job dJ PStateL schedL j t1L t2L).
    Proof.
      intros Ht1 Ht2.
      have Hsum := svc_interval_sum_related t1R t2R t1L t2L
        (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
        (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j t)
        Ht1 Ht2 (fun tR tL Ht => isj_service_at_related j tR tL Ht).
      change (SubNatRel
        (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
        (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
          Job dJ PStateL schedL j t1L t2L)) in Hsum.
      exact Hsum.
    Qed.

    Lemma isj_service_of_jobs_predT_related (jobsR : seq Job) (jobsL : I.List Job)
        (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      ArListRel jobsR jobsL -> SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel
        (@prosa.model.aggregate.service_of_jobs.service_of_jobs Job PStateR schedR predT jobsR t1R t2R)
        (I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job dJ PStateL schedL
          (fun _ => I.Bool_true) jobsL t1L t2L).
    Proof.
      intros Hjobs Ht1 Ht2.
      unfold prosa.model.aggregate.service_of_jobs.service_of_jobs.
      cbn [I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs].
      refine (isj_sum_filter_related Job predT (fun _ => I.Bool_true) _ _ jobsR jobsL _
        (fun j => isj_service_during_related j t1R t2R t1L t2L Ht1 Ht2) Hjobs).
      intro x. exact (@Lean.eq_refl _ _).
    Qed.

    Section Arrivals.
      Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
      Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
      Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

      Lemma isj_scheduled_jobs_at_related (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        ArListRel (@prosa.model.schedule.scheduled.scheduled_jobs_at Job PStateR arrR schedR tR)
          (I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job dJ PStateL arrL schedL tL).
      Proof.
        intro Ht. unfold prosa.model.schedule.scheduled.scheduled_jobs_at.
        cbn [I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at].
        apply ar_filter_related.
        - intro j. exact (isj_scheduled_at_related j tR tL Ht).
        - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr tR tL Ht).
      Qed.

      Lemma isj_is_idle_related (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        SvcBoolRel (@prosa.model.schedule.scheduled.is_idle Job PStateR arrR schedR tR)
          (I.Prosa_Model_Schedule_Scheduled_is_idle Job dJ PStateL arrL schedL tL).
      Proof.
        intro Ht. unfold prosa.model.schedule.scheduled.is_idle.
        cbn [I.Prosa_Model_Schedule_Scheduled_is_idle].
        have Hxs := isj_scheduled_jobs_at_related tR tL Ht.
        unfold SvcBoolRel, ArListRel in *.
        refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_congr (I.List_isEmpty Job) _ _ Hxs)).
        destruct (@prosa.model.schedule.scheduled.scheduled_jobs_at Job PStateR arrR schedR tR) as [|x xs].
        - exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ScheduledInterface_production_isEmpty_nil Job)).
        - exact (sub_imported_eq_sym _ _
            (I.Prosa_Validation_ScheduledInterface_production_isEmpty_cons Job x (ar_list_to_imported xs))).
      Qed.

      Section Arrival.
        Variable jaR : prosa.behavior.job.JobArrival Job.
        Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
        Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

        Lemma isj_jobs_come_from_related :
          PropSPropRel (@prosa.behavior.ready.jobs_come_from_arrival_sequence Job PStateR schedR arrR)
            (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job dJ PStateL schedL arrL).
        Proof.
          unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
          cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence].
          apply ar_forall_identity_correspondence. intro j.
          apply ar_forall_nat_correspondence. intros tR tL Ht.
          apply ar_imp_correspondence;
            [exact (svc_bool_truth_correspondence _ _ (isj_scheduled_at_related j _ _ Ht))|].
          exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
        Qed.

        Lemma isj_jobs_must_arrive_related :
          PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PStateR schedR)
            (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job dJ jaL PStateL schedL).
        Proof.
          unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
          cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute].
          apply ar_forall_identity_correspondence. intro j.
          apply ar_forall_nat_correspondence. intros tR tL Ht.
          apply ar_imp_correspondence;
            [exact (svc_bool_truth_correspondence _ _ (isj_scheduled_at_related j _ _ Ht))|].
          exact (ar_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
        Qed.
      End Arrival.

      (** The conclusion: [exists t, t1 <= t < t2 /\ is_idle arr_seq sched t]. *)
      Lemma isj_idle_exists_related (t1R t2R : nat) (t1L t2L : Lean.Nat) :
        SubNatRel t1R t1L -> SubNatRel t2R t2L ->
        PropSPropRel
          (exists t : nat, (t1R <= t < t2R) /\
             @prosa.model.schedule.scheduled.is_idle Job PStateR arrR schedR t)
          (I.Exists Lean.Nat (fun t =>
             And (Lean.eq (I.Bool_and
                    (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat t1L t) (I.Nat_decLe t1L t))
                    (I.Decidable_decide (I.LT_lt_inst1 Lean.Nat I.instLTNat t t2L) (I.Nat_decLt t t2L)))
                  I.Bool_true)
                 (Lean.eq (I.Prosa_Model_Schedule_Scheduled_is_idle Job dJ PStateL arrL schedL t)
                  I.Bool_true))).
      Proof.
        intros Ht1 Ht2.
        apply ar_exists_nat_correspondence. intros tR tL Ht.
        apply ar_and_correspondence.
        - exact (svc_bool_truth_correspondence _ _ (svc_bool_and_related _ _ _ _
            (svc_decide_le_related _ _ _ _ Ht1 Ht) (svc_decide_lt_related _ _ _ _ Ht Ht2))).
        - exact (svc_bool_truth_correspondence _ _ (isj_is_idle_related tR tL Ht)).
      Qed.
    End Arrivals.
  End Sched.

  (** *** Platform properties *)

  Lemma isj_uniprocessor_related :
    PropSPropRel (@prosa.model.processor.platform_properties.uniprocessor_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.uniprocessor_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply cover_schedule. intros sR sL Hs.
    have Hsv := isj_schedule_fun_to_svc sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (isj_scheduled_at_related sR sL Hsv j1 _ _ Ht))|].
    apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (isj_scheduled_at_related sR sL Hsv j2 _ _ Ht))|].
    exact (isj_eq_identity_correspondence Job j1 j2).
  Qed.

  Lemma isj_ideal_progress_related :
    PropSPropRel (@prosa.model.processor.platform_properties.ideal_progress_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.ideal_progress_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model].
    apply ar_forall_identity_correspondence. intro j.
    apply cover_state. intros sR sL Hs.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (svc_scheduled_in_related Job PStateR PStateL R j sR sL Hs))|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O)
      (svc_service_in_related Job PStateR PStateL R j sR sL Hs)).
  Qed.

  (** *** Supply (the [supply_on] field of the processor-state relation) *)

  Definition IsjSupplyRel : SProp :=
    forall (sR : StateR) (sL : StateL) (cR : @prosa.behavior.schedule.Core Job PStateR),
      svc_ps_state_rel Job PStateR PStateL R sR sL ->
      SubNatRel (@prosa.behavior.schedule.supply_on Job PStateR sR cR)
        (I.Prosa_Behavior_Schedule_ProcessorState_supply_on Job dJ PStateL sL
          (svc_ps_core_to_target Job PStateR PStateL R cR)).

  Section Supply.
    Hypothesis Hsupply : IsjSupplyRel.

    Lemma isj_supply_in_related (sR : StateR) (sL : StateL) :
      svc_ps_state_rel Job PStateR PStateL R sR sL ->
      SubNatRel (@prosa.behavior.schedule.supply_in Job PStateR sR)
        (I.Prosa_Behavior_Schedule_ProcessorState_supply_in Job dJ PStateL sL).
    Proof.
      intro Hstate.
      have Hsum := svc_finite_sum_related _ _
        (svc_ps_core_to_target Job PStateR PStateL R)
        (fun cR => @prosa.behavior.schedule.supply_on Job PStateR sR cR)
        (fun cL => I.Prosa_Behavior_Schedule_ProcessorState_supply_on Job dJ PStateL sL cL)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ PStateL)
        (fun cR => Hsupply sR sL cR Hstate)
        (svc_ps_core_enumeration_rel Job PStateR PStateL R).
      unfold SubNatRel in Hsum |- *.
      exact (sub_imported_eq_trans _ _ _ Hsum
        (sub_imported_eq_sym _ _
          (I.Prosa_Validation_ScheduleInterface_production_supply_in_as_list_sum Job dJ PStateL sL))).
    Qed.

    Section SupplySched.
      Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
      Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
      Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

      Lemma isj_supply_at_related (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        SubNatRel (@prosa.model.processor.supply.supply_at Job PStateR schedR tR)
          (I.Prosa_Model_Processor_Supply_supply_at Job dJ PStateL schedL tL).
      Proof.
        intro Ht. unfold prosa.model.processor.supply.supply_at.
        cbn [I.Prosa_Model_Processor_Supply_supply_at].
        exact (isj_supply_in_related _ _ (Hsched tR tL Ht)).
      Qed.

      Lemma isj_is_blackout_related (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        SvcBoolRel (@prosa.model.processor.supply.is_blackout Job PStateR schedR tR)
          (I.Prosa_Model_Processor_Supply_is_blackout Job dJ PStateL schedL tL).
      Proof.
        intro Ht. unfold prosa.model.processor.supply.is_blackout, prosa.model.processor.supply.has_supply.
        cbn [I.Prosa_Model_Processor_Supply_is_blackout I.Prosa_Model_Processor_Supply_has_supply].
        exact (svc_bool_not_related _ _ (svc_decide_lt_related _ _ _ _
          (sub_nat_rel_canonical O) (isj_supply_at_related tR tL Ht))).
      Qed.

      Lemma isj_blackout_during_related (t1R t2R : nat) (t1L t2L : Lean.Nat) :
        SubNatRel t1R t1L -> SubNatRel t2R t2L ->
        SubNatRel (@prosa.model.processor.supply.blackout_during Job PStateR schedR t1R t2R)
          (I.Prosa_Model_Processor_Supply_blackout_during Job dJ PStateL schedL t1L t2L).
      Proof.
        intros Ht1 Ht2.
        have Hsum := svc_interval_sum_related t1R t2R t1L t2L
          (fun t => nat_of_bool (@prosa.model.processor.supply.is_blackout Job PStateR schedR t))
          (fun t => I.Bool_toNat (I.Prosa_Model_Processor_Supply_is_blackout Job dJ PStateL schedL t))
          Ht1 Ht2 (fun tR tL Ht => isj_bool_to_nat_related _ _ (isj_is_blackout_related tR tL Ht)).
        change (SubNatRel
          (@prosa.model.processor.supply.blackout_during Job PStateR schedR t1R t2R)
          (I.Prosa_Validation_SupplyInterface_blackoutDuringProjection
            Job dJ PStateL schedL t1L t2L)) in Hsum.
        exact Hsum.
      Qed.
    End SupplySched.

    Lemma isj_fully_consuming_related :
      PropSPropRel (@prosa.model.processor.platform_properties.fully_consuming_proc_model Job PStateR)
        (I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job dJ PStateL).
    Proof.
      unfold prosa.model.processor.platform_properties.fully_consuming_proc_model.
      cbn [I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model].
      apply ar_forall_identity_correspondence. intro j.
      apply cover_schedule. intros sR sL Hs.
      have Hsv := isj_schedule_fun_to_svc sR sL Hs.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (isj_scheduled_at_related sR sL Hsv j _ _ Ht))|].
      exact (sub_nat_eq_correspondence _ _ _ _ (isj_service_at_related sR sL Hsv j _ _ Ht)
        (isj_supply_at_related sR sL Hsv _ _ Ht)).
    Qed.
  End Supply.
End Generic.

(** ** Arrival-sequence cover *)

Definition isj_arrival_sequence_to_source (Job : eqType)
    (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job)) :
    prosa.behavior.arrival_sequence.arrival_sequence Job :=
  fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

Lemma isj_arrival_sequence_to_source_rel (Job : eqType) arrL :
  ArArrivalSequenceRel Job (isj_arrival_sequence_to_source Job arrL) arrL.
Proof.
  intros tR tL Ht. unfold ArListRel, isj_arrival_sequence_to_source.
  refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
  exact (sub_imported_eq_congr arrL _ _ Ht).
Qed.

(** ** Statements *)

Section Statements.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

  Let cover_arrival_sequence :=
    isj_forall_cover_sprop _ _ (ArArrivalSequenceRel Job)
      (ar_arrival_sequence_to_imported Job) (isj_arrival_sequence_to_source Job)
      (ar_arrival_sequence_canonical Job) (isj_arrival_sequence_to_source_rel Job).

  Section RS.
    Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
    Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
    Variable R : SvcProcessorStateRel Job PStateR PStateL.
    Hypothesis Hsupply : IsjSupplyRel Job PStateR PStateL R.

    Definition src_low_service_implies_existence_of_idle_time_rs : Prop :=
      ltac:(body_of (fun s : S.statement_low_service_implies_existence_of_idle_time_rs => s Job jaR PStateR)).
    Definition tgt_low_service_implies_existence_of_idle_time_rs : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_ServiceOfJobs_low_service_implies_existence_of_idle_time_rs
        Job dJ jaL PStateL)).
    Theorem low_service_implies_existence_of_idle_time_rs_correspondence :
      PropSPropRel src_low_service_implies_existence_of_idle_time_rs
        tgt_low_service_implies_existence_of_idle_time_rs.
    Proof.
      apply ar_imp_correspondence; [exact (isj_uniprocessor_related Job PStateR PStateL R)|].
      apply ar_imp_correspondence; [exact (isj_fully_consuming_related Job PStateR PStateL R Hsupply)|].
      apply cover_arrival_sequence. intros arrR arrL Harr.
      apply ar_imp_correspondence;
        [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
      apply (isj_forall_cover_sprop _ _ (IsjScheduleFunRel Job PStateR PStateL R)
        (isj_schedule_to_target Job PStateR PStateL R) (isj_schedule_to_source Job PStateR PStateL R)
        (isj_schedule_to_target_rel Job PStateR PStateL R) (isj_schedule_to_source_rel Job PStateR PStateL R)).
      intros sR sL Hs.
      have Hsv := isj_schedule_fun_to_svc Job PStateR PStateL R sR sL Hs.
      apply ar_imp_correspondence; [exact (isj_jobs_come_from_related Job PStateR PStateL R sR sL Hsv arrR arrL Harr)|].
      apply ar_imp_correspondence; [exact (isj_jobs_must_arrive_related Job PStateR PStateL R sR sL Hsv jaR jaL Hja)|].
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
      apply ar_imp_correspondence.
      - exact (sub_nat_lt_correspondence _ _ _ _
          (svc_target_add_related _ _ _ _
            (isj_blackout_during_related Job PStateR PStateL R Hsupply sR sL Hsv _ _ _ _ Ht1 Ht2)
            (isj_service_of_jobs_predT_related Job PStateR PStateL R sR sL Hsv _ _ _ _ _ _
              (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _
                (sub_nat_rel_canonical O) Ht2) Ht1 Ht2))
          (svc_target_sub_related _ _ _ _ Ht2 Ht1)).
      - exact (isj_idle_exists_related Job PStateR PStateL R sR sL Hsv arrR arrL Harr _ _ _ _ Ht1 Ht2).
    Qed.
  End RS.

  Definition src_low_service_implies_existence_of_idle_time : Prop :=
    ltac:(body_of (fun s : S.statement_low_service_implies_existence_of_idle_time => s Job jaR)).
  Definition tgt_low_service_implies_existence_of_idle_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Ideal_ServiceOfJobs_low_service_implies_existence_of_idle_time
      Job dJ jaL)).

End Statements.
