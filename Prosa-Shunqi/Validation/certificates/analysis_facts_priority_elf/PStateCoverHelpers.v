(* Helper copy of the accepted certificates/analysis_facts_model_task_schedule/PStateCover.v,
   re-bound to this export (imported module renamed), without its service-of-jobs lemmas
   (isj_sum_filter_related, isj_service_of_jobs_predT_related), its Boolean-to-Nat lemma
   (isj_bool_to_nat_related), its two ideal-progress lemmas (isj_ideal_progress_related,
   isj_psr_ideal_progress_related) and its supply-observation section (IsjSupplyRel ... End Supply),
   whose target constants are not part of this export; every other definition and proof is
   unchanged. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import behavior.all model.processor.platform_properties model.processor.supply
  model.schedule.scheduled.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPriorityElf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedFactsPriorityElf.

(** Reusable processor-model infrastructure, extracted without change of
    proofs from the accepted certificate of
    [analysis/facts/model/ideal/service_of_jobs.v] (re-bound to this
    artifact's import): generic combinators, schedule-level operations over
    any per-instant [scheduled_at]/[service_at] correspondence ([Ops]), the
    fixed-input [SvcProcessorStateRel] layer with its [supply_on] extension
    ([Generic]), and the two-way cover of processor models quantified inside
    statements ([PSCover]). *)

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



(** ** Schedule-level operations over any per-instant correspondence of
    [scheduled_at] and [service_at] *)

Section Ops.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsa : forall (j : Job) (tR : nat) (tL : Lean.Nat), SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL).
  Hypothesis Hse : forall (j : Job) (tR : nat) (tL : Lean.Nat), SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).

  Lemma isj_service_during_related (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (I.Prosa_Behavior_Service_service_during Job dJ PStateL schedL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
      (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j t)
      Ht1 Ht2 (fun tR tL Ht => Hse j tR tL Ht).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job dJ PStateL schedL j t1L t2L)) in Hsum.
    exact Hsum.
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
      - intro j. exact (Hsa j tR tL Ht).
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
          [exact (svc_bool_truth_correspondence _ _ (Hsa j _ _ Ht))|].
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
          [exact (svc_bool_truth_correspondence _ _ (Hsa j _ _ Ht))|].
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
End Ops.

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


  (** *** Supply (the [supply_on] field of the processor-state relation) *)

End Generic.

(** ** Processor models quantified inside a statement

    [IsjPSRel PR PL] relates a Rocq and a Lean processor model by bijections
    on states and cores (with both roundtrips), [scheduled_on] per core, and
    the aggregate [service_in]/[supply_in].  Every Rocq model has a related
    Lean model ([isj_ps_to_target], whose [Fintype] is exactly the Rocq
    enumeration, so its finite sums compute along it) and every Lean model has
    a related Rocq model ([isj_ps_to_source], whose cores are the Lean core
    enumeration as a [seq_sub] finType, related through the accepted
    enumeration-based sum lemmas).  Hence universally quantified processor
    models are covered in both directions. *)

Lemma isj_forall_cover_type (A B : Type) (Rel : A -> B -> Type)
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

Lemma isj_bool_rel_true (bR : bool) (bL : I.Bool) :
  SvcBoolRel bR bL -> is_true bR -> Lean.eq bL I.Bool_true.
Proof.
  intros H Hb. destruct bR.
  - exact (sub_imported_eq_sym _ _ H).
  - discriminate Hb.
Qed.

Lemma isj_bool_false_of_rocq (b : I.Bool) : ~~ svc_bool_to_rocq b -> Lean.eq b I.Bool_false.
Proof.
  destruct b; cbn; intro H; first [exact (@Lean.eq_refl _ _) | discriminate H].
Qed.

Definition isj_exists_elim_sprop (T : finType) (p : pred T) (Q : SProp)
    (HQ : forall x, p x -> Q) (H : [exists x, p x]) : Q :=
  match elimT existsP H with ex_intro x Hx => HQ x Hx end.

Fixpoint isj_map_values_canonical (C : Type) (f : C -> nat) (xs : seq C) :
    Lean.eq (svc_nat_list_to_imported (map f xs))
      (I.List_map_inst2 C Lean.Nat (fun c => sub_nat_to_imported (f c)) (svc_list_to_imported xs)) :=
  match xs with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => sub_imported_eq_congr (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported (f x))) _ _
      (isj_map_values_canonical C f tail)
  end.

Fixpoint isj_ar_svc_list_eq {T : Type} (xs : seq T) :
    Lean.eq (ar_list_to_imported xs) (svc_list_to_imported xs) :=
  match xs with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => sub_imported_eq_congr (I.List_cons T x) _ _ (isj_ar_svc_list_eq tail)
  end.

Section PSCover.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSL := I.Prosa_Behavior_Schedule_ProcessorState Job dJ.

  Record IsjPSRel (PR : prosa.behavior.schedule.ProcessorState Job) (PL : PSL) : Type := {
    isj_st_to : @prosa.behavior.schedule.State Job PR ->
      I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PL;
    isj_st_from : I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PL ->
      @prosa.behavior.schedule.State Job PR;
    isj_st_rt_source : forall s, Logic.eq (isj_st_from (isj_st_to s)) s;
    isj_st_rt_target : forall s, Lean.eq (isj_st_to (isj_st_from s)) s;
    isj_co_to : @prosa.behavior.schedule.Core Job PR ->
      I.Prosa_Behavior_Schedule_ProcessorState_Core Job dJ PL;
    isj_co_from : I.Prosa_Behavior_Schedule_ProcessorState_Core Job dJ PL ->
      @prosa.behavior.schedule.Core Job PR;
    isj_co_rt_target : forall c, Lean.eq (isj_co_to (isj_co_from c)) c;
    isj_sch_rel : forall j s c,
      SvcBoolRel (@prosa.behavior.schedule.scheduled_on Job PR j s c)
        (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_on Job dJ PL j (isj_st_to s) (isj_co_to c));
    isj_srv_in_rel : forall j s,
      SubNatRel (@prosa.behavior.schedule.service_in Job PR j s)
        (I.Prosa_Behavior_Schedule_ProcessorState_service_in Job dJ PL j (isj_st_to s));
    isj_sup_in_rel : forall s,
      SubNatRel (@prosa.behavior.schedule.supply_in Job PR s)
        (I.Prosa_Behavior_Schedule_ProcessorState_supply_in Job dJ PL (isj_st_to s)) }.
  Arguments isj_st_to {PR PL} _.
  Arguments isj_st_from {PR PL} _.
  Arguments isj_st_rt_source {PR PL} _.
  Arguments isj_st_rt_target {PR PL} _.
  Arguments isj_co_to {PR PL} _.
  Arguments isj_co_from {PR PL} _.
  Arguments isj_co_rt_target {PR PL} _.
  Arguments isj_sch_rel {PR PL} _.
  Arguments isj_srv_in_rel {PR PL} _.
  Arguments isj_sup_in_rel {PR PL} _.

  Section Pair.
    Variable PR : prosa.behavior.schedule.ProcessorState Job.
    Variable PL : PSL.
    Variable X : IsjPSRel PR PL.

    Lemma isj_psr_scheduled_in_related (j : Job) (s : @prosa.behavior.schedule.State Job PR) :
      SvcBoolRel (@prosa.behavior.schedule.scheduled_in Job PR j s)
        (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_in Job dJ PL j (isj_st_to X s)).
    Proof.
      apply svc_bool_rel_from_truth.
      - intro H. unfold prosa.behavior.schedule.scheduled_in in H.
        apply (I.mpr _ _ (I.Prosa_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff
          Job dJ PL j (isj_st_to X s))).
        refine (isj_exists_elim_sprop _ _ _ _ H). intros c Hc.
        exact (I.Exists_intro _ _ (isj_co_to X c) (isj_bool_rel_true _ _ (isj_sch_rel X j s c) Hc)).
      - intro HL.
        have Hex := I.mp _ _ (I.Prosa_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff
          Job dJ PL j (isj_st_to X s)) HL.
        destruct Hex as [cL HcL].
        unfold prosa.behavior.schedule.scheduled_in.
        apply (svc_exists_intro_strict _ _ (isj_co_from X cL)).
        apply (svc_bool_true_elim _ _ (isj_sch_rel X j s (isj_co_from X cL))).
        exact (isj_lean_transport
          (fun c => Lean.eq (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_on Job dJ PL j
             (isj_st_to X s) c) I.Bool_true)
          _ _ (sub_imported_eq_sym _ _ (isj_co_rt_target X cL)) HcL).
    Qed.

    Let cover_state :=
      isj_forall_cover_sprop _ _
        (fun sR sL => Lean.eq (isj_st_to X sR) sL) (isj_st_to X) (isj_st_from X)
        (fun _ => @Lean.eq_refl _ _) (isj_st_rt_target X).

    Definition IsjPSchedRel (schedR : @prosa.behavior.schedule.schedule Job PR)
        (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PL) : SProp :=
      forall tR tL, SubNatRel tR tL -> Lean.eq (isj_st_to X (schedR tR)) (schedL tL).

    Definition isj_psr_sched_to_target (schedR : @prosa.behavior.schedule.schedule Job PR) :
        I.Prosa_Behavior_Schedule_schedule Job dJ PL :=
      fun tL => isj_st_to X (schedR (sub_nat_to_rocq tL)).

    Definition isj_psr_sched_to_source (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PL) :
        @prosa.behavior.schedule.schedule Job PR :=
      fun tR => isj_st_from X (schedL (sub_nat_to_imported tR)).

    Lemma isj_psr_sched_to_target_rel schedR : IsjPSchedRel schedR (isj_psr_sched_to_target schedR).
    Proof.
      intros tR tL Ht. unfold isj_psr_sched_to_target.
      rewrite (isj_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
    Qed.

    Lemma isj_psr_sched_to_source_rel schedL : IsjPSchedRel (isj_psr_sched_to_source schedL) schedL.
    Proof.
      intros tR tL Ht. unfold isj_psr_sched_to_source.
      exact (sub_imported_eq_trans _ _ _ (isj_st_rt_target X _) (sub_imported_eq_congr schedL _ _ Ht)).
    Qed.

    Let cover_schedule :=
      isj_forall_cover_sprop _ _ IsjPSchedRel isj_psr_sched_to_target isj_psr_sched_to_source
        isj_psr_sched_to_target_rel isj_psr_sched_to_source_rel.

    Section PSched.
      Variable schedR : @prosa.behavior.schedule.schedule Job PR.
      Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PL.
      Hypothesis Hs : IsjPSchedRel schedR schedL.

      Lemma isj_psr_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        SvcBoolRel (@prosa.behavior.service.scheduled_at Job PR schedR j tR)
          (I.Prosa_Behavior_Service_scheduled_at Job dJ PL schedL j tL).
      Proof.
        intro Ht. unfold prosa.behavior.service.scheduled_at.
        cbn [I.Prosa_Behavior_Service_scheduled_at].
        exact (isj_lean_transport
          (fun sL => SvcBoolRel (@prosa.behavior.schedule.scheduled_in Job PR j (schedR tR))
             (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_in Job dJ PL j sL))
          _ _ (Hs tR tL Ht) (isj_psr_scheduled_in_related j (schedR tR))).
      Qed.

      Lemma isj_psr_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        SubNatRel (@prosa.behavior.service.service_at Job PR schedR j tR)
          (I.Prosa_Behavior_Service_service_at Job dJ PL schedL j tL).
      Proof.
        intro Ht. unfold prosa.behavior.service.service_at.
        cbn [I.Prosa_Behavior_Service_service_at].
        exact (isj_lean_transport
          (fun sL => SubNatRel (@prosa.behavior.schedule.service_in Job PR j (schedR tR))
             (I.Prosa_Behavior_Schedule_ProcessorState_service_in Job dJ PL j sL))
          _ _ (Hs tR tL Ht) (isj_srv_in_rel X j (schedR tR))).
      Qed.
    End PSched.

    Lemma isj_psr_uniprocessor_related :
      PropSPropRel (@prosa.model.processor.platform_properties.uniprocessor_model Job PR)
        (I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job dJ PL).
    Proof.
      unfold prosa.model.processor.platform_properties.uniprocessor_model.
      cbn [I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model].
      apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      apply cover_schedule. intros sR sL Hs.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related sR sL Hs j1 _ _ Ht))|].
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related sR sL Hs j2 _ _ Ht))|].
      exact (isj_eq_identity_correspondence Job j1 j2).
    Qed.

  End Pair.

  (** *** Rocq model to Lean model *)

  Section ToTarget.
    Variable PR : prosa.behavior.schedule.ProcessorState Job.
    Let CR := @prosa.behavior.schedule.Core Job PR.
    Let enumL : I.List CR := svc_list_to_imported (enum CR).

    Lemma isj_enum_nodup : I.List_Nodup CR enumL.
    Proof.
      exact (isj_lean_transport (fun l => I.List_Nodup CR l) _ _ (isj_ar_svc_list_eq (enum CR))
        (ar_uniq_truth_forward CR (enum CR) (sub_nat_prop_to_truth _ (enum_uniq CR)))).
    Qed.

    Lemma isj_enum_complete : forall c : CR, ar_target_mem c enumL.
    Proof.
      intro c.
      exact (prop_to_sprop _ _ (ar_membership_correspondence CR c (enum CR) enumL
        (isj_ar_svc_list_eq (enum CR))) (mem_enum CR c)).
    Qed.

    Lemma isj_law_le : forall j s r,
      I.LE_le_inst1 I.Prosa_Behavior_Job_work I.instLENat
        (sub_nat_to_imported (@prosa.behavior.schedule.service_on Job PR j s r))
        (sub_nat_to_imported (@prosa.behavior.schedule.supply_on Job PR s r)).
    Proof.
      intros j s r.
      exact (prop_to_sprop _ _ (sub_nat_le_correspondence _ _ _ _
        (sub_nat_rel_canonical _) (sub_nat_rel_canonical _))
        (@prosa.behavior.schedule.service_on_le_supply_on Job PR j s r)).
    Qed.

    Lemma isj_law_zero : forall j s r,
      Lean.eq (svc_bool_to_imported (@prosa.behavior.schedule.scheduled_on Job PR j s r)) I.Bool_false ->
      Lean.eq (sub_nat_to_imported (@prosa.behavior.schedule.service_on Job PR j s r))
        (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Job_work 0 (I.instOfNatNat 0)).
    Proof.
      intros j s r H.
      destruct (@prosa.behavior.schedule.scheduled_on Job PR j s r) eqn:E.
      - exact (svc_false_elim _ (svc_false_ne_true (sub_imported_eq_sym _ _ H))).
      - have Z := @prosa.behavior.schedule.service_on_implies_scheduled_on Job PR j s r (negbT E).
        exact (isj_lean_transport (fun n => Lean.eq (sub_nat_to_imported n)
            (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Job_work 0 (I.instOfNatNat 0)))
          _ _ (coq_eq_to_imported_eq _ _ (Logic.eq_sym Z)) (sub_nat_rel_canonical O)).
    Qed.

    Definition isj_ps_to_target : PSL :=
      I.Prosa_Behavior_Schedule_ProcessorState_mk Job dJ
        (@prosa.behavior.schedule.State Job PR) CR
        (I.Prosa_Validation_ProcessorStateCoverInterface_fintypeOfNodupListing CR enumL
          isj_enum_nodup isj_enum_complete)
        (ar_decidable_eq CR)
        (fun j s c => svc_bool_to_imported (@prosa.behavior.schedule.scheduled_on Job PR j s c))
        (fun s c => sub_nat_to_imported (@prosa.behavior.schedule.supply_on Job PR s c))
        (fun j s c => sub_nat_to_imported (@prosa.behavior.schedule.service_on Job PR j s c))
        isj_law_le isj_law_zero.

    Lemma isj_to_target_service_in (j : Job) (s : @prosa.behavior.schedule.State Job PR) :
      SubNatRel (@prosa.behavior.schedule.service_in Job PR j s)
        (I.Prosa_Behavior_Schedule_ProcessorState_service_in Job dJ isj_ps_to_target j s).
    Proof.
      unfold prosa.behavior.schedule.service_in. rewrite -big_enum.
      rewrite (svc_mathcomp_big_seq_as_fold_core CR (enum CR)).
      change (SubNatRel (foldr addn O (map (fun c => @prosa.behavior.schedule.service_on Job PR j s c) (enum CR)))
        (svc_target_list_sum (I.List_map_inst2 CR Lean.Nat
          (fun c => sub_nat_to_imported (@prosa.behavior.schedule.service_on Job PR j s c))
          (svc_list_to_imported (enum CR))))).
      apply svc_list_sum_related.
      exact (isj_map_values_canonical CR _ (enum CR)).
    Qed.

    Lemma isj_to_target_supply_in (s : @prosa.behavior.schedule.State Job PR) :
      SubNatRel (@prosa.behavior.schedule.supply_in Job PR s)
        (I.Prosa_Behavior_Schedule_ProcessorState_supply_in Job dJ isj_ps_to_target s).
    Proof.
      unfold prosa.behavior.schedule.supply_in. rewrite -big_enum.
      rewrite (svc_mathcomp_big_seq_as_fold_core CR (enum CR)).
      change (SubNatRel (foldr addn O (map (fun c => @prosa.behavior.schedule.supply_on Job PR s c) (enum CR)))
        (svc_target_list_sum (I.List_map_inst2 CR Lean.Nat
          (fun c => sub_nat_to_imported (@prosa.behavior.schedule.supply_on Job PR s c))
          (svc_list_to_imported (enum CR))))).
      apply svc_list_sum_related.
      exact (isj_map_values_canonical CR _ (enum CR)).
    Qed.

    Definition isj_rel_to_target : IsjPSRel PR isj_ps_to_target :=
      Build_IsjPSRel PR isj_ps_to_target
        (fun s : @prosa.behavior.schedule.State Job PR => s)
        (fun s : @prosa.behavior.schedule.State Job PR => s)
        (fun s => Logic.eq_refl s) (fun s => @Lean.eq_refl _ s)
        (fun c : CR => c) (fun c : CR => c) (fun c => @Lean.eq_refl _ c)
        (fun j s c => @Lean.eq_refl _ _)
        isj_to_target_service_in isj_to_target_supply_in.
  End ToTarget.

  (** *** Lean model to Rocq model *)

  Section ToSource.
    Variable PL : PSL.
    Let CL := I.Prosa_Behavior_Schedule_ProcessorState_Core Job dJ PL.
    Let SL := I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PL.
    Let decL := I.Prosa_Behavior_Schedule_ProcessorState_coreDecidableEq Job dJ PL.

    Definition isj_core_eqb (x y : CL) : bool :=
      svc_bool_to_rocq (I.Decidable_decide (Lean.eq x y) (decL x y)).

    Lemma isj_core_eqP : Equality.axiom isj_core_eqb.
    Proof.
      intros x y. unfold isj_core_eqb.
      destruct (decL x y) as [Hne | He]; cbn.
      - apply ReflectF. intro E. destruct E.
        exact (match Hne (@Lean.eq_refl _ x) with end).
      - apply ReflectT. exact (imported_eq_to_coq_eq _ _ He).
    Qed.

    Definition isj_core_eqType : eqType := HB.pack CL (hasDecEq.Build CL isj_core_eqP).

    Definition isj_core_list : seq isj_core_eqType :=
      ar_list_to_rocq (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ PL).

    Lemma isj_core_list_rel :
      ArListRel isj_core_list (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ PL).
    Proof. exact (ar_list_target_roundtrip _). Qed.

    Lemma isj_core_list_uniq : uniq isj_core_list.
    Proof.
      exact (sprop_to_prop _ _ (ar_uniq_correspondence isj_core_eqType _ _ isj_core_list_rel)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration_nodup Job dJ PL)).
    Qed.

    Lemma isj_core_list_complete (c : CL) : (c : isj_core_eqType) \in isj_core_list.
    Proof.
      exact (sprop_to_prop _ _ (ar_membership_correspondence isj_core_eqType c _ _ isj_core_list_rel)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration_complete Job dJ PL c)).
    Qed.

    Definition isj_core_finType : finType := adhoc_seq_sub_finType isj_core_list.

    Definition isj_core_from (c : CL) : isj_core_finType :=
      @SeqSub isj_core_eqType isj_core_list c (isj_core_list_complete c).

    Lemma isj_core_enum_map : map (@ssval isj_core_eqType isj_core_list) (enum isj_core_finType) = isj_core_list.
    Proof. rewrite enumT unlock /=. exact (val_seq_sub_enum isj_core_list_uniq). Qed.

    Definition isj_src_scheduled_on (j : Job) (s : SL) (c : isj_core_finType) : bool :=
      svc_bool_to_rocq (I.Prosa_Behavior_Schedule_ProcessorState_scheduled_on Job dJ PL j s (ssval c)).
    Definition isj_src_supply_on (s : SL) (c : isj_core_finType) : nat :=
      sub_nat_to_rocq (I.Prosa_Behavior_Schedule_ProcessorState_supply_on Job dJ PL s (ssval c)).
    Definition isj_src_service_on (j : Job) (s : SL) (c : isj_core_finType) : nat :=
      sub_nat_to_rocq (I.Prosa_Behavior_Schedule_ProcessorState_service_on Job dJ PL j s (ssval c)).

    Lemma isj_src_law_le j s r : leq (isj_src_service_on j s r) (isj_src_supply_on s r).
    Proof.
      exact (sprop_to_prop _ _ (sub_nat_le_correspondence _ _ _ _
        (sub_nat_rel_surjective _) (sub_nat_rel_surjective _))
        (I.service_on_le_supply_on Job dJ PL j s (ssval r))).
    Qed.

    Lemma isj_src_law_zero j s r : ~~ isj_src_scheduled_on j s r -> isj_src_service_on j s r = O.
    Proof.
      unfold isj_src_scheduled_on, isj_src_service_on. intro H.
      have E : sub_nat_to_rocq (I.Prosa_Behavior_Schedule_ProcessorState_service_on Job dJ PL j s (ssval r))
          = sub_nat_to_rocq (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Job_work 0 (I.instOfNatNat 0)) :=
        f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _
          (I.service_on_implies_scheduled_on Job dJ PL j s (ssval r) (isj_bool_false_of_rocq _ H))).
      rewrite E. exact (sub_nat_rocq_roundtrip O).
    Qed.

    Definition isj_ps_to_source : prosa.behavior.schedule.ProcessorState Job :=
      @prosa.behavior.schedule.Build_ProcessorState Job SL isj_core_finType
        isj_src_scheduled_on isj_src_supply_on isj_src_service_on
        isj_src_law_le isj_src_law_zero.

    Lemma isj_core_enumeration_rel :
      SvcCoreEnumerationRel isj_core_finType CL (@ssval isj_core_eqType isj_core_list)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ PL).
    Proof.
      unfold SvcCoreEnumerationRel. rewrite isj_core_enum_map.
      exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ (isj_ar_svc_list_eq _))
        isj_core_list_rel).
    Qed.

    Lemma isj_to_source_service_in (j : Job) (s : SL) :
      SubNatRel (@prosa.behavior.schedule.service_in Job isj_ps_to_source j s)
        (I.Prosa_Behavior_Schedule_ProcessorState_service_in Job dJ PL j s).
    Proof.
      have Hsum := svc_finite_sum_related isj_core_finType CL (@ssval isj_core_eqType isj_core_list)
        (fun c => isj_src_service_on j s c)
        (fun c => I.Prosa_Behavior_Schedule_ProcessorState_service_on Job dJ PL j s c)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ PL)
        (fun c => sub_nat_rel_surjective _) isj_core_enumeration_rel.
      exact (sub_imported_eq_trans _ _ _ Hsum (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ScheduleInterface_production_service_in_as_list_sum Job dJ PL j s))).
    Qed.

    Lemma isj_to_source_supply_in (s : SL) :
      SubNatRel (@prosa.behavior.schedule.supply_in Job isj_ps_to_source s)
        (I.Prosa_Behavior_Schedule_ProcessorState_supply_in Job dJ PL s).
    Proof.
      have Hsum := svc_finite_sum_related isj_core_finType CL (@ssval isj_core_eqType isj_core_list)
        (fun c => isj_src_supply_on s c)
        (fun c => I.Prosa_Behavior_Schedule_ProcessorState_supply_on Job dJ PL s c)
        (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ PL)
        (fun c => sub_nat_rel_surjective _) isj_core_enumeration_rel.
      exact (sub_imported_eq_trans _ _ _ Hsum (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ScheduleInterface_production_supply_in_as_list_sum Job dJ PL s))).
    Qed.

    Definition isj_rel_to_source : IsjPSRel isj_ps_to_source PL :=
      Build_IsjPSRel isj_ps_to_source PL
        (fun s : SL => s) (fun s : SL => s)
        (fun s => Logic.eq_refl s) (fun s => @Lean.eq_refl _ s)
        (fun c : isj_core_finType => ssval c) isj_core_from (fun c => @Lean.eq_refl _ c)
        (fun j s c => svc_bool_target_roundtrip _)
        isj_to_source_service_in isj_to_source_supply_in.
  End ToSource.

  Definition isj_cover_pstate :=
    isj_forall_cover_type _ _ IsjPSRel isj_ps_to_target isj_ps_to_source
      isj_rel_to_target isj_rel_to_source.
End PSCover.

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

