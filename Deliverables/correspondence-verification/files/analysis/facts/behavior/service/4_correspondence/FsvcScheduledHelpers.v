From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import behavior.all model.schedule.scheduled analysis.definitions.service
  model.processor.platform_properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsService ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedFactsService.

(** Re-bound helper half of the accepted analysis/facts/model/scheduled certificate
    (transports, list/option operations, arrival-sequence / schedule / state
    coverage, ideal-progress and uniprocessor properties, scheduled/served/idle
    operations); its statement certificates are not included.

    Original header: statement correspondences for [analysis/facts/model/scheduled.v].

    Source side: the extracted statement [S.statement_X] specialised at the
    leading input binders [Job], [JobArrival], [ProcessorState].  Target side:
    the type of the imported Lean theorem.  Arrival sequences and schedules
    are covered in both directions; processor states are related by the
    two-sided [SvcProcessorStateRel].  The informative [scheduled_at_dec]
    ([{_} + {_}], Type-valued) is related by a pair of maps in both
    directions ([FsTypeRel]), as in the accepted reflect certificates. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Transports (same as the accepted arrivals certificates) *)

Lemma ari_logic_eq_to_lean_eq {A : Type} (x y : A) : Logic.eq x y -> Lean.eq x y.
Proof. intros []. exact (@Lean.eq_refl _ _). Qed.

Lemma ari_lean_transport {A : Type} (P : A -> SProp) (x y : A) : Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

(** ** Propositional connectives *)

Lemma fs_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [Hpq Hqp]. apply I.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ (Hpq (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP (Hqp (sprop_to_prop _ _ HQ q))).
  - intros [Hpq Hqp]. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ (Hpq (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP (Hqp (prop_to_sprop _ _ HQ q))).
Qed.

Lemma fs_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p|q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intros [p|q]; apply strictly_inhabits.
    + left. exact (sprop_to_prop _ _ HP p).
    + right. exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma fs_exists_id_correspondence (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma fs_eq_id_correspondence (T : Type) (x y : T) : PropSPropRel (x = y) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - exact (coq_eq_to_imported_eq x y).
  - intro H. apply strictly_inhabits. exact (imported_eq_to_coq_eq x y H).
Qed.

Lemma fs_iff_transfer (P P' : Prop) (Q : SProp) :
  (P <-> P') -> PropSPropRel P' Q -> PropSPropRel P Q.
Proof.
  intros [H1 H2] HQ. apply prop_sprop_rel_intro.
  - intro p. exact (prop_to_sprop _ _ HQ (H1 p)).
  - intro q. apply strictly_inhabits. exact (H2 (sprop_to_prop _ _ HQ q)).
Qed.

Lemma fs_not_truth bR bL :
  ArBoolRel bR bL ->
  PropSPropRel (is_true (~~ bR)) (Lean.eq (I.Bool_not bL) I.Bool_true).
Proof. intro H. exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ H)). Qed.

(** ** Lists and options *)

Lemma fs_nilp_related (T : Type) (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL -> ArBoolRel (nilp xsR) (I.List_isEmpty T xsL).
Proof.
  intro H.
  refine (ari_lean_transport (fun l => ArBoolRel (nilp xsR) (I.List_isEmpty T l)) _ _ H _).
  destruct xsR; exact (@Lean.eq_refl _ _).
Qed.

Lemma fs_eq_nil_isEmpty_related (T : eqType) (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL -> ArBoolRel (xsR == [::]) (I.List_isEmpty T xsL).
Proof.
  intro H.
  refine (ari_lean_transport (fun l => ArBoolRel (xsR == [::]) (I.List_isEmpty T l)) _ _ H _).
  destruct xsR; exact (@Lean.eq_refl _ _).
Qed.

Lemma fs_list_eq_truth (T : eqType) (xsR : seq T) (xsL : I.List T) (ysR : seq T) (ysL : I.List T) :
  ArListRel xsR xsL -> ArListRel ysR ysL ->
  PropSPropRel (is_true (xsR == ysR)) (Lean.eq xsL ysL).
Proof.
  intros Hx Hy. apply (fs_iff_transfer _ (xsR = ysR)); [split; [move/eqP; exact (fun E => E) | move=> E; apply/eqP; exact E]|].
  exact (ar_list_eq_correspondence T _ _ _ _ Hx Hy).
Qed.

Lemma fs_list_eq_decide (T : eqType) (xsR : seq T) (xsL : I.List T) (ysR : seq T) (ysL : I.List T)
    (d : I.Decidable (Lean.eq xsL ysL)) :
  ArListRel xsR xsL -> ArListRel ysR ysL ->
  ArBoolRel (xsR == ysR) (I.Decidable_decide (Lean.eq xsL ysL) d).
Proof.
  intros Hx Hy.
  exact (ar_decide_bool_correspondence (xsR == ysR) (Lean.eq xsL ysL) d
    (fs_list_eq_truth T xsR xsL ysR ysL Hx Hy)).
Qed.

Definition fs_option_to_imported {T : Type} (o : option T) : I.Option T :=
  match o with None => I.Option_none T | Some x => I.Option_some T x end.
Definition fs_option_to_rocq {T : Type} (o : I.Option T) : option T :=
  match o with I.Option_none => None | I.Option_some x => Some x end.
Definition FsOptRel {T : Type} (oR : option T) (oL : I.Option T) : SProp :=
  Lean.eq (fs_option_to_imported oR) oL.

Lemma fs_ohead_related (T : Type) (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL -> FsOptRel (ohead xsR) (I.List_head__q T xsL).
Proof.
  intro H.
  refine (ari_lean_transport (fun l => FsOptRel (ohead xsR) (I.List_head__q T l)) _ _ H _).
  destruct xsR; exact (@Lean.eq_refl _ _).
Qed.

Lemma fs_option_eq_correspondence (T : Type) (oR : option T) (oL : I.Option T) (pR : option T) (pL : I.Option T) :
  FsOptRel oR oL -> FsOptRel pR pL -> PropSPropRel (oR = pR) (Lean.eq oL pL).
Proof.
  intros Ho Hp. apply prop_sprop_rel_intro.
  - intro E. destruct E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Ho) Hp).
  - intro E. apply strictly_inhabits.
    have C := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Ho (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hp))).
    have D := f_equal (@fs_option_to_rocq T) C.
    destruct oR, pR; cbn in D; congruence.
Qed.

Lemma fs_option_eq_decide (T : eqType) (oR : option T) (oL : I.Option T) (pR : option T) (pL : I.Option T)
    (d : I.Decidable (Lean.eq oL pL)) :
  FsOptRel oR oL -> FsOptRel pR pL ->
  ArBoolRel (oR == pR) (I.Decidable_decide (Lean.eq oL pL) d).
Proof.
  intros Ho Hp.
  refine (ar_decide_bool_correspondence (oR == pR) (Lean.eq oL pL) d _).
  apply (fs_iff_transfer _ (oR = pR)); [split; [move/eqP; exact (fun E => E) | move=> E; apply/eqP; exact E]|].
  exact (fs_option_eq_correspondence T oR oL pR pL Ho Hp).
Qed.

(** ** Two-way coverage of arrival sequences *)

Section ArrCoverage.
  Context (Job : eqType).
  Definition fs_arrival_sequence_to_source
      (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job)) :
      prosa.behavior.arrival_sequence.arrival_sequence Job :=
    fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).
  Lemma fs_arrival_sequence_to_source_rel arrL :
    ArArrivalSequenceRel Job (fs_arrival_sequence_to_source arrL) arrL.
  Proof.
    intros tR tL Ht. unfold ArListRel, fs_arrival_sequence_to_source.
    refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
    exact (sub_imported_eq_congr arrL _ _ Ht).
  Qed.
  Lemma fs_forall_arrival_sequence
      (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
      (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job) -> SProp) :
    (forall arrR arrL, ArArrivalSequenceRel Job arrR arrL -> PropSPropRel (PR arrR) (PL arrL)) ->
    PropSPropRel (forall arrR, PR arrR) (forall arrL, PL arrL).
  Proof.
    intro H. apply prop_sprop_rel_intro.
    - intros HR arrL. exact (prop_to_sprop _ _ (H _ _ (fs_arrival_sequence_to_source_rel arrL)) (HR _)).
    - intro HL. apply strictly_inhabits. intro arrR.
      exact (sprop_to_prop _ _ (H _ _ (ar_arrival_sequence_canonical Job arrR)) (HL _)).
  Qed.
End ArrCoverage.

(** ** Schedules and processor states (inputs: Job, related processor states) *)

Section Schedules.
  Context (Job : eqType).
  Let d := svc_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job d.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job d PStateL.
  Let SR := SvcScheduleRel Job PStateR PStateL R.
  Let StateR := @prosa.behavior.schedule.State Job PStateR.
  Let StateL := I.Prosa_Behavior_Schedule_ProcessorState_State Job d PStateL.

  Definition fs_sched_to_target (schedR : SchedR) : SchedL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq tL)).
  Definition fs_sched_to_source (schedL : SchedL) : SchedR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)).

  Lemma fs_sched_to_target_rel schedR : SR schedR (fs_sched_to_target schedR).
  Proof.
    intros tR tL Ht. unfold fs_sched_to_target.
    refine (ari_lean_transport (fun x => svc_ps_state_rel Job PStateR PStateL R (schedR tR)
      (svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq x)))) _ _ Ht _).
    refine (ari_lean_transport (fun n => svc_ps_state_rel Job PStateR PStateL R (schedR tR)
      (svc_ps_state_to_target Job PStateR PStateL R (schedR n))) _ _
      (sub_imported_eq_sym _ _ (ari_logic_eq_to_lean_eq _ _ (sub_nat_rocq_roundtrip tR))) _).
    exact (svc_ps_state_rel_canonical Job PStateR PStateL R (schedR tR)).
  Qed.

  Lemma fs_sched_to_source_rel schedL : SR (fs_sched_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. unfold fs_sched_to_source.
    refine (ari_lean_transport (fun x => svc_ps_state_rel Job PStateR PStateL R
      (svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)))
      (schedL x)) _ _ Ht _).
    exact (svc_ps_state_rel_surjective Job PStateR PStateL R (schedL (sub_nat_to_imported tR))).
  Qed.

  Lemma fs_forall_schedule (PR : SchedR -> Prop) (PL : SchedL -> SProp) :
    (forall sR sL, SR sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall sR, PR sR) (forall sL, PL sL).
  Proof.
    intro H. apply prop_sprop_rel_intro.
    - intros HR sL. exact (prop_to_sprop _ _ (H _ _ (fs_sched_to_source_rel sL)) (HR _)).
    - intro HL. apply strictly_inhabits. intro sR.
      exact (sprop_to_prop _ _ (H _ _ (fs_sched_to_target_rel sR)) (HL _)).
  Qed.

  Lemma fs_forall_state (PR : StateR -> Prop) (PL : StateL -> SProp) :
    (forall sR sL, svc_ps_state_rel Job PStateR PStateL R sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall sR, PR sR) (forall sL, PL sL).
  Proof.
    intro H. apply prop_sprop_rel_intro.
    - intros HR sL.
      exact (prop_to_sprop _ _ (H _ _ (svc_ps_state_rel_surjective Job PStateR PStateL R sL)) (HR _)).
    - intro HL. apply strictly_inhabits. intro sR.
      exact (sprop_to_prop _ _ (H _ _ (svc_ps_state_rel_canonical Job PStateR PStateL R sR)) (HL _)).
  Qed.

  Theorem fs_ideal_progress_related :
    PropSPropRel (@prosa.model.processor.platform_properties.ideal_progress_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job d PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.ideal_progress_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model].
    apply ar_forall_identity_correspondence => j.
    apply fs_forall_state => sR sL Hs.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (svc_scheduled_in_related Job PStateR PStateL R j _ _ Hs))|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O)
      (svc_service_in_related Job PStateR PStateL R j _ _ Hs)).
  Qed.

  Section Related.
    Variable schedR : SchedR.
    Variable schedL : SchedL.
    Hypothesis Hsched : SR schedR schedL.

    Lemma fs_scheduled_at_related (j : Job) tR tL :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_scheduled_at Job d PStateL schedL j tL).
    Proof. intro Ht. exact (svc_scheduled_in_related Job PStateR PStateL R j _ _ (Hsched tR tL Ht)). Qed.

    Lemma fs_scheduled_at_truth (j : Job) tR tL :
      SubNatRel tR tL ->
      PropSPropRel (is_true (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR))
        (Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job d PStateL schedL j tL) I.Bool_true).
    Proof. intro Ht. exact (ar_bool_truth_correspondence _ _ (fs_scheduled_at_related j tR tL Ht)). Qed.

    Lemma fs_service_at_related (j : Job) tR tL :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_service_at Job d PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.service_at.
      cbn [I.Prosa_Behavior_Service_service_at].
      exact (svc_service_in_related Job PStateR PStateL R j _ _ (Hsched tR tL Ht)).
    Qed.

    Lemma fs_jobs_come_from_related arrR arrL :
      ArArrivalSequenceRel Job arrR arrL ->
      PropSPropRel (@prosa.behavior.ready.jobs_come_from_arrival_sequence Job PStateR schedR arrR)
        (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job d PStateL schedL arrL).
    Proof.
      intro Harr.
      unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
      cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence].
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (fs_scheduled_at_truth j tR tL Ht)|].
      exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    Qed.

    Lemma fs_jobs_must_arrive_related jaR jaL :
      ArJobArrivalRel Job jaR jaL ->
      PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PStateR schedR)
        (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job d jaL PStateL schedL).
    Proof.
      intro Hja.
      unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute].
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (fs_scheduled_at_truth j tR tL Ht)|].
      exact (ar_bool_truth_correspondence _ _
        (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
    Qed.

    Section WithArr.
      Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
      Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job d.
      Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

      Lemma fs_scheduled_jobs_at_related tR tL :
        SubNatRel tR tL ->
        ArListRel (@prosa.model.schedule.scheduled.scheduled_jobs_at Job PStateR arrR schedR tR)
          (I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job d PStateL arrL schedL tL).
      Proof.
        intro Ht. unfold prosa.model.schedule.scheduled.scheduled_jobs_at.
        cbn [I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at].
        apply ar_filter_related.
        - intro j. exact (fs_scheduled_at_related j tR tL Ht).
        - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr _ _ Ht).
      Qed.

      Lemma fs_scheduled_job_at_related tR tL :
        SubNatRel tR tL ->
        FsOptRel (@prosa.model.schedule.scheduled.scheduled_job_at Job PStateR arrR schedR tR)
          (I.Prosa_Model_Schedule_Scheduled_scheduled_job_at Job d PStateL arrL schedL tL).
      Proof.
        intro Ht. unfold prosa.model.schedule.scheduled.scheduled_job_at.
        cbn [I.Prosa_Model_Schedule_Scheduled_scheduled_job_at].
        exact (fs_ohead_related Job _ _ (fs_scheduled_jobs_at_related tR tL Ht)).
      Qed.

      Lemma fs_is_idle_related tR tL :
        SubNatRel tR tL ->
        ArBoolRel (@prosa.model.schedule.scheduled.is_idle Job PStateR arrR schedR tR)
          (I.Prosa_Model_Schedule_Scheduled_is_idle Job d PStateL arrL schedL tL).
      Proof.
        intro Ht. unfold prosa.model.schedule.scheduled.is_idle.
        cbn [I.Prosa_Model_Schedule_Scheduled_is_idle].
        exact (fs_eq_nil_isEmpty_related Job _ _ (fs_scheduled_jobs_at_related tR tL Ht)).
      Qed.

      Lemma fs_served_jobs_at_related tR tL :
        SubNatRel tR tL ->
        ArListRel (@prosa.analysis.definitions.service.served_jobs_at Job PStateR arrR schedR tR)
          (I.Prosa_Analysis_Definitions_Service_served_jobs_at Job d PStateL arrL schedL tL).
      Proof.
        intro Ht. unfold prosa.analysis.definitions.service.served_jobs_at.
        cbn [I.Prosa_Analysis_Definitions_Service_served_jobs_at].
        apply ar_filter_related.
        - intro j. unfold prosa.behavior.service.receives_service_at.
          cbn [I.Prosa_Behavior_Service_receives_service_at].
          exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (fs_service_at_related j tR tL Ht)).
        - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr _ _ Ht).
      Qed.
    End WithArr.
  End Related.

  Theorem fs_uniprocessor_related :
    PropSPropRel (@prosa.model.processor.platform_properties.uniprocessor_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job d PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.uniprocessor_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply fs_forall_schedule => sR sL Hs.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence; [exact (fs_scheduled_at_truth sR sL Hs j1 tR tL Ht)|].
    apply ar_imp_correspondence; [exact (fs_scheduled_at_truth sR sL Hs j2 tR tL Ht)|].
    exact (fs_eq_id_correspondence Job j1 j2).
  Qed.
End Schedules.
