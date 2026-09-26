From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import FactsPriorityInversionSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPriorityInversion ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PriorityInversionCorrespondence.

Module I := ImportedFactsPriorityInversion.
Module S := FactsPriorityInversionSemanticSource.FactsPriorityInversionSemanticSource.
Module P := PriorityInversionSemanticSource.PriorityInversionSemanticSource.

(** Statement correspondences for [analysis/facts/priority/inversion.v].

    Source side: the extracted statements [S.statement_X] (and the
    Type-valued [reflect] view) specialised at their leading inputs (job
    type, job arrival, processor state, arrival sequence; for the last
    lemma schedule, policy and job); target side: the imported Lean theorem
    types.  Inputs: [job_arrival] by [ArJobArrivalRel], processor states by
    the accepted two-sided [SvcProcessorStateRel], arrival sequences by
    [ArArrivalSequenceRel].  Schedules and JLFP policies quantified inside a
    statement are covered in both directions (through the state conversion
    with its roundtrips, and pointwise on Booleans); jobs are identity
    carriers, Nats are covered in both directions.  [priority_inversion] and
    its cumulative sum are closed by the accepted
    [PriorityInversionCorrespondence]; [reflect] is related to the imported
    [BoolReflect] family by constructor-preserving maps.  No source or
    target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fpi_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Lemma fpi_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma fpi_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma fpi_eq_correspondence (T : Type) (x y : T) : PropSPropRel (x = y) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. destruct E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (imported_eq_to_coq_eq _ _ E).
Qed.

Lemma fpi_bool_eq_correspondence (bR cR : bool) (bL cL : I.Bool) :
  ArBoolRel bR bL -> ArBoolRel cR cL -> PropSPropRel (bR = cR) (Lean.eq bL cL).
Proof.
  intros Hb Hc. apply prop_sprop_rel_intro.
  - intro E. destruct E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hb) Hc).
  - intro E. apply strictly_inhabits.
    have EL := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hb (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hc))).
    destruct bR, cR; cbn in EL; solve [reflexivity | discriminate EL].
Qed.

Lemma fpi_exists_identity (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma fpi_exists2_identity (T : Type) (PR QR : T -> Prop) (PL QL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) -> (forall x, PropSPropRel (QR x) (QL x)) ->
  PropSPropRel (exists2 x, PR x & QR x) (I.Exists T (fun x => Lean.And (PL x) (QL x))).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [x Hx Hy].
    exact (I.Exists_intro T _ x (Lean.And_intro _ _ (prop_to_sprop _ _ (HP x) Hx) (prop_to_sprop _ _ (HQ x) Hy))).
  - intros [x Hxy]. destruct Hxy as [Ha Hb]. apply strictly_inhabits. exists x.
    + exact (sprop_to_prop _ _ (HP x) Ha).
    + exact (sprop_to_prop _ _ (HQ x) Hb).
Qed.

Section Inversion.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.

  (** *** Covers for inner schedules and policies *)

  Definition fpi_schedule_to_target (schedR : SchedR) : SchedL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq tL)).

  Definition fpi_schedule_to_source (schedL : SchedL) : SchedR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)).

  Lemma fpi_schedule_to_target_rel schedR :
    SvcScheduleRel Job PStateR PStateL R schedR (fpi_schedule_to_target schedR).
  Proof.
    intros tR tL Ht. unfold fpi_schedule_to_target.
    rewrite (fpi_nat_input _ _ Ht).
    exact (svc_ps_state_rel_canonical Job PStateR PStateL R (schedR tR)).
  Qed.

  Lemma fpi_schedule_to_source_rel schedL :
    SvcScheduleRel Job PStateR PStateL R (fpi_schedule_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. unfold fpi_schedule_to_source.
    exact (fpi_lean_transport
      (fun sL => svc_ps_state_rel Job PStateR PStateL R
        (svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR))) sL)
      _ _ (sub_imported_eq_congr schedL _ _ Ht)
      (svc_ps_state_rel_surjective Job PStateR PStateL R _)).
  Qed.

  Let cover_schedule :=
    fpi_forall_cover_sprop _ _ (SvcScheduleRel Job PStateR PStateL R)
      fpi_schedule_to_target fpi_schedule_to_source
      fpi_schedule_to_target_rel fpi_schedule_to_source_rel.

  Definition FpiJLFPRel (pR : prosa.model.priority.definitions.JLFP_policy Job)
      (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ) : SProp :=
    forall x y : Job,
      ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
        (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Definition fpi_jlfp_to_target (pR : prosa.model.priority.definitions.JLFP_policy Job) :
      I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ :=
    I.Prosa_Model_Priority_Definitions_JLFP_policy_mk Job dJ
      (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_job Job pR x y)).

  Definition fpi_jlfp_to_source (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ) :
      prosa.model.priority.definitions.JLFP_policy Job :=
    fun x y => ar_bool_to_rocq (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Lemma fpi_jlfp_to_target_rel pR : FpiJLFPRel pR (fpi_jlfp_to_target pR).
  Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

  Lemma fpi_jlfp_to_source_rel pL : FpiJLFPRel (fpi_jlfp_to_source pL) pL.
  Proof. intros x y. exact (ar_bool_target_roundtrip _). Qed.

  Let cover_jlfp :=
    fpi_forall_cover_sprop _ _ FpiJLFPRel fpi_jlfp_to_target fpi_jlfp_to_source
      fpi_jlfp_to_target_rel fpi_jlfp_to_source_rel.

  (** *** Hypotheses of the statements *)

  Let VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.

  Section Sched.
    Variable schedR : SchedR.
    Variable schedL : SchedL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Let SCHED := pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched.

    Lemma fpi_jobs_come_from_related :
      PropSPropRel (@prosa.behavior.ready.jobs_come_from_arrival_sequence Job PStateR schedR arrR)
        (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job dJ PStateL schedL arrL).
    Proof.
      unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
      cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (SCHED j tR tL Ht))|].
      exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    Qed.

    Lemma fpi_jobs_must_arrive_related :
      PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PStateR schedR)
        (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job dJ jaL PStateL schedL).
    Proof.
      unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (SCHED j tR tL Ht))|].
      exact (ar_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
    Qed.

    Section Policy.
      Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
      Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
      Hypothesis Hp : FpiJLFPRel pR pL.

      Let PI := priority_inversion_correspondence Job PStateR PStateL R arrR arrL Harr schedR schedL Hsched pR pL Hp.

      Lemma fpi_reflexive_related :
        PropSPropRel (@prosa.model.priority.definitions.reflexive_job_priorities Job pR)
          (I.Prosa_Model_Priority_Definitions_reflexive_job_priorities Job dJ pL).
      Proof.
        unfold prosa.model.priority.definitions.reflexive_job_priorities.
        cbn [I.Prosa_Model_Priority_Definitions_reflexive_job_priorities].
        apply ar_forall_identity_correspondence. intro j.
        exact (ar_bool_truth_correspondence _ _ (Hp j j)).
      Qed.

      Lemma fpi_is_idle_related (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        ArBoolRel (@prosa.model.schedule.scheduled.is_idle Job PStateR arrR schedR tR)
          (I.Prosa_Model_Schedule_Scheduled_is_idle Job dJ PStateL arrL schedL tL).
      Proof.
        intro Ht. unfold prosa.model.schedule.scheduled.is_idle.
        cbn [I.Prosa_Model_Schedule_Scheduled_is_idle].
        have Hs := pi_scheduled_jobs_at_related Job PStateR PStateL R arrR arrL Harr schedR schedL Hsched tR tL Ht.
        refine (fpi_lean_transport (fun l => ArBoolRel _ (I.List_isEmpty Job l)) _ _ Hs _).
        destruct (@prosa.model.schedule.scheduled.scheduled_jobs_at Job PStateR arrR schedR tR);
          exact (@Lean.eq_refl _ _).
      Qed.

      Section Job.
        Variable j : Job.

        Lemma fpi_not_pi_related (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
          PropSPropRel (is_true (~~ @P.priority_inversion Job PStateR arrR schedR pR j tR))
            (Lean.eq (I.Bool_not (I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion
              Job dJ PStateL arrL schedL pL j tL)) I.Bool_true).
        Proof. exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (PI j tR tL Ht))). Qed.
      End Job.
    End Policy.
  End Sched.

  Lemma fpi_uniprocessor_related :
    PropSPropRel (@prosa.model.processor.platform_properties.uniprocessor_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.uniprocessor_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply cover_schedule. intros schedR schedL Hsched.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j1 tR tL Ht))|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j2 tR tL Ht))|].
    exact (fpi_eq_correspondence Job j1 j2).
  Qed.

  (** Common prefix of the six uniprocessor-context statements: the arrival
      sequence is valid, and for every schedule the two schedule
      hypotheses hold. *)

  Definition src_sched_itself_implies_no_priority_inversion : Prop :=
    ltac:(body_of (fun s : S.statement_sched_itself_implies_no_priority_inversion => s Job jaR PStateR arrR)).
  Definition tgt_sched_itself_implies_no_priority_inversion : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Inversion_sched_itself_implies_no_priority_inversion
      Job dJ jaL PStateL arrL)).
  Theorem sched_itself_implies_no_priority_inversion_correspondence :
    PropSPropRel src_sched_itself_implies_no_priority_inversion tgt_sched_itself_implies_no_priority_inversion.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply cover_schedule. intros schedR schedL Hsched.
    apply ar_imp_correspondence; [exact (fpi_jobs_come_from_related schedR schedL Hsched)|].
    apply ar_imp_correspondence; [exact (fpi_jobs_must_arrive_related schedR schedL Hsched)|].
    apply cover_jlfp. intros pR pL Hp.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht))|].
    exact (fpi_not_pi_related schedR schedL Hsched pR pL Hp j tR tL Ht).
  Qed.

  Definition src_priority_inversion_scheduled_at : Prop :=
    ltac:(body_of (fun s : S.statement_priority_inversion_scheduled_at => s Job jaR PStateR arrR)).
  Definition tgt_priority_inversion_scheduled_at : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Inversion_priority_inversion_scheduled_at
      Job dJ jaL PStateL arrL)).
  Theorem priority_inversion_scheduled_at_correspondence :
    PropSPropRel src_priority_inversion_scheduled_at tgt_priority_inversion_scheduled_at.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply cover_schedule. intros schedR schedL Hsched.
    apply ar_imp_correspondence; [exact (fpi_jobs_come_from_related schedR schedL Hsched)|].
    apply ar_imp_correspondence; [exact (fpi_jobs_must_arrive_related schedR schedL Hsched)|].
    apply cover_jlfp. intros pR pL Hp.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _
        (priority_inversion_correspondence Job PStateR PStateL R arrR arrL Harr schedR schedL Hsched pR pL Hp j tR tL Ht))|].
    apply fpi_exists_identity. intro j'.
    exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j' tR tL Ht)).
  Qed.

  Definition src_no_priority_inversion_when_idle : Prop :=
    ltac:(body_of (fun s : S.statement_no_priority_inversion_when_idle => s Job jaR PStateR arrR)).
  Definition tgt_no_priority_inversion_when_idle : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Inversion_no_priority_inversion_when_idle
      Job dJ jaL PStateL arrL)).
  Theorem no_priority_inversion_when_idle_correspondence :
    PropSPropRel src_no_priority_inversion_when_idle tgt_no_priority_inversion_when_idle.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply cover_schedule. intros schedR schedL Hsched.
    apply ar_imp_correspondence; [exact (fpi_jobs_come_from_related schedR schedL Hsched)|].
    apply ar_imp_correspondence; [exact (fpi_jobs_must_arrive_related schedR schedL Hsched)|].
    apply cover_jlfp. intros pR pL Hp.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (fpi_is_idle_related schedR schedL Hsched tR tL Ht))|].
    exact (fpi_not_pi_related schedR schedL Hsched pR pL Hp j tR tL Ht).
  Qed.

  Definition src_priority_inversion_hep_job : Prop :=
    ltac:(body_of (fun s : S.statement_priority_inversion_hep_job => s Job jaR PStateR arrR)).
  Definition tgt_priority_inversion_hep_job : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Inversion_priority_inversion_hep_job
      Job dJ jaL PStateL arrL)).
  Theorem priority_inversion_hep_job_correspondence :
    PropSPropRel src_priority_inversion_hep_job tgt_priority_inversion_hep_job.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply cover_schedule. intros schedR schedL Hsched.
    apply ar_imp_correspondence; [exact (fpi_jobs_come_from_related schedR schedL Hsched)|].
    apply ar_imp_correspondence; [exact (fpi_jobs_must_arrive_related schedR schedL Hsched)|].
    apply cover_jlfp. intros pR pL Hp.
    apply ar_imp_correspondence; [exact (fpi_reflexive_related pR pL Hp)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact fpi_uniprocessor_related|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j' tR tL Ht))|].
    exact (fpi_bool_eq_correspondence _ _ _ _
      (priority_inversion_correspondence Job PStateR PStateL R arrR arrL Harr schedR schedL Hsched pR pL Hp j tR tL Ht)
      (svc_bool_not_related _ _ (Hp j' j))).
  Qed.

  Definition src_no_priority_inversion_when_hep_job_scheduled : Prop :=
    ltac:(body_of (fun s : S.statement_no_priority_inversion_when_hep_job_scheduled => s Job jaR PStateR arrR)).
  Definition tgt_no_priority_inversion_when_hep_job_scheduled : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Inversion_no_priority_inversion_when_hep_job_scheduled
      Job dJ jaL PStateL arrL)).
  Theorem no_priority_inversion_when_hep_job_scheduled_correspondence :
    PropSPropRel src_no_priority_inversion_when_hep_job_scheduled tgt_no_priority_inversion_when_hep_job_scheduled.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply cover_schedule. intros schedR schedL Hsched.
    apply ar_imp_correspondence; [exact (fpi_jobs_come_from_related schedR schedL Hsched)|].
    apply ar_imp_correspondence; [exact (fpi_jobs_must_arrive_related schedR schedL Hsched)|].
    apply cover_jlfp. intros pR pL Hp.
    apply ar_imp_correspondence; [exact (fpi_reflexive_related pR pL Hp)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact fpi_uniprocessor_related|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j' tR tL Ht))|].
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp j' j))|].
    exact (fpi_not_pi_related schedR schedL Hsched pR pL Hp j tR tL Ht).
  Qed.

  (** *** The [reflect] view *)

  Definition fpi_reflect_forward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
      (HP : PropSPropRel PR PL) (Hb : ArBoolRel bR bL) :
      reflect PR bR ->
      I.Prosa_Analysis_Definitions_BusyInterval_Classical_BoolReflect PL bL.
  Proof.
    destruct Hb. intro HR. destruct HR as [Htrue | Hfalse].
    - exact (I.Prosa_Analysis_Definitions_BusyInterval_Classical_BoolReflect_isTrue
        PL (prop_to_sprop _ _ HP Htrue)).
    - exact (I.Prosa_Analysis_Definitions_BusyInterval_Classical_BoolReflect_isFalse
        PL (fun HL => ar_coq_false_to_target (Hfalse (sprop_to_prop _ _ HP HL)))).
  Defined.

  Definition fpi_reflect_backward_at_bool (PR : Prop) (PL : SProp)
      (HP : PropSPropRel PR PL) (bL : I.Bool) :
      I.Prosa_Analysis_Definitions_BusyInterval_Classical_BoolReflect PL bL ->
      reflect PR (ar_bool_to_rocq bL) :=
    fun HL =>
      match HL in I.Prosa_Analysis_Definitions_BusyInterval_Classical_BoolReflect _ b
        return reflect PR (ar_bool_to_rocq b) with
      | I.Prosa_Analysis_Definitions_BusyInterval_Classical_BoolReflect_isTrue Htrue =>
          ReflectT PR (sprop_to_prop _ _ HP Htrue)
      | I.Prosa_Analysis_Definitions_BusyInterval_Classical_BoolReflect_isFalse Hfalse =>
          ReflectF PR (fun HR =>
            interpret_strict Logic.False
              (ar_target_false_to_strict (Hfalse (prop_to_sprop _ _ HP HR))))
      end.

  Definition fpi_reflect_backward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
      (HP : PropSPropRel PR PL) (Hb : ArBoolRel bR bL) :
      I.Prosa_Analysis_Definitions_BusyInterval_Classical_BoolReflect PL bL ->
      reflect PR bR.
  Proof.
    destruct Hb. destruct bR; cbn; exact (fpi_reflect_backward_at_bool PR PL HP _).
  Defined.

  Lemma fpi_witness_related schedR schedL (Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL)
      pR pL (Hp : FpiJLFPRel pR pL) (j : Job) (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
    PropSPropRel
      (exists2 j' : Job, @prosa.behavior.service.scheduled_at Job PStateR schedR j' tR
        & ~~ @prosa.model.priority.definitions.hep_job Job pR j' j)
      (I.Exists Job (fun j' => Lean.And
        (Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j' tL) I.Bool_true)
        (Lean.eq (I.Bool_not (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL j' j)) I.Bool_true))).
  Proof.
    apply fpi_exists2_identity; intro j'.
    - exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j' tR tL Ht)).
    - exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hp j' j))).
  Qed.

  Definition src_uni_priority_inversion_P : Type :=
    ltac:(body_of (fun s : S.statement_uni_priority_inversion_P => s Job jaR PStateR arrR)).
  Definition tgt_uni_priority_inversion_P : Type :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Inversion_uni_priority_inversion_P
      Job dJ jaL PStateL arrL)).

  Theorem uni_priority_inversion_P_correspondence :
    Datatypes.prod (src_uni_priority_inversion_P -> tgt_uni_priority_inversion_P)
      (tgt_uni_priority_inversion_P -> src_uni_priority_inversion_P).
  Proof.
    split.
    - intros f HvL schedL HfL HmL pL HrL j HuL tL.
      pose (schedR := fpi_schedule_to_source schedL).
      pose (pR := fpi_jlfp_to_source pL).
      have Hs := fpi_schedule_to_source_rel schedL.
      have Hp := fpi_jlfp_to_source_rel pL.
      exact (fpi_reflect_forward _ _ _ _
        (fpi_witness_related schedR schedL Hs pR pL Hp j _ _ (sub_nat_rel_surjective tL))
        (priority_inversion_correspondence Job PStateR PStateL R arrR arrL Harr schedR schedL Hs pR pL Hp j _ _
          (sub_nat_rel_surjective tL))
        (f (sprop_to_prop _ _ VALID HvL) schedR
          (sprop_to_prop _ _ (fpi_jobs_come_from_related schedR schedL Hs) HfL)
          (sprop_to_prop _ _ (fpi_jobs_must_arrive_related schedR schedL Hs) HmL)
          pR (sprop_to_prop _ _ (fpi_reflexive_related pR pL Hp) HrL) j
          (sprop_to_prop _ _ fpi_uniprocessor_related HuL) (sub_nat_to_rocq tL))).
    - intros g HvR schedR HfR HmR pR HrR j HuR tR.
      pose (schedL := fpi_schedule_to_target schedR).
      pose (pL := fpi_jlfp_to_target pR).
      have Hs := fpi_schedule_to_target_rel schedR.
      have Hp := fpi_jlfp_to_target_rel pR.
      exact (fpi_reflect_backward _ _ _ _
        (fpi_witness_related schedR schedL Hs pR pL Hp j _ _ (sub_nat_rel_canonical tR))
        (priority_inversion_correspondence Job PStateR PStateL R arrR arrL Harr schedR schedL Hs pR pL Hp j _ _
          (sub_nat_rel_canonical tR))
        (g (prop_to_sprop _ _ VALID HvR) schedL
          (prop_to_sprop _ _ (fpi_jobs_come_from_related schedR schedL Hs) HfR)
          (prop_to_sprop _ _ (fpi_jobs_must_arrive_related schedR schedL Hs) HmR)
          pL (prop_to_sprop _ _ (fpi_reflexive_related pR pL Hp) HrR) j
          (prop_to_sprop _ _ fpi_uniprocessor_related HuR) (sub_nat_to_imported tR))).
  Qed.
End Inversion.

Section Cat.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hp : forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).
  Variable j : Job.

  Let CPI := cumulative_priority_inversion_correspondence Job PStateR PStateL R arrR arrL Harr
    schedR schedL Hsched pR pL Hp j.

  Definition src_cumulative_priority_inversion_cat : Prop :=
    ltac:(body_of (fun s : S.statement_cumulative_priority_inversion_cat => s Job PStateR arrR schedR pR j)).
  Definition tgt_cumulative_priority_inversion_cat : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Inversion_cumulative_priority_inversion_cat
      Job dJ PStateL arrL schedL pL j)).
  Theorem cumulative_priority_inversion_cat_correspondence :
    PropSPropRel src_cumulative_priority_inversion_cat tgt_cumulative_priority_inversion_cat.
  Proof.
    apply ar_forall_nat_correspondence. intros mR mL Hm.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 Hm)|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hm H2)|].
    exact (sub_nat_eq_correspondence _ _ _ _ (CPI _ _ _ _ H1 H2)
      (svc_target_add_related _ _ _ _ (CPI _ _ _ _ H1 Hm) (CPI _ _ _ _ Hm H2))).
  Qed.
End Cat.
