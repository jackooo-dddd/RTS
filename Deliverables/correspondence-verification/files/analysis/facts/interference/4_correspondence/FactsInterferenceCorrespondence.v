From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsInterferenceSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsInterference ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  ServiceOfJobsCorrespondence InterferenceCorrespondence.

Module I := ImportedFactsInterference.
Module S := FactsInterferenceSemanticSource.FactsInterferenceSemanticSource.
Module B := BusyIntervalClassicalSemanticSource.BusyIntervalClassicalSemanticSource.
Module IS := InterferenceSemanticSource.InterferenceSemanticSource.

(** Statement correspondences for [analysis/facts/interference.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading type-level inputs (task and job types, [job_task],
    [job_arrival], [job_cost], processor state); target side: the imported
    Lean theorem types at related inputs ([Lean.eq] on [job_task],
    [ArJobArrivalRel], [SvcJobCostRel], the accepted two-sided
    [SvcProcessorStateRel], extended by the [supply_on] field
    ([FintSupplyRel], exactly as the accepted ideal service-of-jobs
    certificate) for the statements mentioning supply).  Every other binder
    is covered in both directions: arrival sequences and schedules through
    the list / state conversions with their roundtrips, FP and JLFP
    policies pointwise on Booleans; tasks and jobs are identity carriers,
    Nats are covered in both directions.  The interference functions are
    closed by the accepted [InterferenceCorrespondence], the services of
    other higher-or-equal-priority jobs by the accepted
    [ServiceOfJobsCorrespondence]; [JLFP_FP_compatible], [quiet_time],
    [is_idle], the platform properties and the schedule hypotheses are
    related here from the accepted primitive relations.  No source or target
    theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fint_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Lemma fint_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma fint_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma fint_eq_correspondence (T : Type) (x y : T) : PropSPropRel (x = y) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. destruct E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (imported_eq_to_coq_eq _ _ E).
Qed.

Lemma fint_bool_eq_correspondence (bR cR : bool) (bL cL : I.Bool) :
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

Lemma fint_decide_eq_related (T : eqType) (x y : T) :
  ArBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (ar_decidable_eq T x y)).
Proof.
  unfold ar_decidable_eq, ArBoolRel.
  destruct (@eqP T x y); cbn; exact (@Lean.eq_refl _ _).
Qed.

Section Facts.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let StateR : Type := @prosa.behavior.schedule.State Job PStateR.
  Let StateL : Type := I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PStateL.
  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Let ArrR := prosa.behavior.arrival_sequence.arrival_sequence Job.
  Let ArrL := I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.

  (** *** Covers for inner binders *)

  Definition fint_schedule_to_target (schedR : SchedR) : SchedL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq tL)).

  Definition fint_schedule_to_source (schedL : SchedL) : SchedR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)).

  Lemma fint_schedule_to_target_rel schedR :
    SvcScheduleRel Job PStateR PStateL R schedR (fint_schedule_to_target schedR).
  Proof.
    intros tR tL Ht. unfold fint_schedule_to_target.
    rewrite (fint_nat_input _ _ Ht).
    exact (svc_ps_state_rel_canonical Job PStateR PStateL R (schedR tR)).
  Qed.

  Lemma fint_schedule_to_source_rel schedL :
    SvcScheduleRel Job PStateR PStateL R (fint_schedule_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. unfold fint_schedule_to_source.
    exact (fint_lean_transport
      (fun sL => svc_ps_state_rel Job PStateR PStateL R
        (svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR))) sL)
      _ _ (sub_imported_eq_congr schedL _ _ Ht)
      (svc_ps_state_rel_surjective Job PStateR PStateL R _)).
  Qed.

  Let cover_schedule :=
    fint_forall_cover_sprop _ _ (SvcScheduleRel Job PStateR PStateL R)
      fint_schedule_to_target fint_schedule_to_source
      fint_schedule_to_target_rel fint_schedule_to_source_rel.

  Definition fint_arrival_sequence_to_source (arrL : ArrL) : ArrR :=
    fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

  Lemma fint_arrival_sequence_to_source_rel (arrL : ArrL) :
    ArArrivalSequenceRel Job (fint_arrival_sequence_to_source arrL) arrL.
  Proof.
    intros tR tL Ht. unfold ArListRel, fint_arrival_sequence_to_source.
    exact (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _)
      (sub_imported_eq_congr arrL _ _ Ht)).
  Qed.

  Let cover_arr :=
    fint_forall_cover_sprop _ _ (ArArrivalSequenceRel Job)
      (ar_arrival_sequence_to_imported Job) fint_arrival_sequence_to_source
      (ar_arrival_sequence_canonical Job) fint_arrival_sequence_to_source_rel.

  Definition fint_jlfp_to_target (pR : prosa.model.priority.definitions.JLFP_policy Job) :
      I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ :=
    I.Prosa_Model_Priority_Definitions_JLFP_policy_mk Job dJ
      (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_job Job pR x y)).

  Definition fint_jlfp_to_source (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ) :
      prosa.model.priority.definitions.JLFP_policy Job :=
    fun x y => ar_bool_to_rocq (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Lemma fint_jlfp_to_target_rel pR : SojJLFPRel Job pR (fint_jlfp_to_target pR).
  Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

  Lemma fint_jlfp_to_source_rel pL : SojJLFPRel Job (fint_jlfp_to_source pL) pL.
  Proof. intros x y. exact (ar_bool_target_roundtrip _). Qed.

  Let cover_jlfp :=
    fint_forall_cover_sprop _ _ (SojJLFPRel Job) fint_jlfp_to_target fint_jlfp_to_source
      fint_jlfp_to_target_rel fint_jlfp_to_source_rel.

  Definition FintFPRel (fpR : prosa.model.priority.definitions.FP_policy Task)
      (fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT) : SProp :=
    forall x y : Task,
      ArBoolRel (@prosa.model.priority.definitions.hep_task Task fpR x y)
        (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL x y).

  Definition fint_fp_to_target (fpR : prosa.model.priority.definitions.FP_policy Task) :
      I.Prosa_Model_Priority_Definitions_FP_policy Task dT :=
    I.Prosa_Model_Priority_Definitions_FP_policy_mk Task dT
      (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_task Task fpR x y)).

  Definition fint_fp_to_source (fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT) :
      prosa.model.priority.definitions.FP_policy Task :=
    fun x y => ar_bool_to_rocq (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL x y).

  Lemma fint_fp_to_target_rel fpR : FintFPRel fpR (fint_fp_to_target fpR).
  Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

  Lemma fint_fp_to_source_rel fpL : FintFPRel (fint_fp_to_source fpL) fpL.
  Proof. intros x y. exact (ar_bool_target_roundtrip _). Qed.

  Let cover_fp :=
    fint_forall_cover_sprop _ _ FintFPRel fint_fp_to_target fint_fp_to_source
      fint_fp_to_target_rel fint_fp_to_source_rel.

  Let cover_state :=
    fint_forall_cover_sprop _ _ (svc_ps_state_rel Job PStateR PStateL R)
      (svc_ps_state_to_target Job PStateR PStateL R) (svc_ps_state_to_source Job PStateR PStateL R)
      (svc_ps_state_rel_canonical Job PStateR PStateL R) (svc_ps_state_rel_surjective Job PStateR PStateL R).

  (** *** Tasks of jobs and priority compatibility *)

  Lemma fint_job_of_task_related (tsk : Task) (j : Job) :
    ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof.
    unfold prosa.model.task.concept.job_of_task.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    refine (fint_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
        (I.Decidable_decide (Lean.eq v tsk) (dT v tsk))) _ _ (Hjt j) _).
    exact (fint_decide_eq_related Task _ tsk).
  Qed.

  Lemma fint_hep_task_jobs fpR fpL (Hfp : FintFPRel fpR fpL) (j1 j2 : Job) :
    ArBoolRel (@prosa.model.priority.definitions.hep_task Task fpR
        (@prosa.model.task.concept.job_task Job Task jtR j1)
        (@prosa.model.task.concept.job_task Job Task jtR j2))
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j1)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j2)).
  Proof.
    unfold ArBoolRel.
    exact (sub_imported_eq_trans _ _ _ (Hfp _ _)
      (sub_imported_eq_congr2 (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL)
        _ _ _ _ (Hjt j1) (Hjt j2))).
  Qed.

  Lemma fint_compatible_related fpR fpL (Hfp : FintFPRel fpR fpL) pR pL (Hp : SojJLFPRel Job pR pL) :
    PropSPropRel (@prosa.analysis.definitions.priority.classes.JLFP_FP_compatible Task Job jtR pR fpR)
      (I.Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible Task dT Job dJ jtL pL fpL).
  Proof.
    unfold prosa.analysis.definitions.priority.classes.JLFP_FP_compatible.
    cbn [I.Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible].
    apply ar_and_correspondence.
    - apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp j1 j2))|].
      exact (ar_bool_truth_correspondence _ _ (fint_hep_task_jobs fpR fpL Hfp j1 j2)).
    - apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (if_hp_task_jobs Task Job jtR jtL Hjt fpR fpL Hfp j1 j2))|].
      exact (ar_bool_truth_correspondence _ _ (Hp j1 j2)).
  Qed.

  (** *** Platform properties *)

  Lemma fint_unit_service_related :
    PropSPropRel (@prosa.model.processor.platform_properties.unit_service_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.unit_service_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model].
    apply ar_forall_identity_correspondence. intro j'.
    apply cover_state. intros sR sL Hs.
    exact (sub_nat_le_correspondence _ _ _ _ (svc_service_in_related Job PStateR PStateL R j' sR sL Hs)
      (sub_nat_rel_canonical 1)).
  Qed.

  Lemma fint_uniprocessor_related :
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
    exact (fint_eq_correspondence Job j1 j2).
  Qed.

  (** *** Schedule hypotheses and observations *)

  Section Sched.
    Variable schedR : SchedR.
    Variable schedL : SchedL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Let SCHED := pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched.
    Let SERVICE := pp_service_related Job PStateR PStateL R schedR schedL Hsched.

    Lemma fint_jobs_must_arrive_related :
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

    Lemma fint_completed_jobs_dont_execute_related :
      PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PStateR schedR costR)
        (I.Prosa_Behavior_Ready_completed_jobs_dont_execute Job dJ PStateL schedL costL).
    Proof.
      unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (SCHED j _ _ Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _ (SERVICE j _ _ Ht) (Hcost j)).
    Qed.

    Lemma fint_receives_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      ArBoolRel (@prosa.behavior.service.receives_service_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_receives_service_at Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.receives_service_at.
      cbn [I.Prosa_Behavior_Service_receives_service_at].
      exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O)
        (pp_service_at_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht)).
    Qed.

    Section Arr.
      Variable arrR : ArrR.
      Variable arrL : ArrL.
      Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

      Lemma fint_jobs_come_from_related :
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

      Lemma fint_scheduled_jobs_at_related (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        ArListRel (@prosa.model.schedule.scheduled.scheduled_jobs_at Job PStateR arrR schedR tR)
          (I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job dJ PStateL arrL schedL tL).
      Proof.
        intro Ht. unfold prosa.model.schedule.scheduled.scheduled_jobs_at.
        cbn [I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at].
        apply ar_filter_related.
        - intro j. exact (SCHED j tR tL Ht).
        - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr _ _ Ht).
      Qed.

      Lemma fint_is_idle_related (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        ArBoolRel (@prosa.model.schedule.scheduled.is_idle Job PStateR arrR schedR tR)
          (I.Prosa_Model_Schedule_Scheduled_is_idle Job dJ PStateL arrL schedL tL).
      Proof.
        intro Ht. unfold prosa.model.schedule.scheduled.is_idle.
        cbn [I.Prosa_Model_Schedule_Scheduled_is_idle].
        have Hs := fint_scheduled_jobs_at_related tR tL Ht.
        refine (fint_lean_transport (fun l => ArBoolRel _ (I.List_isEmpty Job l)) _ _ Hs _).
        destruct (@prosa.model.schedule.scheduled.scheduled_jobs_at Job PStateR arrR schedR tR);
          exact (@Lean.eq_refl _ _).
      Qed.

      Section Policy.
        Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
        Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
        Hypothesis Hp : SojJLFPRel Job pR pL.

        Let COMPLETED := pp_completed_by_related Job costR costL Hcost PStateR PStateL R schedR schedL Hsched.

        Lemma fint_quiet_time_related (j : Job) (tR : nat) (tL : Lean.Nat) :
          SubNatRel tR tL ->
          PropSPropRel (@B.quiet_time Job jaR costR PStateR arrR schedR pR j tR)
            (I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time
              Job dJ jaL costL PStateL arrL schedL pL j tL).
        Proof.
          intro Ht. unfold B.quiet_time.
          cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time].
          apply ar_forall_identity_correspondence. intro j_hp.
          apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j_hp Harr)|].
          apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp j_hp j))|].
          apply ar_imp_correspondence;
            [exact (ar_bool_truth_correspondence _ _
              (arrived_before_correspondence_certificate Job jaR jaL j_hp Hja tR tL Ht))|].
          exact (ar_bool_truth_correspondence _ _ (COMPLETED j_hp tR tL Ht)).
        Qed.
      End Policy.
    End Arr.
  End Sched.

  (** *** Supply (the [supply_on] field of the processor-state relation) *)

  Definition FintSupplyRel : SProp :=
    forall (sR : StateR) (sL : StateL) (cR : @prosa.behavior.schedule.Core Job PStateR),
      svc_ps_state_rel Job PStateR PStateL R sR sL ->
      SubNatRel (@prosa.behavior.schedule.supply_on Job PStateR sR cR)
        (I.Prosa_Behavior_Schedule_ProcessorState_supply_on Job dJ PStateL sL
          (svc_ps_core_to_target Job PStateR PStateL R cR)).

  Section Supply.
    Hypothesis Hsupply : FintSupplyRel.

    Lemma fint_supply_in_related (sR : StateR) (sL : StateL) :
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

    Lemma fint_supply_at_related schedR schedL
        (Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.model.processor.supply.supply_at Job PStateR schedR tR)
        (I.Prosa_Model_Processor_Supply_supply_at Job dJ PStateL schedL tL).
    Proof.
      intro Ht. unfold prosa.model.processor.supply.supply_at.
      cbn [I.Prosa_Model_Processor_Supply_supply_at].
      exact (fint_supply_in_related _ _ (Hsched tR tL Ht)).
    Qed.

    Lemma fint_has_supply_related schedR schedL
        (Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      ArBoolRel (@prosa.model.processor.supply.has_supply Job PStateR schedR tR)
        (I.Prosa_Model_Processor_Supply_has_supply Job dJ PStateL schedL tL).
    Proof.
      intro Ht. unfold prosa.model.processor.supply.has_supply.
      cbn [I.Prosa_Model_Processor_Supply_has_supply].
      exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O)
        (fint_supply_at_related schedR schedL Hsched tR tL Ht)).
    Qed.

    Lemma fint_fully_consuming_related :
      PropSPropRel (@prosa.model.processor.platform_properties.fully_consuming_proc_model Job PStateR)
        (I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job dJ PStateL).
    Proof.
      unfold prosa.model.processor.platform_properties.fully_consuming_proc_model.
      cbn [I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model].
      apply ar_forall_identity_correspondence. intro j.
      apply cover_schedule. intros schedR schedL Hsched.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht))|].
      exact (sub_nat_eq_correspondence _ _ _ _
        (pp_service_at_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht)
        (fint_supply_at_related schedR schedL Hsched tR tL Ht)).
    Qed.
  End Supply.

  (** *** Relations of the interference functions at this artifact *)

  Let AHEP schedR schedL Hsched arrR arrL Harr pR pL Hp :=
    another_hep_job_interference_correspondence Job PStateR PStateL R schedR schedL Hsched
      arrR arrL Harr pR pL Hp.
  Let ATHEP schedR schedL Hsched arrR arrL Harr pR pL Hp :=
    another_task_hep_job_interference_correspondence Task Job jtR jtL Hjt PStateR PStateL R
      schedR schedL Hsched arrR arrL Harr pR pL Hp.

  Ltac fint_not_truth H :=
    exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ H)).

  (** *** Statements with a leading FP policy *)

  Definition src_another_task_hep_job_split_hp_ep : Prop :=
    ltac:(body_of (fun s : S.statement_another_task_hep_job_split_hp_ep => s Task Job jtR)).
  Definition tgt_another_task_hep_job_split_hp_ep : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_another_task_hep_job_split_hp_ep
      Task dT Job dJ jtL)).
  Theorem another_task_hep_job_split_hp_ep_correspondence :
    PropSPropRel src_another_task_hep_job_split_hp_ep tgt_another_task_hep_job_split_hp_ep.
  Proof.
    apply cover_fp. intros fpR fpL Hfp.
    apply cover_jlfp. intros pR pL Hp.
    apply ar_imp_correspondence; [exact (fint_compatible_related fpR fpL Hfp pR pL Hp)|].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply fint_bool_eq_correspondence.
    - exact (if_another_task_hep_job_related Task Job jtR jtL Hjt pR pL Hp j1 j2).
    - exact (if_bool_or_related _ _ _ _
        (hp_task_hep_job_correspondence Task Job jtR jtL Hjt fpR fpL Hfp pR pL Hp j1 j2)
        (other_ep_task_hep_job_correspondence Task Job jtR jtL Hjt fpR fpL Hfp pR pL Hp j1 j2)).
  Qed.

  Definition src_hep_interference_another_task_split : Prop :=
    ltac:(body_of (fun s : S.statement_hep_interference_another_task_split => s Task Job jtR PStateR)).
  Definition tgt_hep_interference_another_task_split : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_hep_interference_another_task_split
      Task dT Job dJ jtL PStateL)).
  Theorem hep_interference_another_task_split_correspondence :
    PropSPropRel src_hep_interference_another_task_split tgt_hep_interference_another_task_split.
  Proof.
    apply cover_arr. intros arrR arrL Harr.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_fp. intros fpR fpL Hfp.
    apply cover_jlfp. intros pR pL Hp.
    apply ar_imp_correspondence; [exact (fint_compatible_related fpR fpL Hfp pR pL Hp)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply fint_bool_eq_correspondence.
    - exact (ATHEP schedR schedL Hsched arrR arrL Harr pR pL Hp j tR tL Ht).
    - exact (if_bool_or_related _ _ _ _
        (hep_job_from_hp_task_interference_correspondence Task Job jtR jtL Hjt PStateR PStateL R
          schedR schedL Hsched arrR arrL Harr fpR fpL Hfp pR pL Hp j tR tL Ht)
        (hep_job_from_other_ep_task_interference_correspondence Task Job jtR jtL Hjt PStateR PStateL R
          schedR schedL Hsched arrR arrL Harr fpR fpL Hfp pR pL Hp j tR tL Ht)).
  Qed.

  Definition src_cumulative_hep_interference_split_tasks_new : Prop :=
    ltac:(body_of (fun s : S.statement_cumulative_hep_interference_split_tasks_new => s Task Job jtR PStateR)).
  Definition tgt_cumulative_hep_interference_split_tasks_new : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_cumulative_hep_interference_split_tasks_new
      Task dT Job dJ jtL PStateL)).
  Theorem cumulative_hep_interference_split_tasks_new_correspondence :
    PropSPropRel src_cumulative_hep_interference_split_tasks_new
      tgt_cumulative_hep_interference_split_tasks_new.
  Proof.
    apply cover_arr. intros arrR arrL Harr.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_fp. intros fpR fpL Hfp.
    apply cover_jlfp. intros pR pL Hp.
    apply ar_imp_correspondence; [exact (fint_compatible_related fpR fpL Hfp pR pL Hp)|].
    apply ar_imp_correspondence; [exact fint_uniprocessor_related|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    have H2 := svc_target_add_related _ _ _ _ H1 Hd.
    apply sub_nat_eq_correspondence.
    - exact (cumulative_another_task_hep_job_interference_correspondence Task Job jtR jtL Hjt
        PStateR PStateL R schedR schedL Hsched arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2).
    - apply svc_target_add_related.
      + exact (cumulative_interference_from_hep_jobs_from_hp_tasks_correspondence Task Job jtR jtL Hjt
          PStateR PStateL R schedR schedL Hsched arrR arrL Harr fpR fpL Hfp pR pL Hp j _ _ _ _ H1 H2).
      + exact (cumulative_interference_from_hep_jobs_from_other_ep_tasks_correspondence Task Job jtR jtL Hjt
          PStateR PStateL R schedR schedL Hsched arrR arrL Harr fpR fpL Hfp pR pL Hp j _ _ _ _ H1 H2).
  Qed.

  (** *** Supply-dependent statements *)

  Section SupplyStatements.
    Hypothesis Hsupply : FintSupplyRel.

    Let HAS := fint_has_supply_related Hsupply.
    Let CONSUMING := fint_fully_consuming_related Hsupply.

    Definition src_no_hep_job_interference_without_supply : Prop :=
      ltac:(body_of (fun s : S.statement_no_hep_job_interference_without_supply => s Job PStateR)).
    Definition tgt_no_hep_job_interference_without_supply : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_no_hep_job_interference_without_supply
        Job dJ PStateL)).
    Theorem no_hep_job_interference_without_supply_correspondence :
      PropSPropRel src_no_hep_job_interference_without_supply
        tgt_no_hep_job_interference_without_supply.
    Proof.
      apply cover_arr. intros arrR arrL Harr.
      apply cover_schedule. intros schedR schedL Hsched.
      apply cover_jlfp. intros pR pL Hp.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [fint_not_truth (HAS schedR schedL Hsched tR tL Ht)|].
      apply ar_forall_identity_correspondence. intro j.
      fint_not_truth (AHEP schedR schedL Hsched arrR arrL Harr pR pL Hp j tR tL Ht).
    Qed.

    Definition src_no_hep_task_interference_without_supply : Prop :=
      ltac:(body_of (fun s : S.statement_no_hep_task_interference_without_supply => s Task Job jtR PStateR)).
    Definition tgt_no_hep_task_interference_without_supply : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_no_hep_task_interference_without_supply
        Task dT Job dJ jtL PStateL)).
    Theorem no_hep_task_interference_without_supply_correspondence :
      PropSPropRel src_no_hep_task_interference_without_supply
        tgt_no_hep_task_interference_without_supply.
    Proof.
      apply cover_arr. intros arrR arrL Harr.
      apply cover_schedule. intros schedR schedL Hsched.
      apply cover_jlfp. intros pR pL Hp.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [fint_not_truth (HAS schedR schedL Hsched tR tL Ht)|].
      apply ar_forall_identity_correspondence. intro j.
      fint_not_truth (ATHEP schedR schedL Hsched arrR arrL Harr pR pL Hp j tR tL Ht).
    Qed.

    Ltac fint_supply_prefix :=
      apply ar_imp_correspondence; [exact fint_uniprocessor_related|];
      apply ar_imp_correspondence; [exact CONSUMING|];
      apply cover_arr; let arrR := fresh "arrR" in let arrL := fresh "arrL" in
        let Harr := fresh "Harr" in intros arrR arrL Harr;
      apply ar_imp_correspondence;
        [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|];
      apply cover_schedule; let schedR := fresh "schedR" in let schedL := fresh "schedL" in
        let Hsched := fresh "Hsched" in intros schedR schedL Hsched;
      apply ar_imp_correspondence; [exact (fint_jobs_come_from_related schedR schedL Hsched arrR arrL Harr)|];
      apply ar_imp_correspondence; [exact (fint_jobs_must_arrive_related schedR schedL Hsched)|].

    Definition src_interference_ahep_def : Prop :=
      ltac:(body_of (fun s : S.statement_interference_ahep_def => s Job jaR PStateR)).
    Definition tgt_interference_ahep_def : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_interference_ahep_def Job dJ jaL PStateL)).
    Theorem interference_ahep_def_correspondence :
      PropSPropRel src_interference_ahep_def tgt_interference_ahep_def.
    Proof.
      fint_supply_prefix.
      apply cover_jlfp. intros pR pL Hp.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (HAS schedR schedL Hsched tR tL Ht))|].
      apply ar_forall_identity_correspondence. intro j'.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j' tR tL Ht))|].
      exact (fint_bool_eq_correspondence _ _ _ _
        (AHEP schedR schedL Hsched arrR arrL Harr pR pL Hp j tR tL Ht)
        (if_another_hep_job_related Job pR pL Hp j' j)).
    Qed.

    Definition src_interference_athep_def : Prop :=
      ltac:(body_of (fun s : S.statement_interference_athep_def => s Task Job jtR jaR PStateR)).
    Definition tgt_interference_athep_def : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_interference_athep_def
        Task dT Job dJ jtL jaL PStateL)).
    Theorem interference_athep_def_correspondence :
      PropSPropRel src_interference_athep_def tgt_interference_athep_def.
    Proof.
      fint_supply_prefix.
      apply cover_jlfp. intros pR pL Hp.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (HAS schedR schedL Hsched tR tL Ht))|].
      apply ar_forall_identity_correspondence. intro j'.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j' tR tL Ht))|].
      exact (fint_bool_eq_correspondence _ _ _ _
        (ATHEP schedR schedL Hsched arrR arrL Harr pR pL Hp j tR tL Ht)
        (if_another_task_hep_job_related Task Job jtR jtL Hjt pR pL Hp j' j)).
    Qed.

    Definition src_no_ahep_interference_when_served : Prop :=
      ltac:(body_of (fun s : S.statement_no_ahep_interference_when_served => s Job jaR PStateR)).
    Definition tgt_no_ahep_interference_when_served : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_no_ahep_interference_when_served
        Job dJ jaL PStateL)).
    Theorem no_ahep_interference_when_served_correspondence :
      PropSPropRel src_no_ahep_interference_when_served tgt_no_ahep_interference_when_served.
    Proof.
      fint_supply_prefix.
      apply cover_jlfp. intros pR pL Hp.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (HAS schedR schedL Hsched tR tL Ht))|].
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (fint_receives_service_at_related schedR schedL Hsched j tR tL Ht))|].
      fint_not_truth (AHEP schedR schedL Hsched arrR arrL Harr pR pL Hp j tR tL Ht).
    Qed.

    Definition src_athep_interference_iff : Prop :=
      ltac:(body_of (fun s : S.statement_athep_interference_iff => s Task Job jtR jaR PStateR)).
    Definition tgt_athep_interference_iff : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_athep_interference_iff
        Task dT Job dJ jtL jaL PStateL)).
    Theorem athep_interference_iff_correspondence :
      PropSPropRel src_athep_interference_iff tgt_athep_interference_iff.
    Proof.
      fint_supply_prefix.
      apply ar_forall_identity_correspondence. intro tsk.
      apply cover_jlfp. intros pR pL Hp.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (fint_job_of_task_related tsk j))|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (HAS schedR schedL Hsched tR tL Ht))|].
      apply ar_forall_identity_correspondence. intro j'.
      apply ar_imp_correspondence; [fint_not_truth (fint_job_of_task_related tsk j')|].
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j' tR tL Ht))|].
      exact (fint_bool_eq_correspondence _ _ _ _
        (ATHEP schedR schedL Hsched arrR arrL Harr pR pL Hp j tR tL Ht) (Hp j' j)).
    Qed.

    Definition src_athep_interference_if : Prop :=
      ltac:(body_of (fun s : S.statement_athep_interference_if => s Task Job jtR jaR PStateR)).
    Definition tgt_athep_interference_if : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_athep_interference_if
        Task dT Job dJ jtL jaL PStateL)).
    Theorem athep_interference_if_correspondence :
      PropSPropRel src_athep_interference_if tgt_athep_interference_if.
    Proof.
      fint_supply_prefix.
      apply ar_forall_identity_correspondence. intro tsk.
      apply cover_jlfp. intros pR pL Hp.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (fint_job_of_task_related tsk j))|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (HAS schedR schedL Hsched tR tL Ht))|].
      apply ar_forall_identity_correspondence. intro j'.
      apply ar_imp_correspondence; [fint_not_truth (fint_job_of_task_related tsk j')|].
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j' tR tL Ht))|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp j' j))|].
      exact (ar_bool_truth_correspondence _ _
        (ATHEP schedR schedL Hsched arrR arrL Harr pR pL Hp j tR tL Ht)).
    Qed.
  End SupplyStatements.

  (** *** Idle schedules *)

  Ltac fint_idle_prefix :=
    apply cover_arr; let arrR := fresh "arrR" in let arrL := fresh "arrL" in
      let Harr := fresh "Harr" in intros arrR arrL Harr;
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|];
    apply cover_schedule; let schedR := fresh "schedR" in let schedL := fresh "schedL" in
      let Hsched := fresh "Hsched" in intros schedR schedL Hsched;
    apply ar_imp_correspondence; [exact (fint_jobs_come_from_related schedR schedL Hsched arrR arrL Harr)|];
    apply ar_imp_correspondence; [exact (fint_jobs_must_arrive_related schedR schedL Hsched)|];
    apply cover_jlfp; let pR := fresh "pR" in let pL := fresh "pL" in
      let Hp := fresh "Hp" in intros pR pL Hp;
    apply ar_forall_nat_correspondence; let tR := fresh "tR" in let tL := fresh "tL" in
      let Ht := fresh "Ht" in intros tR tL Ht;
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (fint_is_idle_related schedR schedL Hsched arrR arrL Harr tR tL Ht))|];
    apply ar_forall_identity_correspondence; let j := fresh "j" in intro j.

  Definition src_no_hep_job_interference_when_idle : Prop :=
    ltac:(body_of (fun s : S.statement_no_hep_job_interference_when_idle => s Job jaR PStateR)).
  Definition tgt_no_hep_job_interference_when_idle : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_no_hep_job_interference_when_idle
      Job dJ jaL PStateL)).
  Theorem no_hep_job_interference_when_idle_correspondence :
    PropSPropRel src_no_hep_job_interference_when_idle tgt_no_hep_job_interference_when_idle.
  Proof.
    fint_idle_prefix.
    fint_not_truth (AHEP schedR schedL Hsched arrR arrL Harr pR pL Hp j tR tL Ht).
  Qed.

  Definition src_no_hep_task_interference_when_idle : Prop :=
    ltac:(body_of (fun s : S.statement_no_hep_task_interference_when_idle => s Task Job jtR jaR PStateR)).
  Definition tgt_no_hep_task_interference_when_idle : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_no_hep_task_interference_when_idle
      Task dT Job dJ jtL jaL PStateL)).
  Theorem no_hep_task_interference_when_idle_correspondence :
    PropSPropRel src_no_hep_task_interference_when_idle tgt_no_hep_task_interference_when_idle.
  Proof.
    fint_idle_prefix.
    fint_not_truth (ATHEP schedR schedL Hsched arrR arrL Harr pR pL Hp j tR tL Ht).
  Qed.

  (** *** Uniprocessor statements without supply *)

  Definition src_no_ahep_interference_when_scheduled : Prop :=
    ltac:(body_of (fun s : S.statement_no_ahep_interference_when_scheduled => s Job PStateR)).
  Definition tgt_no_ahep_interference_when_scheduled : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_no_ahep_interference_when_scheduled
      Job dJ PStateL)).
  Theorem no_ahep_interference_when_scheduled_correspondence :
    PropSPropRel src_no_ahep_interference_when_scheduled tgt_no_ahep_interference_when_scheduled.
  Proof.
    apply ar_imp_correspondence; [exact fint_uniprocessor_related|].
    apply cover_arr. intros arrR arrL Harr.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_jlfp. intros pR pL Hp.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _
        (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht))|].
    fint_not_truth (AHEP schedR schedL Hsched arrR arrL Harr pR pL Hp j tR tL Ht).
  Qed.

  Definition src_no_athep_interference_when_scheduled : Prop :=
    ltac:(body_of (fun s : S.statement_no_athep_interference_when_scheduled => s Task Job jtR PStateR)).
  Definition tgt_no_athep_interference_when_scheduled : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_no_athep_interference_when_scheduled
      Task dT Job dJ jtL PStateL)).
  Theorem no_athep_interference_when_scheduled_correspondence :
    PropSPropRel src_no_athep_interference_when_scheduled tgt_no_athep_interference_when_scheduled.
  Proof.
    apply ar_imp_correspondence; [exact fint_uniprocessor_related|].
    apply cover_arr. intros arrR arrL Harr.
    apply cover_schedule. intros schedR schedL Hsched.
    apply ar_forall_identity_correspondence. intro tsk.
    apply cover_jlfp. intros pR pL Hp.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (fint_job_of_task_related tsk j))|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (fint_job_of_task_related tsk j'))|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _
        (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j' tR tL Ht))|].
    fint_not_truth (ATHEP schedR schedL Hsched arrR arrL Harr pR pL Hp j tR tL Ht).
  Qed.

  Definition src_no_ahep_interference_when_scheduled_lp : Prop :=
    ltac:(body_of (fun s : S.statement_no_ahep_interference_when_scheduled_lp => s Job PStateR)).
  Definition tgt_no_ahep_interference_when_scheduled_lp : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_no_ahep_interference_when_scheduled_lp
      Job dJ PStateL)).
  Theorem no_ahep_interference_when_scheduled_lp_correspondence :
    PropSPropRel src_no_ahep_interference_when_scheduled_lp
      tgt_no_ahep_interference_when_scheduled_lp.
  Proof.
    apply ar_imp_correspondence; [exact fint_uniprocessor_related|].
    apply cover_arr. intros arrR arrL Harr.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_jlfp. intros pR pL Hp.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _
        (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j' tR tL Ht))|].
    apply ar_imp_correspondence; [fint_not_truth (Hp j' j)|].
    fint_not_truth (AHEP schedR schedL Hsched arrR arrL Harr pR pL Hp j tR tL Ht).
  Qed.

  (** *** Service equivalences from a quiet time *)

  Ltac fint_service_prefix :=
    apply ar_imp_correspondence; [exact fint_uniprocessor_related|];
    apply cover_arr; let arrR := fresh "arrR" in let arrL := fresh "arrL" in
      let Harr := fresh "Harr" in intros arrR arrL Harr;
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|];
    apply cover_schedule; let schedR := fresh "schedR" in let schedL := fresh "schedL" in
      let Hsched := fresh "Hsched" in intros schedR schedL Hsched;
    apply ar_imp_correspondence; [exact (fint_jobs_must_arrive_related schedR schedL Hsched)|];
    apply ar_imp_correspondence; [exact (fint_completed_jobs_dont_execute_related schedR schedL Hsched)|];
    apply cover_jlfp; let pR := fresh "pR" in let pL := fresh "pL" in
      let Hp := fresh "Hp" in intros pR pL Hp;
    apply ar_imp_correspondence; [exact fint_unit_service_related|];
    apply ar_forall_identity_correspondence; let j := fresh "j" in intro j;
    apply ar_forall_nat_correspondence; let t1R := fresh "t1R" in let t1L := fresh "t1L" in
      let H1 := fresh "H1" in intros t1R t1L H1;
    apply ar_forall_nat_correspondence; let tR := fresh "tR" in let tL := fresh "tL" in
      let Ht := fresh "Ht" in intros tR tL Ht;
    apply ar_imp_correspondence;
      [exact (fint_quiet_time_related schedR schedL Hsched arrR arrL Harr pR pL Hp j t1R t1L H1)|].

  Definition src_cumulative_i_ohep_eq_service_of_ohep : Prop :=
    ltac:(body_of (fun s : S.statement_cumulative_i_ohep_eq_service_of_ohep => s Job jaR costR PStateR)).
  Definition tgt_cumulative_i_ohep_eq_service_of_ohep : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_cumulative_i_ohep_eq_service_of_ohep
      Job dJ jaL costL PStateL)).
  Theorem cumulative_i_ohep_eq_service_of_ohep_correspondence :
    PropSPropRel src_cumulative_i_ohep_eq_service_of_ohep tgt_cumulative_i_ohep_eq_service_of_ohep.
  Proof.
    fint_service_prefix.
    apply sub_nat_eq_correspondence.
    - exact (cumulative_another_hep_job_interference_correspondence Job PStateR PStateL R
        schedR schedL Hsched arrR arrL Harr pR pL Hp j _ _ _ _ H1 Ht).
    - exact (service_of_other_hep_jobs_correspondence Job PStateR PStateL R schedR schedL Hsched
        pR pL Hp arrR arrL Harr j _ _ _ _ H1 Ht).
  Qed.

  Definition src_cumulative_i_thep_eq_service_of_othep : Prop :=
    ltac:(body_of (fun s : S.statement_cumulative_i_thep_eq_service_of_othep =>
      s Task Job jtR jaR costR PStateR)).
  Definition tgt_cumulative_i_thep_eq_service_of_othep : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Interference_cumulative_i_thep_eq_service_of_othep
      Task dT Job dJ jtL jaL costL PStateL)).
  Theorem cumulative_i_thep_eq_service_of_othep_correspondence :
    PropSPropRel src_cumulative_i_thep_eq_service_of_othep tgt_cumulative_i_thep_eq_service_of_othep.
  Proof.
    fint_service_prefix.
    apply sub_nat_eq_correspondence.
    - exact (cumulative_another_task_hep_job_interference_correspondence Task Job jtR jtL Hjt
        PStateR PStateL R schedR schedL Hsched arrR arrL Harr pR pL Hp j _ _ _ _ H1 Ht).
    - exact (service_of_other_task_hep_jobs_correspondence Job PStateR PStateL R schedR schedL Hsched
        pR pL Hp arrR arrL Harr Task jtR jtL Hjt j _ _ _ _ H1 Ht).
  Qed.
End Facts.
