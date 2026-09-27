From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import IdealAbstractRtaSemanticSource.
From prosa Require Import analysis.abstract.definitions analysis.abstract.search_space model.job.properties
  model.processor.platform_properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdealAbstractRta ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  WorkloadCorrespondence
  AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations
  AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations
  AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums
  AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations
  AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations
  AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers.
From FoundationCertificates Require
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskPreemptionParametersCorrespondence.

Module I := ImportedIdealAbstractRta.
Module S := IdealAbstractRtaSemanticSource.IdealAbstractRtaSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module JSO := FoundationCertificates.JitterSvcScheduleOperations.
Module PPC := FoundationCertificates.PreemptionParameterCorrespondence.
Module TPPC := FoundationCertificates.TaskPreemptionParametersCorrespondence.
Module TPP := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.

(** Statement correspondences for [analysis/abstract/ideal/abstract_rta.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types and classes and the processor
    state type); target side: the imported Lean theorem types.  Inputs:
    processor states by the accepted two-sided [SvcProcessorStateRel] of the
    abstract-definitions family; the preemption-parameter family's relation
    of the same shape is built from it field by field ([iarta_jsvc]), so both
    families' certificates apply to one state relation and to every schedule
    related through it.  [job_arrival], [job_cost], [task_cost] and
    [task_rtct] pointwise by [SubNatRel]; [JobTask] by the accepted
    [AdJobTaskRel]; [JobPreemptable] by the accepted [PpJobPreemptableRel].
    Inputs quantified inside a statement are covered in both directions by
    explicit conversions: processor states (for the platform properties),
    arrival sequences, schedules, task sets, [Interference] and
    [InterferingWorkload], interference-bound functions, tasks and jobs
    (identity), instants and durations.  Preemption-model validity and the
    run-to-completion-threshold validity are related by the accepted
    preemption-parameter certificates; everything else by the accepted
    abstract-definitions and abstract-RTA certificates.  No source or target
    theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section IdealAbstractRta.
  Context (Task Job : eqType).
  Let dT := ad_decidable_eq Task.
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SSO.SvcProcessorStateRel Job PStateR PStateL.
  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.

  (** The preemption-parameter family's state relation, built from [R]. *)
  Definition iarta_jsvc : JSO.SvcProcessorStateRel Job PStateR PStateL := {|
    JSO.svc_ps_state_rel := SSO.svc_ps_state_rel Job PStateR PStateL R;
    JSO.svc_ps_state_to_target := SSO.svc_ps_state_to_target Job PStateR PStateL R;
    JSO.svc_ps_state_to_source := SSO.svc_ps_state_to_source Job PStateR PStateL R;
    JSO.svc_ps_core_to_target := SSO.svc_ps_core_to_target Job PStateR PStateL R;
    JSO.svc_ps_core_to_source := SSO.svc_ps_core_to_source Job PStateR PStateL R;
    JSO.svc_ps_state_source_roundtrip := SSO.svc_ps_state_source_roundtrip Job PStateR PStateL R;
    JSO.svc_ps_state_target_roundtrip := SSO.svc_ps_state_target_roundtrip Job PStateR PStateL R;
    JSO.svc_ps_core_source_roundtrip := SSO.svc_ps_core_source_roundtrip Job PStateR PStateL R;
    JSO.svc_ps_core_target_roundtrip := SSO.svc_ps_core_target_roundtrip Job PStateR PStateL R;
    JSO.svc_ps_state_rel_canonical := SSO.svc_ps_state_rel_canonical Job PStateR PStateL R;
    JSO.svc_ps_state_rel_surjective := SSO.svc_ps_state_rel_surjective Job PStateR PStateL R;
    JSO.svc_ps_core_enumeration_rel := SSO.svc_ps_core_enumeration_rel Job PStateR PStateL R;
    JSO.svc_ps_scheduled_on_rel := SSO.svc_ps_scheduled_on_rel Job PStateR PStateL R;
    JSO.svc_ps_service_on_rel := SSO.svc_ps_service_on_rel Job PStateR PStateL R
  |}.

  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable rtcR : TPP.TaskRunToCompletionThreshold Task.
  Variable rtcL : I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task dT.
  Hypothesis Hrtc : forall tsk : Task,
    SubNatRel (@TPP.task_rtct Task rtcR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task dT rtcL tsk).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : AdJobTaskRel Job Task jtR jtL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).
  Variable jpR : PP.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PPC.PpJobPreemptableRel Job jpR jpL.

  (** *** Covers *)

  Definition iarta_sched_to_target (sR : SchedR) : SchedL :=
    fun tL => SSO.svc_ps_state_to_target Job PStateR PStateL R (sR (sub_nat_to_rocq tL)).
  Definition iarta_sched_to_source (sL : SchedL) : SchedR :=
    fun tR => SSO.svc_ps_state_to_source Job PStateR PStateL R (sL (sub_nat_to_imported tR)).

  Lemma iarta_forall_sched (PR : SchedR -> Prop) (PL : SchedL -> SProp) :
    (forall sR sL, SSO.SvcScheduleRel Job PStateR PStateL R sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    apply (arta_forall_cover _ _ (SSO.SvcScheduleRel Job PStateR PStateL R)
      iarta_sched_to_target iarta_sched_to_source).
    - intros sR tR tL Ht. unfold iarta_sched_to_target. rewrite (arta_nat_input _ _ Ht).
      exact (SSO.svc_ps_state_rel_canonical Job PStateR PStateL R _).
    - intros sL tR tL Ht. destruct Ht.
      exact (SSO.svc_ps_state_rel_surjective Job PStateR PStateL R _).
  Qed.

  Definition iarta_arr_to_source (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ) :
      prosa.behavior.arrival_sequence.arrival_sequence Job :=
    fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

  Lemma iarta_forall_arr (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
      (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ -> SProp) :
    (forall aR aL, ArArrivalSequenceRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) ->
    PropSPropRel (forall a, PR a) (forall a, PL a).
  Proof.
    apply (arta_forall_cover _ _ (ArArrivalSequenceRel Job) (ar_arrival_sequence_to_imported Job)
      iarta_arr_to_source (ar_arrival_sequence_canonical Job)).
    intros arrL tR tL Ht. unfold ArListRel, iarta_arr_to_source.
    refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
    exact (sub_imported_eq_congr arrL _ _ Ht).
  Qed.

  (** *** Platform and schedule properties *)

  Lemma iarta_forall_state (PR : @prosa.behavior.schedule.State Job PStateR -> Prop)
      (PL : I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PStateL -> SProp) :
    (forall sR sL, SSO.svc_ps_state_rel Job PStateR PStateL R sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    exact (arta_forall_cover _ _ (SSO.svc_ps_state_rel Job PStateR PStateL R)
      (SSO.svc_ps_state_to_target Job PStateR PStateL R) (SSO.svc_ps_state_to_source Job PStateR PStateL R)
      (SSO.svc_ps_state_rel_canonical Job PStateR PStateL R)
      (SSO.svc_ps_state_rel_surjective Job PStateR PStateL R) PR PL).
  Qed.

  Lemma iarta_ideal_progress_rel :
    PropSPropRel (@prosa.model.processor.platform_properties.ideal_progress_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.ideal_progress_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model].
    apply ad_forall_identity_correspondence. intro j.
    apply iarta_forall_state. intros sR sL Hs.
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (SSO.svc_scheduled_in_related Job PStateR PStateL R j _ _ Hs))|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O)
      (SSO.svc_service_in_related Job PStateR PStateL R j _ _ Hs)).
  Qed.

  Lemma iarta_unit_service_rel :
    PropSPropRel (@prosa.model.processor.platform_properties.unit_service_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.unit_service_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model].
    apply ad_forall_identity_correspondence. intro j.
    apply iarta_forall_state. intros sR sL Hs.
    exact (sub_nat_le_correspondence _ _ _ _ (SSO.svc_service_in_related Job PStateR PStateL R j _ _ Hs)
      (sub_nat_rel_canonical 1)).
  Qed.

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL.

    Lemma iarta_scheduled_at_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR sR j tR)
        (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL sL j tL).
    Proof.
      unfold prosa.behavior.service.scheduled_at.
      exact (SSO.svc_scheduled_in_related Job PStateR PStateL R j _ _ (Hs tR tL Ht)).
    Qed.

    Lemma iarta_must_arrive_rel :
      PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PStateR sR)
        (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job dJ jaL PStateL sL).
    Proof.
      unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros tR tL Ht.
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (iarta_scheduled_at_related j _ _ Ht))|].
      exact (ad_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
    Qed.

    Lemma iarta_completed_dont_execute_rel :
      PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PStateR sR costR)
        (I.Prosa_Behavior_Ready_completed_jobs_dont_execute Job dJ PStateL sL costL).
    Proof.
      unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros tR tL Ht.
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (iarta_scheduled_at_related j _ _ Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _
        (ad_service_related Job PStateR PStateL R sR sL Hs j tR tL Ht) (Hcost j)).
    Qed.
  End Sched.

  Lemma iarta_np_fun_rel (tsk : Task) :
    ArtaFunRel (fun F _ => F - @TPP.task_rtct Task rtcR tsk)
      (fun F _ => I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat) F
        (I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task dT rtcL tsk)).
  Proof. intros xR xL dR dL Hx _. exact (arta_sub_related _ _ _ _ Hx (Hrtc tsk)). Qed.

  (** *** nonpreemptive_interference_is_bounded *)

  Definition src_nonpreemptive_interference_is_bounded : Prop :=
    ltac:(body_of (fun s : S.statement_nonpreemptive_interference_is_bounded =>
      s Task tcR rtcR Job jtR jaR costR jpR PStateR)).
  Definition tgt_nonpreemptive_interference_is_bounded : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_Ideal_AbstractRta_nonpreemptive_interference_is_bounded
      Task dT tcL rtcL Job dJ jtL jaL costL jpL PStateL)).

  Theorem nonpreemptive_interference_is_bounded_correspondence :
    PropSPropRel src_nonpreemptive_interference_is_bounded tgt_nonpreemptive_interference_is_bounded.
  Proof.
    unfold src_nonpreemptive_interference_is_bounded, tgt_nonpreemptive_interference_is_bounded.
    apply ad_imp_correspondence; [exact iarta_ideal_progress_rel|].
    apply ad_imp_correspondence; [exact iarta_unit_service_rel|].
    apply iarta_forall_arr. intros arrR arrL Harr.
    apply iarta_forall_sched. intros sR sL Hs.
    apply ad_imp_correspondence; [exact (iarta_must_arrive_rel sR sL Hs)|].
    apply ad_imp_correspondence; [exact (iarta_completed_dont_execute_rel sR sL Hs)|].
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    apply ad_imp_correspondence;
      [exact (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL
        iarta_jsvc sR sL Hs arrR arrL Harr)|].
    apply ad_imp_correspondence;
      [exact (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rtcR rtcL Hrtc
        jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk)|].
    apply arta_forall_inter. intros interR interL Hinter.
    apply arta_forall_iw. intros workloadR workloadL Hworkload.
    apply ad_imp_correspondence;
      [exact (arta_wc_rel Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr
        interR interL Hinter workloadR workloadL Hworkload)|].
    apply arta_forall_fun. intros PR PL HP.
    exact (arta_ibfnp_bounded_rel Task Job PStateR PStateL R rtcR rtcL Hrtc jtR jtL Hjt jaR jaL Hja
      costR costL Hcost sR sL Hs arrR arrL Harr interR interL Hinter workloadR workloadL Hworkload
      tsk PR PL HP _ _ (iarta_np_fun_rel tsk)).
  Qed.

  (** *** uniprocessor_response_time_bound_ideal *)

  Definition src_uniprocessor_response_time_bound_ideal : Prop :=
    ltac:(body_of (fun s : S.statement_uniprocessor_response_time_bound_ideal =>
      s Task tcR rtcR Job jtR jaR costR jpR PStateR)).
  Definition tgt_uniprocessor_response_time_bound_ideal : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_Ideal_AbstractRta_uniprocessor_response_time_bound_ideal
      Task dT tcL rtcL Job dJ jtL jaL costL jpL PStateL)).

  Theorem uniprocessor_response_time_bound_ideal_correspondence :
    PropSPropRel src_uniprocessor_response_time_bound_ideal tgt_uniprocessor_response_time_bound_ideal.
  Proof.
    unfold src_uniprocessor_response_time_bound_ideal, tgt_uniprocessor_response_time_bound_ideal.
    apply ad_imp_correspondence; [exact iarta_ideal_progress_rel|].
    apply ad_imp_correspondence; [exact iarta_unit_service_rel|].
    apply iarta_forall_arr. intros arrR arrL Harr.
    apply iarta_forall_sched. intros sR sL Hs.
    apply ad_imp_correspondence; [exact (iarta_must_arrive_rel sR sL Hs)|].
    apply ad_imp_correspondence; [exact (iarta_completed_dont_execute_rel sR sL Hs)|].
    apply ad_imp_correspondence;
      [exact (arta_valid_job_costs_rel Task Job tcR tcL Htc jtR jtL Hjt costR costL Hcost arrR arrL Harr)|].
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    apply ad_imp_correspondence;
      [exact (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL
        iarta_jsvc sR sL Hs arrR arrL Harr)|].
    apply ad_imp_correspondence;
      [exact (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rtcR rtcL Hrtc
        jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk)|].
    apply arta_forall_inter. intros interR interL Hinter.
    apply arta_forall_iw. intros workloadR workloadL Hworkload.
    apply ad_imp_correspondence;
      [exact (arta_wc_rel Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr
        interR interL Hinter workloadR workloadL Hworkload)|].
    apply ad_forall_nat_correspondence. intros LR LL HL.
    apply ad_imp_correspondence;
      [exact (arta_bounded_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL Hcost
        sR sL Hs arrR arrL Harr interR interL Hinter workloadR workloadL Hworkload tsk LR LL HL)|].
    apply arta_forall_fun. intros PR PL HP.
    apply ad_imp_correspondence;
      [exact (arta_ibfp_bounded_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL Hcost
        sR sL Hs arrR arrL Harr interR interL Hinter workloadR workloadL Hworkload tsk PR PL HP)|].
    apply ad_forall_nat_correspondence. intros RR RL HR.
    apply ad_imp_correspondence.
    - apply ad_forall_nat_correspondence. intros AR AL HA.
      apply ad_imp_correspondence; [exact (arta_search_space_rel _ _ _ _ _ _ HP HL HA)|].
      apply ad_exists_nat_correspondence. intros FR FL HF.
      have HAF := arta_add_related _ _ _ _ HA HF.
      apply ad_and_correspondence.
      + exact (sub_nat_le_correspondence _ _ _ _
          (arta_add_related _ _ _ _ (Hrtc tsk) (HP _ _ _ _ HA HAF)) HAF).
      + exact (sub_nat_le_correspondence _ _ _ _
          (arta_add_related _ _ _ _ HF (arta_sub_related _ _ _ _ (Htc tsk) (Hrtc tsk))) HR).
    - exact (arta_response_time_bound_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL
        Hcost sR sL Hs arrR arrL Harr tsk RR RL HR).
  Qed.
End IdealAbstractRta.
