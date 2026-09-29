From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import IbfTaskSemanticSource.
From prosa Require Import analysis.abstract.definitions model.job.properties model.processor.platform_properties
  analysis.definitions.task_schedule model.task.sequentiality model.aggregate.service_of_jobs
  model.aggregate.workload model.task.arrival.curves.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaArmEdfFloatingNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  WorkloadCorrespondence
  AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations
  AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations
  AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums
  AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations
  AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations
  AbstractDefinitionsBusyIntervalHelpers AbstractRtaHelpers IdealAbstractRtaHelpers.
From FoundationCertificates Require
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations TaskScheduleCorrespondence
  CurvesCorrespondence RequestBoundFunctionCorrespondence SequentialityCorrespondence
  ServiceOfJobsCorrespondence PreemptionParameterCorrespondence.

Module I := ImportedRtaArmEdfFloatingNonpreemptive.
Module S := IbfTaskSemanticSource.IbfTaskSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module JSO := FoundationCertificates.JitterSvcScheduleOperations.
Module JNB := FoundationCertificates.JitterSvcNatBoolOperations.
Module TSC := FoundationCertificates.TaskScheduleCorrespondence.
Module CVC := FoundationCertificates.CurvesCorrespondence.
Module RBC := FoundationCertificates.RequestBoundFunctionCorrespondence.
Module SQC := FoundationCertificates.SequentialityCorrespondence.
Module SOJ := FoundationCertificates.ServiceOfJobsCorrespondence.
Module RBS := RequestBoundFunctionSemanticSource.RequestBoundFunctionSemanticSource.

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section IbfTask.
  Context (Task Job : eqType).
  Let dT := ad_decidable_eq Task.
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SSO.SvcProcessorStateRel Job PStateR PStateL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : AdJobTaskRel Job Task jtR jtL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j) (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j) (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).

  Section Defs.
    Variable sR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable sL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Theorem nonself_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      AdBoolRel (@S.nonself Job Task jtR PStateR arrR sR j tR)
        (I.Prosa_Analysis_Abstract_IBF_Task_nonself Job dJ Task dT jtL PStateL arrL sL j tL).
    Proof.
      intro Ht. unfold S.nonself.
      cbn [I.Prosa_Analysis_Abstract_IBF_Task_nonself].
      refine (arta_lean_transport (fun v => AdBoolRel _
        (I.Bool_not (I.Prosa_Analysis_Definitions_TaskSchedule_task_served_at Task dT Job dJ jtL
          PStateL arrL sL v tL))) _ _ (Hjt j) _).
      exact (JNB.svc_bool_not_related _ _
        (TSC.task_served_at_correspondence Task Job jtR jtL Hjt PStateR PStateL R sR sL Hs arrR arrL Harr
          _ tR tL Ht)).
    Qed.

    Lemma ibt_nonself_pred :
      AdBoolPredRel Job (@S.nonself Job Task jtR PStateR arrR sR)
        (I.Prosa_Analysis_Abstract_IBF_Task_nonself Job dJ Task dT jtL PStateL arrL sL).
    Proof. intros j t. exact (nonself_correspondence j t _ (sub_nat_rel_canonical t)). Qed.

    Variable interR : prosa.analysis.abstract.definitions.Interference Job.
    Variable interL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ.
    Hypothesis Hinter : AdInterferenceRel Job interR interL.

    Theorem task_interference_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      AdBoolRel (@S.task_interference Job Task jtR PStateR arrR sR interR j tR)
        (I.Prosa_Analysis_Abstract_IBF_Task_task_interference Job dJ Task dT jtL PStateL arrL sL interL j tL).
    Proof.
      intro Ht. unfold S.task_interference.
      cbn [I.Prosa_Analysis_Abstract_IBF_Task_task_interference].
      exact (cond_interference_correspondence_general Job interR interL _ _ j tR tL Hinter ibt_nonself_pred Ht).
    Qed.

    Theorem cumul_task_interference_correspondence (j : Job) t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@S.cumul_task_interference Job Task jtR PStateR arrR sR interR j t1R t2R)
        (I.Prosa_Analysis_Abstract_IBF_Task_cumul_task_interference Job dJ Task dT jtL PStateL arrL sL interL
          j t1L t2L).
    Proof.
      intros H1 H2. unfold S.cumul_task_interference.
      cbn [I.Prosa_Analysis_Abstract_IBF_Task_cumul_task_interference].
      exact (cumul_cond_interference_correspondence Job interR interL Hinter _ _ ibt_nonself_pred j _ _ _ _ H1 H2).
    Qed.
    Variable wR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
    Variable wL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ.
    Hypothesis Hw : AdInterferingWorkloadRel Job wR wL.

    Lemma ibt_arr_ad : AdArrivalSequenceRel Job arrR arrL.
    Proof. exact Harr. Qed.

    Theorem task_interference_is_bounded_by_correspondence (tsk : Task) IBFR IBFL
        (HIBF : forall xR xL dR dL, SubNatRel xR xL -> SubNatRel dR dL -> SubNatRel (IBFR xR dR) (IBFL xL dL)) :
      PropSPropRel (@S.task_interference_is_bounded_by Job Task jtR jaR costR PStateR arrR sR tsk interR wR IBFR)
        (I.Prosa_Analysis_Abstract_IBF_Task_task_interference_is_bounded_by Job dJ Task dT jtL jaL costL PStateL
          arrL sL tsk interL wL IBFL).
    Proof.
      unfold S.task_interference_is_bounded_by.
      cbn [I.Prosa_Analysis_Abstract_IBF_Task_task_interference_is_bounded_by].
      exact (ad_cond_interference_bounded_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL
        Hcost interR interL Hinter wR wL Hw arrR arrL ibt_arr_ad Task jtR jtL Hjt tsk IBFR IBFL HIBF _ _
        (fun j xR xL Hx => relative_arrival_time_of_job_is_A_correspondence Job PStateR PStateL R jaR jaL Hja
          costR costL Hcost sR sL Hs interR interL Hinter wR wL Hw j xR xL Hx) _ _ ibt_nonself_pred).
    Qed.

    Lemma ibt_busy_interval_related (j : Job) t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      PropSPropRel (@prosa.analysis.abstract.definitions.busy_interval Job jaR costR PStateR sR interR wR j t1R t2R)
        (I.Prosa_Analysis_Abstract_Definitions_busy_interval Job dJ interL wL jaL costL PStateL sL j t1L t2L).
    Proof.
      exact (ad_busy_interval_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
        interR interL Hinter wR wL Hw j t1R t2R t1L t2L).
    Qed.

    Lemma ibt_job_of_task_related (tsk : Task) (j : Job) :
      AdBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
        (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
    Proof. exact (job_of_task_related Job Task jtR jtL Hjt tsk tsk (@Lean.eq_refl _ _) j). Qed.

    Theorem interference_and_workload_consistent_with_sequential_tasks_correspondence (tsk : Task) :
      PropSPropRel
        (@S.interference_and_workload_consistent_with_sequential_tasks Task Job jtR jaR costR PStateR arrR sR tsk
          interR wR)
        (I.Prosa_Analysis_Abstract_IBF_Task_interference_and_workload_consistent_with_sequential_tasks
          Job dJ Task dT jtL jaL costL PStateL arrL sL tsk interL wL).
    Proof.
      unfold S.interference_and_workload_consistent_with_sequential_tasks.
      cbn [I.Prosa_Analysis_Abstract_IBF_Task_interference_and_workload_consistent_with_sequential_tasks].
      apply ad_forall_identity_correspondence => j.
      apply ad_forall_nat_correspondence => t1R t1L H1.
      apply ad_forall_nat_correspondence => t2R t2L H2.
      apply ad_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (ibt_job_of_task_related tsk j))|].
      apply ad_imp_correspondence;
        [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))|].
      apply ad_imp_correspondence; [exact (ibt_busy_interval_related j _ _ _ _ H1 H2)|].
      exact (sub_nat_eq_correspondence _ _ _ _
        (task_workload_between_correspondence Job costR costL Hcost arrR arrL Harr Task jtR jtL Hjt tsk
          _ _ _ _ (sub_nat_rel_canonical O) H1)
        (SOJ.task_service_of_jobs_in_correspondence Job PStateR PStateL (iarta_jsvc Job PStateR PStateL R) sR sL
          Hs Task jtR jtL Hjt tsk _ _ (arrivals_between_correspondence_certificate Job arrR arrL Harr
            _ _ _ _ (sub_nat_rel_canonical O) H1) _ _ _ _ (sub_nat_rel_canonical O) H1)).
    Qed.
  End Defs.
  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  (** ** Observations of a schedule pair *)

  Section Pair.
    Variable sR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable sL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL.

    Lemma ibt_sched_at (j : Job) tR tL (Ht : SubNatRel tR tL) :
      AdBoolRel (@prosa.behavior.service.scheduled_at Job PStateR sR j tR)
        (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL sL j tL).
    Proof. exact (iarta_scheduled_at_related Job PStateR PStateL R sR sL Hs j tR tL Ht). Qed.

    Lemma ibt_service_at (j : Job) tR tL (Ht : SubNatRel tR tL) :
      SubNatRel (@prosa.behavior.service.service_at Job PStateR sR j tR)
        (I.Prosa_Behavior_Service_service_at Job dJ PStateL sL j tL).
    Proof. exact (ad_service_at_related Job PStateR PStateL R sR sL Hs j tR tL Ht). Qed.

    Lemma ibt_completed (j : Job) tR tL (Ht : SubNatRel tR tL) :
      AdBoolRel (@prosa.behavior.service.completed_by Job PStateR sR costR j tR)
        (I.Prosa_Behavior_Service_completed_by Job dJ PStateL sL costL j tL).
    Proof. exact (ad_completed_by_related Job PStateR PStateL R sR sL Hs costR costL Hcost j tR tL Ht). Qed.

    Lemma ibt_pending (j : Job) tR tL (Ht : SubNatRel tR tL) :
      AdBoolRel (@prosa.behavior.service.pending Job PStateR sR costR jaR j tR)
        (I.Prosa_Behavior_Service_pending Job dJ PStateL sL costL jaL j tL).
    Proof.
      unfold prosa.behavior.service.pending. cbn [I.Prosa_Behavior_Service_pending].
      exact (ar_bool_and_related _ _ _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)
        (svc_bool_not_related _ _ (ibt_completed j tR tL Ht))).
    Qed.

    Section Arr.
      Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
      Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
      Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

      Lemma ibt_come_from :
        PropSPropRel (@prosa.behavior.ready.jobs_come_from_arrival_sequence Job PStateR sR arrR)
          (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job dJ PStateL sL arrL).
      Proof.
        unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
        cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence].
        apply ad_forall_identity_correspondence => j.
        apply ad_forall_nat_correspondence => tR tL Ht.
        imp (ad_bool_truth_correspondence _ _ (ibt_sched_at j tR tL Ht)).
        exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      Qed.

    End Arr.
  End Pair.

  Lemma ibt_eq_identity (T : Type) (x y : T) : PropSPropRel (x = y) (Lean.eq x y).
  Proof.
    apply prop_sprop_rel_intro.
    - exact (coq_eq_to_imported_eq x y).
    - intro H. apply strictly_inhabits. exact (imported_eq_to_coq_eq x y H).
  Qed.

  Lemma ibt_uni :
    PropSPropRel (@prosa.model.processor.platform_properties.uniprocessor_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.uniprocessor_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model].
    apply ad_forall_identity_correspondence => j1.
    apply ad_forall_identity_correspondence => j2.
    apply (iarta_forall_sched Job PStateR PStateL R). intros sR sL Hs.
    apply ad_forall_nat_correspondence => tR tL Ht.
    imp (ad_bool_truth_correspondence _ _ (ibt_sched_at sR sL Hs j1 tR tL Ht)).
    imp (ad_bool_truth_correspondence _ _ (ibt_sched_at sR sL Hs j2 tR tL Ht)).
    exact (ibt_eq_identity Job j1 j2).
  Qed.

  (** The common inequality of the case lemmas. *)
  Local Ltac rhs sR sL Hs arrR arrL Harr iR iL Hi tsk j H1 Ht :=
    let Hup := fresh "Hup" in
    have Hup := arta_add_related _ _ _ _ (arta_add_related _ _ _ _ H1 (arta_sub_related _ _ _ _ (Hja j) H1))
      (sub_nat_rel_canonical 1);
    apply sub_nat_le_correspondence;
    [ exact (arta_add_related _ _ _ _ (ad_bool_to_nat_related _ _ (ad_interference_related_general Job iR iL Hi j _ _ Ht))
        (ibt_service_at sR sL Hs j _ _ Ht))
    | exact (arta_add_related _ _ _ _
        (SOJ.service_of_jobs_at_correspondence Job PStateR PStateL (iarta_jsvc Job PStateR PStateL R) sR sL Hs
          _ _ (job_of_task_related Job Task jtR jtL Hjt tsk tsk (@Lean.eq_refl _ _)) _ _
          (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 Hup) _ _ Ht)
        (ad_bool_to_nat_related _ _ (task_interference_correspondence sR sL Hs arrR arrL Harr iR iL Hi j _ _ Ht))) ].













  (** ** Statements with task costs and arrival curves *)

  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).

  Definition IbtMaxArrivalsRel (maR : prosa.model.task.arrival.curves.MaxArrivals Task)
      (maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT) : SProp :=
    forall (tsk : Task) (nR : nat) (nL : Lean.Nat), SubNatRel nR nL ->
      SubNatRel (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk nR)
        (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk nL).

  Lemma ibt_forall_ma (PR : prosa.model.task.arrival.curves.MaxArrivals Task -> Prop)
      (PL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT -> SProp) :
    (forall maR maL, IbtMaxArrivalsRel maR maL -> PropSPropRel (PR maR) (PL maL)) ->
    PropSPropRel (forall m, PR m) (forall m, PL m).
  Proof.
    apply (arta_forall_cover _ _ IbtMaxArrivalsRel
      (fun maR => I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_mk Task dT
        (fun tsk nL => sub_nat_to_imported (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk
          (sub_nat_to_rocq nL))))
      (fun maL => ((fun tsk n => sub_nat_to_rocq
        (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk (sub_nat_to_imported n)))
        : prosa.model.task.arrival.curves.MaxArrivals Task))).
    - intros maR tsk nR nL Hn. cbn. rewrite (arta_nat_input _ _ Hn). exact (sub_nat_rel_canonical _).
    - intros maL tsk nR nL Hn. unfold SubNatRel. cbn.
      exact (sub_imported_eq_trans _ _ _ (sub_nat_imported_roundtrip _)
        (sub_imported_eq_congr (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk)
          _ _ Hn)).
  Qed.

  Lemma ibt_taskset_respects arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) tsR tsL
      (Hts : ArListRel tsR tsL) maR maL (Hma : IbtMaxArrivalsRel maR maL) :
    PropSPropRel (@prosa.model.task.arrival.curves.taskset_respects_max_arrivals Task Job jtR arrR maR tsR)
      (I.Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task dT Job dJ jtL arrL maL tsL).
  Proof.
    unfold prosa.model.task.arrival.curves.taskset_respects_max_arrivals.
    cbn [I.Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals].
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    exact (CVC.respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsk _ _ (Hma tsk)).
  Qed.


End IbfTask.
