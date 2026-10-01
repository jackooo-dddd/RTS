(* Main certificate for results/rta/ideal/edf/bounded_nps.v: the helper part (no statement correspondences) of the accepted
   certificates/analysis_abstract_ideal_iw_instantiation/IdealIwInstantiationCorrespondence.v (generator
   gen_idl_main.py), replayed at the ideal processor-model universe instance of this export, followed by the local
   helpers and the statement correspondences of this file.  Dropped helper blocks: rsi_policy_respects_sequential_rel, IL, WL, rsi_interference_rel, rsi_workload_rel, rsi_interference_related, rsi_ab_quiet_time_related, rsi_ab_busy_interval_prefix_related, rsi_ab_busy_interval_related (they name the two ideal interference instances or an iw_instantiation statement constant, none of which this export contains; not used). *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import IdealIwInstantiationSemanticSource RtaIdealEdfBoundedNpsSemanticSource.
From prosa Require TaskPreemptionParametersSemanticSource PreemptionParameterSemanticSource
  PriorityDrivenSemanticSource
  EdfAthepBoundSemanticSource RtaIdealEdfBoundedPiSemanticSource BlockingBoundEdfSemanticSource.
From prosa Require Import analysis.abstract.search_space model.task.arrival.curves.
From prosa Require Import model.readiness.basic model.priority.edf model.task.absolute_deadline.
From prosa Require Import analysis.abstract.definitions model.job.properties
  model.processor.platform_properties model.processor.supply model.schedule.work_conserving
  analysis.definitions.work_bearing_readiness model.processor.ideal.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaIdealEdfBoundedNps ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  IdlArrivalsSeqBaseAdapter IdlArrivalsSeqOperations IdlArrivalsSeqCorrespondence IdlArrivalsCorrespondence
  IdlWorkloadCorrespondence
  IdlAbstractDefinitionsBaseAdapter IdlServiceBaseAdapter IdlServiceNatBoolOperations
  IdlAbstractDefinitionsArrivalOperations IdlAbstractDefinitionsClasses IdlAbstractDefinitionsNatBoolOperations
  IdlAbstractDefinitionsIntervalOperations IdlAbstractDefinitionsOperations IdlAbstractDefinitionsSums
  IdlAbstractDefinitionsLogical IdlServiceIntervalOperations IdlServiceScheduleOperations
  IdlAbstractDefinitionsPendingOperations IdlAbstractDefinitionsTaskOperations
  IdlAbstractDefinitionsBusyIntervalHelpers IdlAbstractRtaHelpers IdlIdealAbstractRtaHelpers.
From FoundationCertificates Require
  IdlSupplyScheduleBaseAdapter IdlSupplyScheduleFiniteOperations IdlSupplyScheduleOperations
  IdlSupplyBaseAdapter IdlSupplyNatBoolOperations IdlSupplyIntervalOperations IdlSupplyCorrespondence
  IdlJitterSvcBaseAdapter IdlJitterSvcNatBoolOperations IdlJitterSvcIntervalOperations
  IdlJitterSvcScheduleOperations IdlJitterSvcJobOperations IdlPreemptionParameterCorrespondence
  IdlTaskPreemptionParametersCorrespondence IdlSequentialityCorrespondence
  IdlIbfTaskHelpers IdlIbfSupplyTaskCorrespondence IdlServiceInversionPredCorrespondence
  IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlPreemptionTimeCorrespondence
  IdlEdfAthepBoundCorrespondence.
From FoundationCertificates Require Import IdlIbfTaskFullHelpers IdlStateRel.
From FoundationCertificates Require Import IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence.

Module I := ImportedRtaIdealEdfBoundedNps.
Module S := IdealIwInstantiationSemanticSource.IdealIwInstantiationSemanticSource.
Module S2 := RtaIdealEdfBoundedNpsSemanticSource.RtaIdealEdfBoundedNpsSemanticSource.
Module BPI := RtaIdealEdfBoundedPiSemanticSource.RtaIdealEdfBoundedPiSemanticSource.
Module BBES := BlockingBoundEdfSemanticSource.BlockingBoundEdfSemanticSource.
Module EABC := FoundationCertificates.IdlEdfAthepBoundCorrespondence.
Module PPC := FoundationCertificates.IdlPreemptionParameterCorrespondence.
Module TPPC := FoundationCertificates.IdlTaskPreemptionParametersCorrespondence.
Module SQC := FoundationCertificates.IdlSequentialityCorrespondence.
Module PTC := FoundationCertificates.IdlPreemptionTimeCorrespondence.
Module TPP := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module PDS := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.
Module EAS := EdfAthepBoundSemanticSource.EdfAthepBoundSemanticSource.
Module PIC := FoundationCertificates.IdlPriorityInversionCorrespondence.
Module PIS := PriorityInversionSemanticSource.PriorityInversionSemanticSource.
Module SSO := FoundationCertificates.IdlServiceScheduleOperations.
Module SUP := FoundationCertificates.IdlSupplyScheduleOperations.
Module SUPC := FoundationCertificates.IdlSupplyCorrespondence.
Module JSO := FoundationCertificates.IdlJitterSvcScheduleOperations.
Module IBST := FoundationCertificates.IdlIbfSupplyTaskCorrespondence.
Module SIPC := FoundationCertificates.IdlServiceInversionPredCorrespondence.
Module IFC := FoundationCertificates.IdlInterferenceCorrespondence.
Module B := BusyIntervalClassicalSemanticSource.BusyIntervalClassicalSemanticSource.
Module SIP := ServiceInversionPredSemanticSource.ServiceInversionPredSemanticSource.
Module IFS := InterferenceSemanticSource.InterferenceSemanticSource.
Module IBTS := IbfTaskSemanticSource.IbfTaskSemanticSource.

(** Statement correspondences for [results/rta/ideal/edf/bounded_nps.v], on top of the helper part (no statement
    correspondences) of the accepted certificate for [analysis/abstract/ideal/iw_instantiation.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading instance inputs; target side: the imported Lean theorem
    types.  The processor model is fixed to the ideal uniprocessor on both
    sides: its states are related by the constructor-preserving Option map
    and its unit core by the singleton core enumeration ([IdlStateRel], built
    from the accepted duplicate-freedom and completeness interface theorems),
    giving a concrete [SvcProcessorStateRel]; every accepted generic chain
    certificate is replayed at the ideal processor-model universe instance of
    this export.  From it the preemption and supply family relations are
    built exactly as in the accepted restricted-supply certificate.
    [job_arrival], [job_cost] and [task_cost] pointwise; [JobTask] by
    [AdJobTaskRel]; arrival sequences, schedules, JLFP policies (pointwise on
    Booleans), readiness instances (on the statement's schedule pair),
    max-arrival bounds, task sets, jobs, tasks and instants are covered in
    both directions.  The two section-local instances are related field by
    field: priority inversion by the accepted priority-inversion certificate,
    the higher-or-equal-priority interference and interfering workload by
    the accepted interference definition certificate, Booleans counted as
    naturals by the accepted bool-to-nat lemmas.  The abstract, classical and
    IBF/task notions are the accepted certificates over these instance
    relations (as in the accepted restricted-supply certificate, whose helper
    part is replayed here); the ideal idle predicate and [all_jobs_from_taskset]
    are related here by unfolding.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma rsi_and_true_right (a b : I.Bool) :
  Lean.eq (I.Bool_and a b) I.Bool_true -> Lean.eq b I.Bool_true.
Proof.
  destruct a; cbn; intro H.
  - exact (ar_false_elim _ (ar_false_ne_true H)).
  - exact H.
Qed.

Lemma rsi_and_absorb_target (bR : bool) (pL : I.Bool) :
  (bR = true -> Lean.eq pL I.Bool_true) ->
  Lean.eq (ar_bool_to_imported bR) (I.Bool_and (ar_bool_to_imported bR) pL).
Proof.
  destruct bR; cbn; intro H.
  - exact (sub_imported_eq_sym _ _ (H (Logic.eq_refl _))).
  - exact (@Lean.eq_refl _ _).
Qed.

Lemma rsi_and_absorb_source (rL : I.Bool) (pR : bool) :
  (Lean.eq rL I.Bool_true -> pR = true) ->
  Lean.eq (ar_bool_to_imported (ar_bool_to_rocq rL && pR)) rL.
Proof.
  destruct rL; cbn; intro H.
  - exact (@Lean.eq_refl _ _).
  - rewrite (H (@Lean.eq_refl _ _)). exact (@Lean.eq_refl _ _).
Qed.

Lemma rsi_bool_true_of_rel (bR : bool) (bL : I.Bool) :
  ArBoolRel bR bL -> Lean.eq bL I.Bool_true -> bR = true.
Proof.
  intros Hb HL.
  have E := imported_eq_to_coq_eq _ _ (sub_imported_eq_trans _ _ _ Hb HL).
  have E' := f_equal ar_bool_to_rocq E.
  rewrite ar_bool_source_roundtrip in E'. exact E'.
Qed.

Lemma rsi_exists_identity (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (H x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (H x) Hx).
Qed.

Section IdealIwInstantiation.
  Context (Task Job : eqType).
  Let dT := ad_decidable_eq Task.
  Let dJ := ad_decidable_eq Job.
  Let PStateR := prosa.model.processor.ideal.processor_state Job.
  Let PStateL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.
  Let R : SSO.SvcProcessorStateRel Job PStateR PStateL := idl_psrel Job.
  Let Hsupply_on := idl_supply_on Job.
  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PStateL.

  (** *** The family relations, built from [R] *)

  Definition rsi_jsvc : JSO.SvcProcessorStateRel Job PStateR PStateL := {|
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

  Definition rsi_sup : SUP.SupplyProcessorStateRel Job PStateR PStateL := {|
    SUP.supply_ps_state_rel := SSO.svc_ps_state_rel Job PStateR PStateL R;
    SUP.supply_ps_core_to_target := SSO.svc_ps_core_to_target Job PStateR PStateL R;
    SUP.supply_ps_core_enumeration_rel := SSO.svc_ps_core_enumeration_rel Job PStateR PStateL R;
    SUP.supply_ps_supply_on_rel := Hsupply_on
  |}.

  Lemma rsi_hs_sup sR sL :
    SSO.SvcScheduleRel Job PStateR PStateL R sR sL -> SUP.SupplyScheduleRel Job PStateR PStateL rsi_sup sR sL.
  Proof. exact (fun Hs => Hs). Qed.

  Lemma rsi_hs_jsvc sR sL :
    SSO.SvcScheduleRel Job PStateR PStateL R sR sL -> JSO.SvcScheduleRel Job PStateR PStateL rsi_jsvc sR sL.
  Proof. exact (fun Hs => Hs). Qed.

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

  (** *** Covers *)

  Definition rsi_sched_to_target (sR : SchedR) : SchedL :=
    fun tL => SSO.svc_ps_state_to_target Job PStateR PStateL R (sR (sub_nat_to_rocq tL)).
  Definition rsi_sched_to_source (sL : SchedL) : SchedR :=
    fun tR => SSO.svc_ps_state_to_source Job PStateR PStateL R (sL (sub_nat_to_imported tR)).

  Lemma rsi_forall_sched (PR : SchedR -> Prop) (PL : SchedL -> SProp) :
    (forall sR sL, SSO.SvcScheduleRel Job PStateR PStateL R sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    apply (arta_forall_cover _ _ (SSO.SvcScheduleRel Job PStateR PStateL R)
      rsi_sched_to_target rsi_sched_to_source).
    - intros sR tR tL Ht. unfold rsi_sched_to_target. rewrite (arta_nat_input _ _ Ht).
      exact (SSO.svc_ps_state_rel_canonical Job PStateR PStateL R _).
    - intros sL tR tL Ht. destruct Ht.
      exact (SSO.svc_ps_state_rel_surjective Job PStateR PStateL R _).
  Qed.

  Definition rsi_arr_to_source (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ) :
      prosa.behavior.arrival_sequence.arrival_sequence Job :=
    fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

  Lemma rsi_forall_arr (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
      (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ -> SProp) :
    (forall aR aL, ArArrivalSequenceRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) ->
    PropSPropRel (forall a, PR a) (forall a, PL a).
  Proof.
    apply (arta_forall_cover _ _ (ArArrivalSequenceRel Job) (ar_arrival_sequence_to_imported Job)
      rsi_arr_to_source (ar_arrival_sequence_canonical Job)).
    intros arrL tR tL Ht. unfold ArListRel, rsi_arr_to_source.
    refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
    exact (sub_imported_eq_congr arrL _ _ Ht).
  Qed.

  Lemma rsi_forall_state (PR : @prosa.behavior.schedule.State Job PStateR -> Prop)
      (PL : I.Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job dJ PStateL -> SProp) :
    (forall sR sL, SSO.svc_ps_state_rel Job PStateR PStateL R sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    exact (arta_forall_cover _ _ (SSO.svc_ps_state_rel Job PStateR PStateL R)
      (SSO.svc_ps_state_to_target Job PStateR PStateL R) (SSO.svc_ps_state_to_source Job PStateR PStateL R)
      (SSO.svc_ps_state_rel_canonical Job PStateR PStateL R)
      (SSO.svc_ps_state_rel_surjective Job PStateR PStateL R) PR PL).
  Qed.

  (** JLFP policies, pointwise on Booleans. *)
  Definition RsiJLFPRel (pR : prosa.model.priority.definitions.JLFP_policy Job)
      (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ) : SProp :=
    forall x y : Job, ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Lemma rsi_forall_jlfp (PR : prosa.model.priority.definitions.JLFP_policy Job -> Prop)
      (PL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ -> SProp) :
    (forall pR pL, RsiJLFPRel pR pL -> PropSPropRel (PR pR) (PL pL)) ->
    PropSPropRel (forall p, PR p) (forall p, PL p).
  Proof.
    apply (arta_forall_cover _ _ RsiJLFPRel
      (fun pR => I.Prosa_Model_Priority_Definitions_JLFP_policy_mk Job dJ
        (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_job Job pR x y)))
      (fun pL => ((fun x y => ar_bool_to_rocq
        (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y))
        : prosa.model.priority.definitions.JLFP_policy Job))).
    - intros pR x y. exact (@Lean.eq_refl _ _).
    - intros pL x y. exact (ar_bool_target_roundtrip _).
  Qed.

  Lemma rsi_reflexive_rel pR pL (Hp : RsiJLFPRel pR pL) :
    PropSPropRel (@prosa.model.priority.definitions.reflexive_job_priorities Job pR)
      (I.Prosa_Model_Priority_Definitions_reflexive_job_priorities Job dJ pL).
  Proof.
    unfold prosa.model.priority.definitions.reflexive_job_priorities.
    cbn [I.Prosa_Model_Priority_Definitions_reflexive_job_priorities].
    apply ar_forall_identity_correspondence. intro j.
    exact (ar_bool_truth_correspondence _ _ (Hp j j)).
  Qed.

  (** The JLDP view of a JLFP policy. *)
  Lemma rsi_jlfp_to_jldp_rel pR pL (Hp : RsiJLFPRel pR pL) :
    forall tR tL, SubNatRel tR tL -> forall x y : Job,
      ArBoolRel (@prosa.model.priority.definitions.hep_job_at Job
          (@prosa.model.priority.coercion.JLFP_to_JLDP Job pR) tR x y)
        (I.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job dJ
          (I.Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job dJ pL) tL x y).
  Proof. intros tR tL Ht x y. exact (Hp x y). Qed.


  (** *** Observations of the processor model *)

  Lemma rsi_fully_consuming_rel :
    PropSPropRel (@prosa.model.processor.platform_properties.fully_consuming_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model_inst4 Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.fully_consuming_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model_inst4].
    apply ad_forall_identity_correspondence. intro j.
    apply rsi_forall_sched. intros sR sL Hs.
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (ibt_sched_at Job PStateR PStateL R sR sL Hs j _ _ Ht))|].
    exact (sub_nat_eq_correspondence _ _ _ _ (ad_service_at_related Job PStateR PStateL R sR sL Hs j tR tL Ht)
      (SUPC.supply_at_correspondence Job PStateR PStateL rsi_sup sR sL (rsi_hs_sup sR sL Hs) tR tL Ht)).
  Qed.

  (** *** Observations of a schedule pair *)

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL.

    Let Hsa := ibt_sched_at Job PStateR PStateL R sR sL Hs.
    Let COMPLETED := ibt_completed Job PStateR PStateL R costR costL Hcost sR sL Hs.
    Let PENDING := ibt_pending Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs.

    Lemma rsi_must_arrive_rel :
      PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PStateR sR)
        (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job dJ jaL PStateL sL).
    Proof.
      unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros tR tL Ht.
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (Hsa j _ _ Ht))|].
      exact (ad_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
    Qed.

    Lemma rsi_completed_dont_execute_rel :
      PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PStateR sR costR)
        (I.Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job dJ PStateL sL costL).
    Proof.
      unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros tR tL Ht.
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (Hsa j _ _ Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _
        (ad_service_related Job PStateR PStateL R sR sL Hs j tR tL Ht) (Hcost j)).
    Qed.

    Lemma rsi_receives_service_at_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
      ArBoolRel (@prosa.behavior.service.receives_service_at Job PStateR sR j tR)
        (I.Prosa_Behavior_Service_receives_service_at_inst4 Job dJ PStateL sL j tL).
    Proof.
      unfold prosa.behavior.service.receives_service_at.
      cbn [I.Prosa_Behavior_Service_receives_service_at_inst4].
      exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O)
        (ad_service_at_related Job PStateR PStateL R sR sL Hs j tR tL Ht)).
    Qed.

    Section Arr.
      Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
      Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
      Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

      Section Policy.
        Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
        Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
        Hypothesis Hp : RsiJLFPRel pR pL.

        (** **** The instantiated interference and interfering workload *)

        Let IR := @S.ideal_jlfp_interference Job arrR sR pR.
        Let WR := @S.ideal_jlfp_interfering_workload Job costR arrR sR pR.
        Lemma rsi_priority_inversion_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
          ArBoolRel (@PIS.priority_inversion Job PStateR arrR sR pR j tR)
            (I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_inst4 Job dJ PStateL arrL sL pL j tL).
        Proof.
          exact (PIC.priority_inversion_correspondence Job PStateR PStateL rsi_jsvc arrR arrL Harr sR sL
            (rsi_hs_jsvc sR sL Hs) pR pL Hp j tR tL Ht).
        Qed.



        Lemma rsi_quiet_time_related (j : Job) (tR : nat) (tL : Lean.Nat) :
          SubNatRel tR tL ->
          PropSPropRel (@B.quiet_time Job jaR costR PStateR arrR sR pR j tR)
            (I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time_inst4
              Job dJ jaL costL PStateL arrL sL pL j tL).
        Proof.
          intro Ht. unfold B.quiet_time.
          cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time_inst4].
          apply ar_forall_identity_correspondence. intro j_hp.
          apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL
            j_hp Harr)|].
          apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp j_hp j))|].
          apply ar_imp_correspondence;
            [exact (ar_bool_truth_correspondence _ _
              (arrived_before_correspondence_certificate Job jaR jaL j_hp Hja tR tL Ht))|].
          exact (ar_bool_truth_correspondence _ _ (COMPLETED j_hp tR tL Ht)).
        Qed.

        Lemma rsi_busy_interval_prefix_related (j : Job) t1R t1L t2R t2L :
          SubNatRel t1R t1L -> SubNatRel t2R t2L ->
          PropSPropRel (@B.busy_interval_prefix Job jaR costR PStateR arrR sR pR j t1R t2R)
            (I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix_inst4
              Job dJ jaL costL PStateL arrL sL pL j t1L t2L).
        Proof.
          intros H1 H2. unfold B.busy_interval_prefix.
          cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix_inst4].
          apply ar_and_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ H1 H2)|].
          apply ar_and_correspondence; [exact (rsi_quiet_time_related j _ _ H1)|].
          apply ar_and_correspondence.
          - apply ar_forall_nat_correspondence. intros tR tL Ht.
            apply ar_imp_correspondence.
            + exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
                (ar_decide_lt_related _ _ _ _ H1 Ht) (ar_decide_lt_related _ _ _ _ Ht H2))).
            + exact (ad_not_correspondence _ _ (rsi_quiet_time_related j _ _ Ht)).
          - exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
              (ar_decide_le_related _ _ _ _ H1 (Hja j)) (ar_decide_lt_related _ _ _ _ (Hja j) H2))).
        Qed.

        Lemma rsi_busy_interval_related (j : Job) t1R t1L t2R t2L :
          SubNatRel t1R t1L -> SubNatRel t2R t2L ->
          PropSPropRel (@B.busy_interval Job jaR costR PStateR arrR sR pR j t1R t2R)
            (I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_inst4
              Job dJ jaL costL PStateL arrL sL pL j t1L t2L).
        Proof.
          intros H1 H2. unfold B.busy_interval.
          cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_inst4].
          apply ar_and_correspondence; [exact (rsi_busy_interval_prefix_related j _ _ _ _ H1 H2)|].
          exact (rsi_quiet_time_related j _ _ H2).
        Qed.

        (** **** Abstract busy intervals over the instantiation *)




        (** **** Readiness at this schedule pair *)

        Definition RsiJrAt (jrR : @prosa.behavior.ready.JobReady Job PStateR costR jaR)
            (jrL : I.Prosa_Behavior_Ready_JobReady_inst4 Job dJ PStateL costL jaL) : SProp :=
          forall j tR tL, SubNatRel tR tL ->
            ArBoolRel (@prosa.behavior.ready.job_ready Job PStateR costR jaR jrR sR j tR)
              (I.Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job dJ PStateL costL jaL jrL sL j tL).

        Definition rsi_jr_to_target (jrR : @prosa.behavior.ready.JobReady Job PStateR costR jaR) :
            I.Prosa_Behavior_Ready_JobReady_inst4 Job dJ PStateL costL jaL :=
          I.Prosa_Behavior_Ready_JobReady_mk_inst4 Job dJ PStateL costL jaL
            (fun s j tL => I.Bool_and
              (ar_bool_to_imported (@prosa.behavior.ready.job_ready Job PStateR costR jaR jrR sR j
                (sub_nat_to_rocq tL)))
              (I.Prosa_Behavior_Service_pending_inst4 Job dJ PStateL s costL jaL j tL))
            (fun s j t H => rsi_and_true_right _ _ H).

        Definition rsi_jr_to_source (jrL : I.Prosa_Behavior_Ready_JobReady_inst4 Job dJ PStateL costL jaL) :
            @prosa.behavior.ready.JobReady Job PStateR costR jaR :=
          @prosa.behavior.ready.Build_JobReady Job PStateR costR jaR
            (fun s j t => ar_bool_to_rocq
              (I.Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job dJ PStateL costL jaL jrL sL j
                (sub_nat_to_imported t))
              && @prosa.behavior.service.pending Job PStateR s costR jaR j t)
            (fun s j t H => proj2 (andP H)).

        Lemma rsi_jr_to_target_rel jrR : RsiJrAt jrR (rsi_jr_to_target jrR).
        Proof.
          intros j tR tL Ht. unfold ArBoolRel, rsi_jr_to_target. cbn.
          have Hpd := PENDING j tR tL Ht.
          destruct Ht. rewrite sub_nat_rocq_roundtrip.
          destruct jrR as [f Hf]. cbn.
          apply rsi_and_absorb_target. intro Hr.
          have Hpr : @prosa.behavior.service.pending Job PStateR sR costR jaR j tR = true := Hf sR j tR Hr.
          rewrite Hpr in Hpd. exact (sub_imported_eq_sym _ _ Hpd).
        Qed.

        Lemma rsi_jr_to_source_rel jrL : RsiJrAt (rsi_jr_to_source jrL) jrL.
        Proof.
          intros j tR tL Ht. unfold ArBoolRel, rsi_jr_to_source. cbn.
          have Hpd := PENDING j tR tL Ht.
          have Hlaw := I.Prosa_Behavior_Ready_JobReady_ready_implies_pending_inst4 Job dJ PStateL costL jaL jrL sL j tL.
          destruct Ht.
          apply rsi_and_absorb_source. intro Hr.
          exact (rsi_bool_true_of_rel _ _ Hpd (Hlaw Hr)).
        Qed.

        Lemma rsi_forall_jr (PRr : @prosa.behavior.ready.JobReady Job PStateR costR jaR -> Prop)
            (PLr : I.Prosa_Behavior_Ready_JobReady_inst4 Job dJ PStateL costL jaL -> SProp) :
          (forall jrR jrL, RsiJrAt jrR jrL -> PropSPropRel (PRr jrR) (PLr jrL)) ->
          PropSPropRel (forall jr, PRr jr) (forall jr, PLr jr).
        Proof.
          exact (arta_forall_cover _ _ RsiJrAt rsi_jr_to_target rsi_jr_to_source
            rsi_jr_to_target_rel rsi_jr_to_source_rel PRr PLr).
        Qed.

        Section Ready.
          Variable jrR : @prosa.behavior.ready.JobReady Job PStateR costR jaR.
          Variable jrL : I.Prosa_Behavior_Ready_JobReady_inst4 Job dJ PStateL costL jaL.
          Hypothesis Hjr : RsiJrAt jrR jrL.

          Lemma rsi_valid_schedule_rel :
            PropSPropRel (@prosa.behavior.ready.valid_schedule Job jaR PStateR sR costR jrR arrR)
              (I.Prosa_Behavior_Ready_valid_schedule_inst4 Job dJ jaL PStateL sL costL jrL arrL).
          Proof.
            unfold prosa.behavior.ready.valid_schedule, prosa.behavior.ready.jobs_must_be_ready_to_execute.
            cbn [I.Prosa_Behavior_Ready_valid_schedule_inst4 I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst4].
            apply ar_and_correspondence;
              [exact (ibt_come_from Job PStateR PStateL R sR sL Hs
                arrR arrL Harr)|].
            apply ar_forall_identity_correspondence. intro j.
            apply ar_forall_nat_correspondence. intros tR tL Ht.
            apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j _ _ Ht))|].
            exact (ar_bool_truth_correspondence _ _ (Hjr j tR tL Ht)).
          Qed.

          Lemma rsi_backlogged_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
            ArBoolRel (@prosa.behavior.ready.backlogged Job PStateR costR jaR jrR sR j tR)
              (I.Prosa_Behavior_Ready_backlogged_inst4 Job dJ PStateL costL jaL jrL sL j tL).
          Proof.
            unfold prosa.behavior.ready.backlogged. cbn [I.Prosa_Behavior_Ready_backlogged_inst4].
            exact (ar_bool_and_related _ _ _ _ (Hjr j tR tL Ht) (svc_bool_not_related _ _ (Hsa j tR tL Ht))).
          Qed.

          Lemma rsi_work_conserving_related :
            PropSPropRel (@prosa.model.schedule.work_conserving.work_conserving Job jaR costR PStateR jrR
              arrR sR)
              (I.Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job dJ jaL costL PStateL jrL arrL sL).
          Proof.
            unfold prosa.model.schedule.work_conserving.work_conserving.
            cbn [I.Prosa_Model_Schedule_WorkConserving_work_conserving_inst4].
            apply ar_forall_identity_correspondence. intro j.
            apply ar_forall_nat_correspondence. intros tR tL Ht.
            apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j
              Harr)|].
            apply ar_imp_correspondence;
              [exact (ar_bool_truth_correspondence _ _ (rsi_backlogged_related j tR tL Ht))|].
            apply rsi_exists_identity. intro jo.
            exact (ar_bool_truth_correspondence _ _ (Hsa jo tR tL Ht)).
          Qed.

          Lemma rsi_work_bearing_related :
            PropSPropRel
              (@prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness
                Job jaR costR PStateR jrR arrR sR pR)
              (I.Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness_inst4
                Job dJ jaL costL PStateL jrL arrL sL pL).
          Proof.
            unfold prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness.
            cbn [I.Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness_inst4].
            apply ar_forall_identity_correspondence. intro j.
            apply ar_forall_nat_correspondence. intros tR tL Ht.
            apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j
              Harr)|].
            apply ar_imp_correspondence;
              [exact (ar_bool_truth_correspondence _ _ (PENDING j tR tL Ht))|].
            apply rsi_exists_identity. intro jhp.
            apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL
              jhp Harr)|].
            apply ar_and_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hjr jhp tR tL Ht))|].
            exact (ar_bool_truth_correspondence _ _ (Hp jhp j)).
          Qed.
        End Ready.
      End Policy.
    End Arr.
  End Sched.

  (** *** Task costs, the ideal idle predicate, task sets *)

  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).

  Lemma idl_idle_related (sR : SchedR) (sL : SchedL) (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL)
      (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
    AdBoolRel (@prosa.model.processor.ideal.ideal_is_idle Job sR tR)
      (I.Prosa_Model_Processor_Ideal_ideal_is_idle Job dJ sL tL).
  Proof.
    unfold prosa.model.processor.ideal.ideal_is_idle. unfold I.Prosa_Model_Processor_Ideal_ideal_is_idle.
    have E := imported_eq_to_coq_eq (idl_st_to Job (sR tR)) (sL tL) (Hs tR tL Ht). rewrite <- E.
    destruct (sR tR); exact (@Lean.eq_refl _ _).
  Qed.

  Lemma idl_all_jobs_from_taskset_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
      (tsR : seq Task) (tsL : I.List Task) (Hts : ArListRel tsR tsL) :
    PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
      (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
  Proof.
    unfold prosa.model.task.concept.all_jobs_from_taskset.
    cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    have E : Logic.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j) := imported_eq_to_coq_eq _ _ (Hjt j).
    rewrite <- E.
    exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task _ tsR tsL Hts)).
  Qed.

  (** *** Shared hypothesis prefixes *)

  Ltac rsi_arr_sched arrR arrL Harr sR sL Hs :=
    apply rsi_forall_arr; intros arrR arrL Harr;
    (apply ad_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|]);
    apply rsi_forall_sched; intros sR sL Hs;
    (apply ad_imp_correspondence;
      [exact (ibt_come_from Job PStateR PStateL R sR sL Hs
        arrR arrL Harr)|]);
    (apply ad_imp_correspondence; [exact (rsi_must_arrive_rel sR sL Hs)|]).
  Ltac rsi_jlfp pR pL Hp :=
    apply rsi_forall_jlfp; intros pR pL Hp;
    (apply ad_imp_correspondence; [exact (rsi_reflexive_rel pR pL Hp)|]).
  Ltac idl_full arrR arrL Harr sR sL Hs pR pL Hp :=
    rsi_arr_sched arrR arrL Harr sR sL Hs;
    (apply ad_imp_correspondence; [exact (rsi_completed_dont_execute_rel sR sL Hs)|]);
    rsi_jlfp pR pL Hp.
  Ltac idl_ready sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr :=
    apply (rsi_forall_jr sR sL Hs); intros jrR jrL Hjr;
    (apply ad_imp_correspondence; [exact (rsi_work_bearing_related sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr)|]);
    (apply ad_imp_correspondence; [exact (rsi_work_conserving_related sR sL Hs arrR arrL Harr jrR jrL Hjr)|]).
  Ltac idl_j_pos arrR arrL Harr j :=
    apply ad_forall_identity_correspondence; intro j;
    (apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j Harr)|]);
    (apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (arta_cost_positive_related Job costR costL Hcost j))|]).

  (** ** Statement correspondences for [results/rta/ideal/edf/bounded_nps.v] *)

  Local Ltac imp H := apply ad_imp_correspondence; [exact H|].

  (** *** Task-set predicates (as in the accepted ideal FP bounded_pi certificate) *)

  Lemma rien_all_jobs_from_taskset_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
      (tsR : seq Task) (tsL : I.List Task) (Hts : ArListRel tsR tsL) :
    PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
      (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
  Proof.
    unfold prosa.model.task.concept.all_jobs_from_taskset.
    cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    have E : Logic.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j) := imported_eq_to_coq_eq _ _ (Hjt j).
    rewrite <- E.
    exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task _ tsR tsL Hts)).
  Qed.

  Lemma rien_valid_taskset_curve_rel tsR tsL (Hts : ArListRel tsR tsL) maR maL
      (Hma : IbtMaxArrivalsRel Task maR maL) :
    PropSPropRel (@prosa.model.task.arrival.curves.valid_taskset_arrival_curve Task tsR
        (@prosa.model.task.arrival.curves.max_arrivals Task maR))
      (I.Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task dT tsL
        (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL)).
  Proof.
    unfold prosa.model.task.arrival.curves.valid_taskset_arrival_curve.
    cbn [I.Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve].
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    unfold prosa.model.task.arrival.curves.valid_arrival_curve.
    cbn [I.Prosa_Model_Task_Arrival_Curves_valid_arrival_curve].
    apply ad_and_correspondence.
    - exact (sub_nat_eq_correspondence _ _ _ _ (Hma tsk _ _ (sub_nat_rel_canonical O)) (sub_nat_rel_canonical O)).
    - unfold prosa.util.rel.monotone. cbn [I.Prosa_Util_Rel_monotone_inst1].
      apply ad_forall_nat_correspondence => xR xL Hx.
      apply ad_forall_nat_correspondence => yR yL Hy.
      imp (ad_bool_truth_correspondence _ _ (svc_decide_le_related _ _ _ _ Hx Hy)).
      exact (ad_bool_truth_correspondence _ _ (svc_decide_le_related _ _ _ _ (Hma tsk _ _ Hx) (Hma tsk _ _ Hy))).
  Qed.

  (** *** Function relation for bound functions *)

  Definition RienFunRel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) : SProp :=
    forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

  (** *** Task deadlines, the EDF policy and the basic readiness at the related schedule pair (as in the accepted
      restricted-supply EDF fully-preemptive certificate) *)

  Variable tdR : prosa.model.task.concept.TaskDeadline Task.
  Variable tdL : I.Prosa_Model_Task_Concept_TaskDeadline Task dT.
  Hypothesis Htd : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR tsk)
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL tsk).

  Lemma rien_task_deadline_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (arta_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_deadline Task tdR
          (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL v)) _ _ (Hjt j) (Htd _)).
  Qed.

  Let ER := @prosa.model.priority.edf.EDF Job
    (@prosa.model.task.absolute_deadline.job_deadline_from_task_deadline Job Task tdR jaR jtR).
  Let EL := I.Prosa_Model_Priority_Edf_EDF Job dJ
    (I.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task dJ dT tdL jaL jtL).

  Lemma rien_edf_rel : RsiJLFPRel ER EL.
  Proof.
    intros x y. cbn.
    exact (svc_decide_le_related _ _ _ _
      (svc_target_add_related _ _ _ _ (Hja x) (rien_task_deadline_of_job_related x))
      (svc_target_add_related _ _ _ _ (Hja y) (rien_task_deadline_of_job_related y))).
  Qed.

  Lemma rien_basic_ready_at sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL) :
    RsiJrAt sR sL
      (@prosa.model.readiness.basic.basic_ready_instance Job PStateR jaR costR)
      (I.Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job dJ PStateL jaL costL).
  Proof.
    intros j tR tL Ht. cbn.
    exact (ibt_pending Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs j tR tL Ht).
  Qed.

  Lemma rien_backlogged_rel sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL) jrR jrL
      (Hjr : RsiJrAt sR sL jrR jrL) (j : Job) tR tL (Ht : SubNatRel tR tL) :
    ArBoolRel (@prosa.behavior.ready.backlogged Job PStateR costR jaR jrR sR j tR)
      (I.Prosa_Behavior_Ready_backlogged_inst4 Job dJ PStateL costL jaL jrL sL j tL).
  Proof.
    unfold prosa.behavior.ready.backlogged. cbn [I.Prosa_Behavior_Ready_backlogged_inst4].
    exact (ar_bool_and_related _ _ _ _ (Hjr j tR tL Ht)
      (svc_bool_not_related _ _ (ibt_sched_at Job PStateR PStateL R sR sL Hs j tR tL Ht))).
  Qed.

  Lemma rien_respects_jlfp_rel sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL)
      arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
      jpR jpL (Hjp : PPC.PpJobPreemptableRel Job jpR jpL)
      jrR jrL (Hjr : RsiJrAt sR sL jrR jrL) pR pL (Hp : RsiJLFPRel pR pL) :
    PropSPropRel (@PDS.respects_JLFP_policy_at_preemption_point Job jaR costR PStateR jpR jrR arrR sR pR)
      (I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4
        Job dJ jaL costL PStateL jpL jrL arrL sL pL).
  Proof.
    unfold PDS.respects_JLFP_policy_at_preemption_point, PDS.respects_JLDP_policy_at_preemption_point.
    cbn [I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4
      I.Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point_inst4].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j_hp.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _
      (PTC.preemption_time_correspondence Job jpR jpL Hjp PStateR PStateL rsi_jsvc sR sL (rsi_hs_jsvc sR sL Hs)
        arrR arrL Harr tR tL Ht)).
    imp (ar_bool_truth_correspondence _ _ (rien_backlogged_rel sR sL Hs jrR jrL Hjr j tR tL Ht)).
    imp (ar_bool_truth_correspondence _ _
      (PPC.pp_scheduled_at_related Job PStateR PStateL rsi_jsvc sR sL (rsi_hs_jsvc sR sL Hs) j_hp tR tL Ht)).
    exact (ar_bool_truth_correspondence _ _ (Hp j_hp j)).
  Qed.

  (** *** The four search-space definitions (restating the accepted restricted-supply EDF search-space definition
      certificate, with the priority-inversion bound in place of the blocking bound) *)

  Lemma rien_decide_not (P : SProp) (d : I.Decidable P) :
    Lean.eq (I.Decidable_decide (I.Not P) (I.instDecidableNot P d))
      (I.Bool_not (I.Decidable_decide P d)).
  Proof. destruct d; exact (@Lean.eq_refl _ _). Qed.

  Lemma rien_nat_neqb_related aR aL bR bL :
    SubNatRel aR aL -> SubNatRel bR bL ->
    SvcBoolRel (aR != bR)
      (I.Decidable_decide (I.Ne Lean.Nat aL bL)
        (I.instDecidableNot (Lean.eq aL bL) (I.instDecidableEqNat aL bL))).
  Proof.
    intros Ha Hb. unfold SvcBoolRel.
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (rien_decide_not _ _))).
    exact (svc_bool_not_related _ _ (svc_decide_eq_related _ _ _ _ Ha Hb)).
  Qed.

  Section RienAny.
    Context (X : Type).
    Variable PR : X -> bool.
    Variable PL : X -> I.Bool.
    Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).

    Lemma rien_has_canonical (xs : seq X) :
      ArBoolRel (has PR xs) (I.List_any X (ar_list_to_imported xs) PL).
    Proof.
      induction xs as [|x xs IH].
      - exact (sub_imported_eq_sym _ _
          (I.Prosa_Validation_SearchSpaceEdfInterface_production_any_nil X PL)).
      - cbn [has ar_list_to_imported].
        refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
          (I.Prosa_Validation_SearchSpaceEdfInterface_production_any_cons
            X PL x (ar_list_to_imported xs)))).
        exact (PPC.pp_bool_or_related _ _ _ _ (HP x) IH).
    Qed.

    Lemma rien_has_related (xsR : seq X) (xsL : I.List X) :
      ArListRel xsR xsL -> ArBoolRel (has PR xsR) (I.List_any X xsL PL).
    Proof.
      intro Hxs.
      exact (sub_imported_eq_trans _ _ _ (rien_has_canonical xsR)
        (sub_imported_eq_congr (fun l => I.List_any X l PL) _ _ Hxs)).
    Qed.
  End RienAny.

  Lemma rien_bpi_task_rbf_changes_rel maR maL (Hma : IbtMaxArrivalsRel Task maR maL) (tsk : Task)
      (AR : nat) (AL : Lean.Nat) :
    SubNatRel AR AL ->
    SvcBoolRel (@BPI.task_rbf_changes_at Task tcR maR tsk AR)
      (I.Prosa_Results_Rta_Ideal_Edf_BoundedPi_task_rbf_changes_at Task dT tcL maL tsk AL).
  Proof.
    intro HA. unfold BPI.task_rbf_changes_at.
    cbn [I.Prosa_Results_Rta_Ideal_Edf_BoundedPi_task_rbf_changes_at].
    exact (rien_nat_neqb_related _ _ _ _
      (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _ HA)
      (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
        (svc_target_add_related _ _ _ _ HA (sub_nat_rel_canonical (S O))))).
  Qed.

  Lemma rien_bpi_bound_changes_rel tsR tsL (Hts : ArListRel tsR tsL)
      maR maL (Hma : IbtMaxArrivalsRel Task maR maL) (tsk : Task) (AR : nat) (AL : Lean.Nat) :
    SubNatRel AR AL ->
    SvcBoolRel (@BPI.bound_on_total_hep_workload_changes_at Task tcR tdR tsR maR tsk AR)
      (I.Prosa_Results_Rta_Ideal_Edf_BoundedPi_bound_on_total_hep_workload_changes_at
        Task dT tcL tdL tsL maL tsk AL).
  Proof.
    intro HA. unfold BPI.bound_on_total_hep_workload_changes_at.
    cbn [I.Prosa_Results_Rta_Ideal_Edf_BoundedPi_bound_on_total_hep_workload_changes_at].
    apply rien_has_related; [|exact Hts]. intro tsko.
    exact (ar_bool_and_related _ _ _ _ (wl_ne_observation Task tsk tsko)
      (rien_nat_neqb_related _ _ _ _
        (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsko _ _
          (svc_target_sub_related _ _ _ _ (svc_target_add_related _ _ _ _ HA (Htd tsk)) (Htd tsko)))
        (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsko _ _
          (svc_target_sub_related _ _ _ _
            (svc_target_add_related _ _ _ _ (svc_target_add_related _ _ _ _ HA (sub_nat_rel_canonical (S O)))
              (Htd tsk)) (Htd tsko))))).
  Qed.

  Lemma rien_bpi_pi_changes_rel pR pL (Hp : RienFunRel pR pL) (AR : nat) (AL : Lean.Nat) :
    SubNatRel AR AL ->
    SvcBoolRel (@BPI.priority_inversion_changes_at pR AR)
      (I.Prosa_Results_Rta_Ideal_Edf_BoundedPi_priority_inversion_changes_at pL AL).
  Proof.
    intro HA. unfold BPI.priority_inversion_changes_at.
    cbn [I.Prosa_Results_Rta_Ideal_Edf_BoundedPi_priority_inversion_changes_at].
    exact (rien_nat_neqb_related _ _ _ _ (Hp _ _ (svc_target_sub_related _ _ _ _ HA (sub_nat_rel_canonical (S O))))
      (Hp _ _ HA)).
  Qed.

  Lemma rien_bpi_is_in_search_space_rel tsR tsL (Hts : ArListRel tsR tsL)
      maR maL (Hma : IbtMaxArrivalsRel Task maR maL) (tsk : Task) pR pL (Hp : RienFunRel pR pL)
      (LR AR : nat) (LL AL : Lean.Nat) :
    SubNatRel LR LL -> SubNatRel AR AL ->
    SvcBoolRel (@BPI.is_in_search_space Task tcR tdR tsR maR tsk pR LR AR)
      (I.Prosa_Results_Rta_Ideal_Edf_BoundedPi_is_in_search_space Task dT tcL tdL tsL maL tsk pL LL AL).
  Proof.
    intros HL HA. unfold BPI.is_in_search_space.
    cbn [I.Prosa_Results_Rta_Ideal_Edf_BoundedPi_is_in_search_space].
    refine (ar_bool_and_related _ _ _ _ (svc_decide_lt_related _ _ _ _ HA HL) _).
    refine (PPC.pp_bool_or_related _ _ _ _ (PPC.pp_bool_or_related _ _ _ _ _ _) _).
    - exact (rien_bpi_pi_changes_rel pR pL Hp AR AL HA).
    - exact (rien_bpi_task_rbf_changes_rel maR maL Hma tsk AR AL HA).
    - exact (rien_bpi_bound_changes_rel tsR tsL Hts maR maL Hma tsk AR AL HA).
  Qed.

  Lemma rien_forall_jp (PR : PP.JobPreemptable Job -> Prop)
      (PL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ -> SProp) :
    (forall jpR jpL, PPC.PpJobPreemptableRel Job jpR jpL -> PropSPropRel (PR jpR) (PL jpL)) ->
    PropSPropRel (forall jp, PR jp) (forall jp, PL jp).
  Proof.
    exact (arta_forall_cover _ _ (PPC.PpJobPreemptableRel Job)
      (fun jpR => I.Prosa_Model_Preemption_Parameter_JobPreemptable_mk Job dJ
        (fun j nL => ar_bool_to_imported (jpR j (sub_nat_to_rocq nL))))
      (fun jpL => ((fun j n => ar_bool_to_rocq
        (I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job dJ jpL j
          (sub_nat_to_imported n))) : PP.JobPreemptable Job))
      (PPC.JobPreemptable_source_total Job) (PPC.JobPreemptable_target_total Job) PR PL).
  Qed.

  (** *** Conditional maxima (replayed from the accepted busy-interval priority-inversion certificate) *)

  Section RienBigMax.
    Context (X : Type).
    Variable PR : X -> bool.
    Variable PL : X -> I.Bool.
    Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).
    Variable FR : X -> nat.
    Variable FL : X -> Lean.Nat.
    Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

    Lemma rien_bigmax_canonical (xs : seq X) :
      SubNatRel (\max_(x <- xs | PR x) FR x)
        (I.Prosa_Util_Minmax_bigMaxListCond X (ar_list_to_imported xs) PL FL).
    Proof.
      induction xs as [|x xs IH].
      - rewrite big_nil.
        exact (sub_imported_eq_sym _ _
          (I.Prosa_Validation_PiInterface_production_bigMaxListCond_nil X PL FL)).
      - rewrite big_cons. cbn [ar_list_to_imported].
        have Hx := HP x. unfold ArBoolRel in Hx.
        destruct (PR x).
        + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
            (I.Prosa_Validation_PiInterface_production_bigMaxListCond_cons_true
              X PL FL x (ar_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
          refine (sub_imported_eq_trans _ _ _
            (sub_imported_eq_sym _ _ (PPC.pp_max_canonical (FR x) (\max_(y <- xs | PR y) FR y))) _).
          exact (sub_imported_eq_congr2 I.Nat_max _ _ _ _ (HF x) IH).
        + refine (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
            (I.Prosa_Validation_PiInterface_production_bigMaxListCond_cons_false
              X PL FL x (ar_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
    Qed.

    Lemma rien_bigmax_related (xsR : seq X) (xsL : I.List X) :
      ArListRel xsR xsL ->
      SubNatRel (\max_(x <- xsR | PR x) FR x) (I.Prosa_Util_Minmax_bigMaxListCond X xsL PL FL).
    Proof.
      intro Hxs.
      exact (sub_imported_eq_trans _ _ _ (rien_bigmax_canonical xsR)
        (sub_imported_eq_congr (fun l => I.Prosa_Util_Minmax_bigMaxListCond X l PL FL) _ _ Hxs)).
    Qed.
  End RienBigMax.

  (** *** The EDF blocking bound (the accepted blocking-bound definition certificate, restated over the conditional
      maximum above) *)

  Variable mR : TPP.TaskMaxNonpreemptiveSegment Task.
  Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
  Hypothesis Hm : TPPC.TppMaxSegmentRel Task mR mL.

  Lemma rien_blocking_relevant_rel maR maL (Hma : IbtMaxArrivalsRel Task maR maL) (tsk : Task) :
    ArBoolRel (@BBES.blocking_relevant Task tcR maR tsk)
      (I.Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_relevant Task dT tcL maL tsk).
  Proof.
    unfold BBES.blocking_relevant.
    cbn [I.Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_relevant].
    apply ar_bool_and_related.
    - exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hma tsk _ _ (sub_nat_rel_canonical 1))).
    - exact (ar_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Htc tsk)).
  Qed.

  Lemma rien_blocking_bound_rel tsR tsL (Hts : ArListRel tsR tsL) maR maL (Hma : IbtMaxArrivalsRel Task maR maL)
      (tsk : Task) (AR : nat) (AL : Lean.Nat) :
    SubNatRel AR AL ->
    SubNatRel (@BBES.blocking_bound Task tcR tdR mR tsR maR tsk AR)
      (I.Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task dT tcL tdL mL tsL maL tsk AL).
  Proof.
    intro HA. unfold BBES.blocking_bound.
    cbn [I.Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound].
    apply rien_bigmax_related; [| |exact Hts].
    - intro tsk_o. apply ar_bool_and_related.
      + exact (rien_blocking_relevant_rel maR maL Hma tsk_o).
      + exact (ar_decide_lt_related _ _ _ _ (svc_target_add_related _ _ _ _ (Htd tsk) HA) (Htd tsk_o)).
    - intro tsk_o. exact (svc_target_sub_related _ _ _ _ (Hm tsk_o) (sub_nat_rel_canonical 1)).
  Qed.

  (** *** The search-space definition of this file *)

  Theorem is_in_search_space_correspondence tsR tsL (Hts : ArListRel tsR tsL)
      maR maL (Hma : IbtMaxArrivalsRel Task maR maL) (tsk : Task) (LR AR : nat) (LL AL : Lean.Nat) :
    SubNatRel LR LL -> SubNatRel AR AL ->
    SvcBoolRel (@S2.is_in_search_space Task tcR tdR tsR maR tsk LR AR)
      (I.Prosa_Results_Rta_Ideal_Edf_BoundedNps_is_in_search_space Task dT tcL tdL tsL maL tsk LL AL).
  Proof.
    intros HL HA. unfold S2.is_in_search_space.
    cbn [I.Prosa_Results_Rta_Ideal_Edf_BoundedNps_is_in_search_space].
    refine (ar_bool_and_related _ _ _ _ (svc_decide_lt_related _ _ _ _ HA HL) _).
    exact (PPC.pp_bool_or_related _ _ _ _ (rien_bpi_task_rbf_changes_rel maR maL Hma tsk AR AL HA)
      (rien_bpi_bound_changes_rel tsR tsL Hts maR maL Hma tsk AR AL HA)).
  Qed.

  (** *** blocking_bound_decreasing *)

  Definition src_blocking_bound_decreasing : Prop :=
    ltac:(body_of (fun s : S2.statement_blocking_bound_decreasing => s Task tcR tdR mR)).
  Definition tgt_blocking_bound_decreasing : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Edf_BoundedNps_blocking_bound_decreasing Task dT tcL tdL mL)).

  Theorem blocking_bound_decreasing_correspondence :
    PropSPropRel src_blocking_bound_decreasing tgt_blocking_bound_decreasing.
  Proof.
    unfold src_blocking_bound_decreasing, tgt_blocking_bound_decreasing.
    apply arta_forall_list. intros tsR tsL Hts.
    apply ibt_forall_ma. intros maR maL Hma.
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply ad_forall_nat_correspondence => A1R A1L H1.
    apply ad_forall_nat_correspondence => A2R A2L H2.
    imp (sub_nat_le_correspondence _ _ _ _ H1 H2).
    exact (sub_nat_le_correspondence _ _ _ _ (rien_blocking_bound_rel tsR tsL Hts maR maL Hma tsk _ _ H2)
      (rien_blocking_bound_rel tsR tsL Hts maR maL Hma tsk _ _ H1)).
  Qed.

  (** *** task_with_equal_deadline_exists *)

  Definition src_task_with_equal_deadline_exists : Prop :=
    ltac:(body_of (fun s : S2.statement_task_with_equal_deadline_exists => s Task tcR tdR mR)).
  Definition tgt_task_with_equal_deadline_exists : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Results_Rta_Ideal_Edf_BoundedNps_task_with_equal_deadline_exists Task dT tcL tdL mL)).

  Theorem task_with_equal_deadline_exists_correspondence :
    PropSPropRel src_task_with_equal_deadline_exists tgt_task_with_equal_deadline_exists.
  Proof.
    unfold src_task_with_equal_deadline_exists, tgt_task_with_equal_deadline_exists.
    apply arta_forall_list. intros tsR tsL Hts.
    apply ibt_forall_ma. intros maR maL Hma.
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply ad_forall_nat_correspondence => AR AL HA.
    imp (ad_bool_truth_correspondence _ _ (rien_bpi_pi_changes_rel _ _
      (fun nR nL Hn => rien_blocking_bound_rel tsR tsL Hts maR maL Hma tsk nR nL Hn) AR AL HA)).
    apply rsi_exists_identity. intro tsk_o.
    apply ad_bool_truth_correspondence.
    apply ar_bool_and_related; [apply ar_bool_and_related; [apply ar_bool_and_related|]|].
    - exact (ar_decide_mem_related Task tsk_o _ _ Hts).
    - exact (rien_blocking_relevant_rel maR maL Hma tsk_o).
    - exact (wl_ne_observation Task tsk_o tsk).
    - exact (svc_decide_eq_related _ _ _ _ (Htd tsk_o) (svc_target_add_related _ _ _ _ (Htd tsk) HA)).
  Qed.

  (** *** search_space_inclusion *)

  Definition src_search_space_inclusion : Prop :=
    ltac:(body_of (fun s : S2.statement_search_space_inclusion => s Task tcR tdR mR)).
  Definition tgt_search_space_inclusion : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Edf_BoundedNps_search_space_inclusion Task dT tcL tdL mL)).

  Theorem search_space_inclusion_correspondence :
    PropSPropRel src_search_space_inclusion tgt_search_space_inclusion.
  Proof.
    unfold src_search_space_inclusion, tgt_search_space_inclusion.
    apply arta_forall_list. intros tsR tsL Hts.
    apply ibt_forall_ma. intros maR maL Hma.
    imp (rien_valid_taskset_curve_rel tsR tsL Hts maR maL Hma).
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply ad_forall_nat_correspondence => AR AL HA.
    apply ad_forall_nat_correspondence => LR LL HL.
    imp (ad_bool_truth_correspondence _ _ (rien_bpi_is_in_search_space_rel tsR tsL Hts maR maL Hma tsk _ _
      (fun nR nL Hn => rien_blocking_bound_rel tsR tsL Hts maR maL Hma tsk nR nL Hn) LR AR LL AL HL HA)).
    exact (ad_bool_truth_correspondence _ _ (is_in_search_space_correspondence tsR tsL Hts maR maL Hma tsk
      LR AR LL AL HL HA)).
  Qed.

  (** *** uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments *)

  Variable rtcR : TPP.TaskRunToCompletionThreshold Task.
  Variable rtcL : I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task dT.
  Hypothesis Hrtc : forall tsk : Task,
    SubNatRel (@TPP.task_rtct Task rtcR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task dT rtcL tsk).

  Definition src_uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments : Prop :=
    ltac:(body_of (fun s : S2.statement_uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments =>
      s Task tcR tdR rtcR mR Job jtR jaR costR)).
  Definition tgt_uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Results_Rta_Ideal_Edf_BoundedNps_uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
        Task dT Job dJ tcL tdL rtcL mL jtL jaL costL)).

  Theorem uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments_correspondence :
    PropSPropRel src_uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
      tgt_uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments.
  Proof.
    unfold src_uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments,
      tgt_uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments.
    apply rsi_forall_arr. intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply rsi_forall_sched. intros sR sL Hs.
    have Hjr := rien_basic_ready_at sR sL Hs.
    imp (rsi_valid_schedule_rel sR sL Hs arrR arrL Harr _ _ Hjr).
    apply rien_forall_jp. intros jpR jpL Hjp.
    imp (TPPC.valid_model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt
      costR costL Hcost mR mL Hm jpR jpL Hjp arrR arrL Harr PStateR PStateL rsi_jsvc sR sL (rsi_hs_jsvc sR sL Hs)).
    imp (rsi_work_conserving_related sR sL Hs arrR arrL Harr _ _ Hjr).
    imp (rien_respects_jlfp_rel sR sL Hs arrR arrL Harr jpR jpL Hjp _ _ Hjr _ _ rien_edf_rel).
    apply arta_forall_list. intros tsR tsL Hts.
    imp (rien_all_jobs_from_taskset_rel arrR arrL Harr tsR tsL Hts).
    imp (arta_valid_job_costs_rel Task Job tcR tcL Htc jtR jtL Hjt costR costL Hcost arrR arrL Harr).
    apply ibt_forall_ma. intros maR maL Hma.
    imp (rien_valid_taskset_curve_rel tsR tsL Hts maR maL Hma).
    imp (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma).
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    imp (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL rsi_jsvc
      sR sL (rsi_hs_jsvc sR sL Hs) arrR arrL Harr).
    imp (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rtcR rtcL Hrtc
      jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk).
    apply ad_forall_nat_correspondence => LR LL HL.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    imp (sub_nat_eq_correspondence _ _ _ _ HL
      (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts LR LL HL)).
    apply ad_forall_nat_correspondence => RR RL HR.
    apply ad_imp_correspondence.
    { apply ad_forall_nat_correspondence => AR AL HA.
      imp (ad_bool_truth_correspondence _ _ (is_in_search_space_correspondence tsR tsL Hts maR maL Hma tsk
        LR AR LL AL HL HA)).
      apply ad_exists_nat_correspondence => FR FL HF.
      have HAF := arta_add_related _ _ _ _ HA HF.
      have Hcr := arta_sub_related _ _ _ _ (Htc tsk) (Hrtc tsk).
      apply ad_and_correspondence.
      - exact (sub_nat_le_correspondence _ _ _ _ (arta_add_related _ _ _ _ (arta_add_related _ _ _ _
          (rien_blocking_bound_rel tsR tsL Hts maR maL Hma tsk _ _ HA)
          (arta_sub_related _ _ _ _ (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
            (arta_add_related _ _ _ _ HA (sub_nat_rel_canonical 1))) Hcr))
          (EABC.bound_on_athep_workload_correspondence Task tcR tcL Htc tdR tdL Htd maR maL Hma tsR tsL Hts tsk
            _ _ _ _ HA HAF)) HAF).
      - exact (sub_nat_le_correspondence _ _ _ _ (arta_add_related _ _ _ _ HF Hcr) HR). }
    exact (arta_response_time_bound_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL Hcost
      sR sL Hs arrR arrL Harr tsk RR RL HR).
  Qed.
End IdealIwInstantiation.
