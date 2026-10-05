(* Main certificate: generated from the ideal-specific statement correspondences and the helper part of the accepted
   certificates/analysis_abstract_restricted_supply_iw_instantiation/RsIwInstantiationCorrespondence.v (generator
   gen_idl_main.py), replayed at the ideal processor-model universe instance of this export by the processor-model
   replay tool (every imported constant with a universe-specialised copy renamed to it; chain modules as their Idl
   copies).  The processor-state relation is the concrete ideal one of IdlStateRel.v; the restricted-supply-only
   helper rsi_unit_supply_rel is not generated. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import IdealIwInstantiationSemanticSource.
From prosa Require Import analysis.abstract.definitions model.job.properties
  model.processor.platform_properties model.processor.supply model.schedule.work_conserving
  analysis.definitions.work_bearing_readiness model.processor.ideal.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdealIwInstantiation ImportedSubadditivity.
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
  IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence.
From FoundationCertificates Require Import IdlIbfTaskFullHelpers IdlStateRel.
From FoundationCertificates Require Import IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence.

Module I := ImportedIdealIwInstantiation.
Module S := IdealIwInstantiationSemanticSource.IdealIwInstantiationSemanticSource.
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

(** Statement correspondences for [analysis/abstract/ideal/iw_instantiation.v].

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

  Lemma rsi_policy_respects_sequential_rel pR pL (Hp : RsiJLFPRel pR pL) :
    PropSPropRel (@prosa.model.priority.definitions.policy_respects_sequential_tasks Task Job jtR jaR pR)
      (I.Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks Task dT Job dJ jtL jaL pL).
  Proof.
    unfold prosa.model.priority.definitions.policy_respects_sequential_tasks.
    cbn [I.Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (IFC.if_eq_transport Task _ _ _ _ (Hjt j1) (Hjt j2)))|].
    apply ar_imp_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
    exact (ar_bool_truth_correspondence _ _ (Hp j1 j2)).
  Qed.

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
        Let IL := I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job dJ arrL sL pL.
        Let WR := @S.ideal_jlfp_interfering_workload Job costR arrR sR pR.
        Let WL := I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload
          Job dJ costL arrL sL pL.

        Lemma rsi_priority_inversion_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
          ArBoolRel (@PIS.priority_inversion Job PStateR arrR sR pR j tR)
            (I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_inst4 Job dJ PStateL arrL sL pL j tL).
        Proof.
          exact (PIC.priority_inversion_correspondence Job PStateR PStateL rsi_jsvc arrR arrL Harr sR sL
            (rsi_hs_jsvc sR sL Hs) pR pL Hp j tR tL Ht).
        Qed.

        Lemma rsi_interference_rel : AdInterferenceRel Job IR IL.
        Proof.
          intros j t. unfold AdBoolRel, IR, IL.
          cbn [I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference
            I.Prosa_Analysis_Abstract_Definitions_Interference_interference].
          have Ht := sub_nat_rel_canonical t.
          apply IFC.if_bool_or_related.
          - exact (rsi_priority_inversion_related j _ _ Ht).
          - exact (IFC.another_hep_job_interference_correspondence Job PStateR PStateL rsi_jsvc sR sL
              (rsi_hs_jsvc sR sL Hs) arrR arrL Harr pR pL Hp j _ _ Ht).
        Qed.

        Lemma rsi_workload_rel : AdInterferingWorkloadRel Job WR WL.
        Proof.
          intros j t. unfold WR, WL.
          cbn [I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload
            I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload_interfering_workload].
          have Ht := sub_nat_rel_canonical t.
          apply arta_add_related.
          - exact (ad_bool_to_nat_related _ _ (rsi_priority_inversion_related j _ _ Ht)).
          - exact (IFC.other_hep_jobs_interfering_workload_correspondence Job costR costL Hcost arrR arrL Harr
              pR pL Hp j _ _ Ht).
        Qed.

        Lemma rsi_interference_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
          AdBoolRel (@prosa.analysis.abstract.definitions.interference Job IR j tR)
            (I.Prosa_Analysis_Abstract_Definitions_Interference_interference Job dJ IL j tL).
        Proof. destruct Ht. exact (rsi_interference_rel j tR). Qed.

        (** **** Classical busy intervals (replayed from the accepted existence helpers) *)

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

        Lemma rsi_ab_quiet_time_related (j : Job) (tR : nat) (tL : Lean.Nat) :
          SubNatRel tR tL ->
          AdBoolRel (@prosa.analysis.abstract.definitions.quiet_time Job jaR costR PStateR sR IR WR j tR)
            (I.Prosa_Analysis_Abstract_Definitions_quiet_time_inst4 Job dJ IL WL jaL costL PStateL sL j tL).
        Proof.
          exact (ad_quiet_time_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
            IR IL rsi_interference_rel WR WL rsi_workload_rel j tR tL).
        Qed.

        Lemma rsi_ab_busy_interval_prefix_related (j : Job) t1R t1L t2R t2L :
          SubNatRel t1R t1L -> SubNatRel t2R t2L ->
          PropSPropRel (@prosa.analysis.abstract.definitions.busy_interval_prefix Job jaR costR PStateR sR IR WR
              j t1R t2R)
            (I.Prosa_Analysis_Abstract_Definitions_busy_interval_prefix_inst4 Job dJ IL WL jaL costL PStateL sL
              j t1L t2L).
        Proof.
          exact (ad_busy_interval_prefix_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL
            Hcost IR IL rsi_interference_rel WR WL rsi_workload_rel j t1R t2R t1L t2L).
        Qed.

        Lemma rsi_ab_busy_interval_related (j : Job) t1R t1L t2R t2L :
          SubNatRel t1R t1L -> SubNatRel t2R t2L ->
          PropSPropRel (@prosa.analysis.abstract.definitions.busy_interval Job jaR costR PStateR sR IR WR
              j t1R t2R)
            (I.Prosa_Analysis_Abstract_Definitions_busy_interval_inst4 Job dJ IL WL jaL costL PStateL sL
              j t1L t2L).
        Proof.
          exact (ad_busy_interval_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL
            Hcost IR IL rsi_interference_rel WR WL rsi_workload_rel j t1R t2R t1L t2L).
        Qed.

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

  (** *** IdleSchedule *)

  Definition src_no_interference_when_idle : Prop :=
    ltac:(body_of (fun s : S.statement_no_interference_when_idle => s Job jaR)).
  Definition tgt_no_interference_when_idle : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_no_interference_when_idle Job dJ jaL)).

  Theorem no_interference_when_idle_correspondence :
    PropSPropRel src_no_interference_when_idle tgt_no_interference_when_idle.
  Proof.
    unfold src_no_interference_when_idle, tgt_no_interference_when_idle.
    rsi_arr_sched arrR arrL Harr sR sL Hs.
    apply rsi_forall_jlfp. intros pR pL Hp.
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (idl_idle_related sR sL Hs tR tL Ht))|].
    apply ad_forall_identity_correspondence. intro j.
    exact (ad_bool_truth_correspondence _ _ (svc_bool_not_related _ _
      (rsi_interference_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht))).
  Qed.

  Definition src_no_task_interference_when_idle : Prop :=
    ltac:(body_of (fun s : S.statement_no_task_interference_when_idle => s Task Job jtR jaR)).
  Definition tgt_no_task_interference_when_idle : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_no_task_interference_when_idle Task dT Job dJ jtL jaL)).

  Theorem no_task_interference_when_idle_correspondence :
    PropSPropRel src_no_task_interference_when_idle tgt_no_task_interference_when_idle.
  Proof.
    unfold src_no_task_interference_when_idle, tgt_no_task_interference_when_idle.
    rsi_arr_sched arrR arrL Harr sR sL Hs.
    apply rsi_forall_jlfp. intros pR pL Hp.
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (idl_idle_related sR sL Hs tR tL Ht))|].
    apply ad_forall_identity_correspondence. intro j.
    exact (ad_bool_truth_correspondence _ _ (svc_bool_not_related _ _
      (task_interference_correspondence Task Job PStateR PStateL R jtR jtL Hjt sR sL Hs arrR arrL Harr _ _
        (rsi_interference_rel sR sL Hs arrR arrL Harr pR pL Hp) j _ _ Ht))).
  Qed.

  (** *** ScheduledJob *)

  Definition src_task_interference_eq_false : Prop :=
    ltac:(body_of (fun s : S.statement_task_interference_eq_false => s Task Job jtR jaR)).
  Definition tgt_task_interference_eq_false : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_task_interference_eq_false Task dT Job dJ jtL jaL)).

  Theorem task_interference_eq_false_correspondence :
    PropSPropRel src_task_interference_eq_false tgt_task_interference_eq_false.
  Proof.
    unfold src_task_interference_eq_false, tgt_task_interference_eq_false.
    rsi_arr_sched arrR arrL Harr sR sL Hs.
    apply rsi_forall_jlfp. intros pR pL Hp.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_forall_identity_correspondence. intro j'.
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j' Hjt))|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ibt_sched_at Job PStateR PStateL R sR sL Hs j' _ _ Ht))|].
    exact (ad_bool_truth_correspondence _ _ (svc_bool_not_related _ _
      (task_interference_correspondence Task Job PStateR PStateL R jtR jtL Hjt sR sL Hs arrR arrL Harr _ _
        (rsi_interference_rel sR sL Hs arrR arrL Harr pR pL Hp) j _ _ Ht))).
  Qed.

  Definition src_sched_athep_implies_task_interference : Prop :=
    ltac:(body_of (fun s : S.statement_sched_athep_implies_task_interference => s Task Job jtR jaR)).
  Definition tgt_sched_athep_implies_task_interference : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_sched_athep_implies_task_interference Task dT Job dJ jtL jaL)).

  Theorem sched_athep_implies_task_interference_correspondence :
    PropSPropRel src_sched_athep_implies_task_interference tgt_sched_athep_implies_task_interference.
  Proof.
    unfold src_sched_athep_implies_task_interference, tgt_sched_athep_implies_task_interference.
    rsi_arr_sched arrR arrL Harr sR sL Hs.
    apply rsi_forall_jlfp. intros pR pL Hp.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_forall_identity_correspondence. intro j'.
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (ad_job_of_task_related Job Task jtR jtL tsk j' Hjt)))|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ibt_sched_at Job PStateR PStateL R sR sL Hs j' _ _ Ht))|].
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (Hp j' j))|].
    exact (ad_bool_truth_correspondence _ _
      (task_interference_correspondence Task Job PStateR PStateL R jtR jtL Hjt sR sL Hs arrR arrL Harr _ _
        (rsi_interference_rel sR sL Hs arrR arrL Harr pR pL Hp) j _ _ Ht)).
  Qed.

  (** *** Cumulative splits *)

  Definition src_cumulative_interference_split : Prop :=
    ltac:(body_of (fun s : S.statement_cumulative_interference_split => s Job jaR)).
  Definition tgt_cumulative_interference_split : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_cumulative_interference_split Job dJ jaL)).

  Theorem cumulative_interference_split_correspondence :
    PropSPropRel src_cumulative_interference_split tgt_cumulative_interference_split.
  Proof.
    unfold src_cumulative_interference_split, tgt_cumulative_interference_split.
    rsi_arr_sched arrR arrL Harr sR sL Hs. rsi_jlfp pR pL Hp.
    apply ad_forall_identity_correspondence. intro j.
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    apply sub_nat_eq_correspondence.
    - exact (cumulative_interference_correspondence Job _ _ j _ _ _ _
        (rsi_interference_rel sR sL Hs arrR arrL Harr pR pL Hp) H1 H2).
    - apply arta_add_related.
      + exact (PIC.cumulative_priority_inversion_correspondence Job PStateR PStateL rsi_jsvc arrR arrL Harr sR sL
          (rsi_hs_jsvc sR sL Hs) pR pL Hp j _ _ _ _ H1 H2).
      + exact (IFC.cumulative_another_hep_job_interference_correspondence Job PStateR PStateL rsi_jsvc sR sL
          (rsi_hs_jsvc sR sL Hs) arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2).
  Qed.

  Definition src_cumulative_interfering_workload_split : Prop :=
    ltac:(body_of (fun s : S.statement_cumulative_interfering_workload_split => s Job costR)).
  Definition tgt_cumulative_interfering_workload_split : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_cumulative_interfering_workload_split Job dJ costL)).

  Theorem cumulative_interfering_workload_split_correspondence :
    PropSPropRel src_cumulative_interfering_workload_split tgt_cumulative_interfering_workload_split.
  Proof.
    unfold src_cumulative_interfering_workload_split, tgt_cumulative_interfering_workload_split.
    apply rsi_forall_arr. intros arrR arrL Harr.
    apply rsi_forall_sched. intros sR sL Hs.
    apply rsi_forall_jlfp. intros pR pL Hp.
    apply ad_forall_identity_correspondence. intro j.
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    apply sub_nat_eq_correspondence.
    - exact (cumulative_interfering_workload_correspondence Job _ _
        (rsi_workload_rel sR sL Hs arrR arrL Harr pR pL Hp) j _ _ _ _ H1 H2).
    - apply arta_add_related.
      + exact (PIC.cumulative_priority_inversion_correspondence Job PStateR PStateL rsi_jsvc arrR arrL Harr sR sL
          (rsi_hs_jsvc sR sL Hs) pR pL Hp j _ _ _ _ H1 H2).
      + exact (IFC.cumulative_other_hep_jobs_interfering_workload_correspondence Job costR costL Hcost
          arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2).
  Qed.

  Definition src_cumulative_task_interference_split : Prop :=
    ltac:(body_of (fun s : S.statement_cumulative_task_interference_split => s Task Job jtR jaR costR)).
  Definition tgt_cumulative_task_interference_split : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_cumulative_task_interference_split
        Task dT Job dJ jtL jaL costL)).

  Theorem cumulative_task_interference_split_correspondence :
    PropSPropRel src_cumulative_task_interference_split tgt_cumulative_task_interference_split.
  Proof.
    unfold src_cumulative_task_interference_split, tgt_cumulative_task_interference_split.
    rsi_arr_sched arrR arrL Harr sR sL Hs. rsi_jlfp pR pL Hp.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_forall_identity_correspondence. intro j.
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j Harr)|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (ibt_completed Job PStateR PStateL R costR costL Hcost sR sL Hs j _ _ H2)))|].
    apply sub_nat_le_correspondence.
    - exact (cumul_task_interference_correspondence Task Job PStateR PStateL R jtR jtL Hjt sR sL Hs arrR arrL Harr
        _ _ (rsi_interference_rel sR sL Hs arrR arrL Harr pR pL Hp) j _ _ _ _ H1 H2).
    - apply arta_add_related.
      + exact (PIC.cumulative_priority_inversion_correspondence Job PStateR PStateL rsi_jsvc arrR arrL Harr sR sL
          (rsi_hs_jsvc sR sL Hs) pR pL Hp j _ _ _ _ H1 H2).
      + exact (IFC.cumulative_another_task_hep_job_interference_correspondence Task Job jtR jtL Hjt
          PStateR PStateL rsi_jsvc sR sL (rsi_hs_jsvc sR sL Hs) arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2).
  Qed.

  Definition src_cumulative_iw_hep_eq_workload_of_ohep : Prop :=
    ltac:(body_of (fun s : S.statement_cumulative_iw_hep_eq_workload_of_ohep => s Job costR)).
  Definition tgt_cumulative_iw_hep_eq_workload_of_ohep : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_cumulative_iw_hep_eq_workload_of_ohep
      Job dJ costL)).

  Theorem cumulative_iw_hep_eq_workload_of_ohep_correspondence :
    PropSPropRel src_cumulative_iw_hep_eq_workload_of_ohep tgt_cumulative_iw_hep_eq_workload_of_ohep.
  Proof.
    unfold src_cumulative_iw_hep_eq_workload_of_ohep, tgt_cumulative_iw_hep_eq_workload_of_ohep.
    apply rsi_forall_arr. intros arrR arrL Harr.
    apply rsi_forall_jlfp. intros pR pL Hp.
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    apply ad_forall_identity_correspondence. intro j.
    apply sub_nat_eq_correspondence.
    - exact (IFC.cumulative_other_hep_jobs_interfering_workload_correspondence Job costR costL Hcost
        arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2).
    - exact (workload_of_other_hep_jobs_correspondence Job costR costL Hcost arrR arrL Harr pR pL Hp
        j _ _ _ _ H1 H2).
  Qed.

  (** *** Busy-interval equivalences *)

  Definition src_quiet_time_cl_implies_quiet_time_ab : Prop :=
    ltac:(body_of (fun s : S.statement_quiet_time_cl_implies_quiet_time_ab => s Job jaR costR)).
  Definition tgt_quiet_time_cl_implies_quiet_time_ab : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_quiet_time_cl_implies_quiet_time_ab
      Job dJ jaL costL)).

  Theorem quiet_time_cl_implies_quiet_time_ab_correspondence :
    PropSPropRel src_quiet_time_cl_implies_quiet_time_ab tgt_quiet_time_cl_implies_quiet_time_ab.
  Proof.
    unfold src_quiet_time_cl_implies_quiet_time_ab, tgt_quiet_time_cl_implies_quiet_time_ab.
    idl_full arrR arrL Harr sR sL Hs pR pL Hp.
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j Harr)|].
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_imp_correspondence; [exact (rsi_quiet_time_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht)|].
    exact (ad_bool_truth_correspondence _ _ (rsi_ab_quiet_time_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht)).
  Qed.

  Definition src_quiet_time_ab_implies_quiet_time_cl : Prop :=
    ltac:(body_of (fun s : S.statement_quiet_time_ab_implies_quiet_time_cl => s Job jaR costR)).
  Definition tgt_quiet_time_ab_implies_quiet_time_cl : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_quiet_time_ab_implies_quiet_time_cl
      Job dJ jaL costL)).

  Theorem quiet_time_ab_implies_quiet_time_cl_correspondence :
    PropSPropRel src_quiet_time_ab_implies_quiet_time_cl tgt_quiet_time_ab_implies_quiet_time_cl.
  Proof.
    unfold src_quiet_time_ab_implies_quiet_time_cl, tgt_quiet_time_ab_implies_quiet_time_cl.
    idl_full arrR arrL Harr sR sL Hs pR pL Hp.
    idl_j_pos arrR arrL Harr j.
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (rsi_ab_quiet_time_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht))|].
    exact (rsi_quiet_time_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht).
  Qed.

  Definition src_instantiated_quiet_time_equivalent_quiet_time : Prop :=
    ltac:(body_of (fun s : S.statement_instantiated_quiet_time_equivalent_quiet_time => s Job jaR costR)).
  Definition tgt_instantiated_quiet_time_equivalent_quiet_time : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_instantiated_quiet_time_equivalent_quiet_time
      Job dJ jaL costL)).

  Theorem instantiated_quiet_time_equivalent_quiet_time_correspondence :
    PropSPropRel src_instantiated_quiet_time_equivalent_quiet_time tgt_instantiated_quiet_time_equivalent_quiet_time.
  Proof.
    unfold src_instantiated_quiet_time_equivalent_quiet_time, tgt_instantiated_quiet_time_equivalent_quiet_time.
    idl_full arrR arrL Harr sR sL Hs pR pL Hp.
    idl_j_pos arrR arrL Harr j.
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_iff_correspondence; [exact (rsi_quiet_time_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht)|].
    exact (ad_bool_truth_correspondence _ _ (rsi_ab_quiet_time_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht)).
  Qed.

  Definition src_instantiated_busy_interval_prefix_equivalent_busy_interval_prefix : Prop :=
    ltac:(body_of (fun s : S.statement_instantiated_busy_interval_prefix_equivalent_busy_interval_prefix =>
      s Job jaR costR)).
  Definition tgt_instantiated_busy_interval_prefix_equivalent_busy_interval_prefix : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_instantiated_busy_interval_prefix_equivalent_busy_interval_prefix
      Job dJ jaL costL)).

  Theorem instantiated_busy_interval_prefix_equivalent_busy_interval_prefix_correspondence :
    PropSPropRel src_instantiated_busy_interval_prefix_equivalent_busy_interval_prefix
      tgt_instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
  Proof.
    unfold src_instantiated_busy_interval_prefix_equivalent_busy_interval_prefix,
      tgt_instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
    idl_full arrR arrL Harr sR sL Hs pR pL Hp.
    idl_j_pos arrR arrL Harr j.
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    apply ad_iff_correspondence;
      [exact (rsi_busy_interval_prefix_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2)|].
    exact (rsi_ab_busy_interval_prefix_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2).
  Qed.

  Definition src_instantiated_busy_interval_equivalent_busy_interval : Prop :=
    ltac:(body_of (fun s : S.statement_instantiated_busy_interval_equivalent_busy_interval =>
      s Job jaR costR)).
  Definition tgt_instantiated_busy_interval_equivalent_busy_interval : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_instantiated_busy_interval_equivalent_busy_interval
      Job dJ jaL costL)).

  Theorem instantiated_busy_interval_equivalent_busy_interval_correspondence :
    PropSPropRel src_instantiated_busy_interval_equivalent_busy_interval
      tgt_instantiated_busy_interval_equivalent_busy_interval.
  Proof.
    unfold src_instantiated_busy_interval_equivalent_busy_interval,
      tgt_instantiated_busy_interval_equivalent_busy_interval.
    idl_full arrR arrL Harr sR sL Hs pR pL Hp.
    idl_j_pos arrR arrL Harr j.
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    apply ad_iff_correspondence;
      [exact (rsi_busy_interval_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2)|].
    exact (rsi_ab_busy_interval_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2).
  Qed.

  Definition src_abstract_busy_interval_classic_quiet_time : Prop :=
    ltac:(body_of (fun s : S.statement_abstract_busy_interval_classic_quiet_time => s Job jaR costR)).
  Definition tgt_abstract_busy_interval_classic_quiet_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_abstract_busy_interval_classic_quiet_time
      Job dJ jaL costL)).

  Theorem abstract_busy_interval_classic_quiet_time_correspondence :
    PropSPropRel src_abstract_busy_interval_classic_quiet_time tgt_abstract_busy_interval_classic_quiet_time.
  Proof.
    unfold src_abstract_busy_interval_classic_quiet_time, tgt_abstract_busy_interval_classic_quiet_time.
    idl_full arrR arrL Harr sR sL Hs pR pL Hp.
    idl_j_pos arrR arrL Harr j.
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    apply ad_imp_correspondence;
      [exact (rsi_ab_busy_interval_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2)|].
    exact (rsi_quiet_time_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ H1).
  Qed.

  Definition src_abstract_busy_interval_classic_busy_interval_prefix : Prop :=
    ltac:(body_of (fun s : S.statement_abstract_busy_interval_classic_busy_interval_prefix =>
      s Job jaR costR)).
  Definition tgt_abstract_busy_interval_classic_busy_interval_prefix : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_abstract_busy_interval_classic_busy_interval_prefix
      Job dJ jaL costL)).

  Theorem abstract_busy_interval_classic_busy_interval_prefix_correspondence :
    PropSPropRel src_abstract_busy_interval_classic_busy_interval_prefix
      tgt_abstract_busy_interval_classic_busy_interval_prefix.
  Proof.
    unfold src_abstract_busy_interval_classic_busy_interval_prefix,
      tgt_abstract_busy_interval_classic_busy_interval_prefix.
    idl_full arrR arrL Harr sR sL Hs pR pL Hp.
    idl_j_pos arrR arrL Harr j.
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    apply ad_imp_correspondence;
      [exact (rsi_ab_busy_interval_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2)|].
    exact (rsi_busy_interval_prefix_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2).
  Qed.

  (** *** I/IW correctness *)

  Definition src_not_interference_implies_scheduled : Prop :=
    ltac:(body_of (fun s : S.statement_not_interference_implies_scheduled => s Job jaR costR)).
  Definition tgt_not_interference_implies_scheduled : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_not_interference_implies_scheduled
      Job dJ jaL costL)).

  Theorem not_interference_implies_scheduled_correspondence :
    PropSPropRel src_not_interference_implies_scheduled tgt_not_interference_implies_scheduled.
  Proof.
    unfold src_not_interference_implies_scheduled, tgt_not_interference_implies_scheduled.
    idl_full arrR arrL Harr sR sL Hs pR pL Hp.
    idl_ready sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr.
    apply ad_imp_correspondence; [exact (rsi_reflexive_rel pR pL Hp)|].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j Harr)|].
    apply ad_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))|].
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    apply ad_imp_correspondence;
      [exact (rsi_ab_busy_interval_prefix_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2)|].
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
        (ar_decide_le_related _ _ _ _ H1 Ht) (ar_decide_lt_related _ _ _ _ Ht H2)))|].
    apply ad_imp_correspondence;
      [exact (ad_not_correspondence _ _ (ad_bool_truth_correspondence _ _
        (rsi_interference_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht)))|].
    exact (ad_bool_truth_correspondence _ _ (rsi_receives_service_at_related sR sL Hs j _ _ Ht)).
  Qed.

  Definition src_scheduled_implies_no_interference : Prop :=
    ltac:(body_of (fun s : S.statement_scheduled_implies_no_interference => s Job jaR)).
  Definition tgt_scheduled_implies_no_interference : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_scheduled_implies_no_interference
      Job dJ jaL)).

  Theorem scheduled_implies_no_interference_correspondence :
    PropSPropRel src_scheduled_implies_no_interference tgt_scheduled_implies_no_interference.
  Proof.
    unfold src_scheduled_implies_no_interference, tgt_scheduled_implies_no_interference.
    rsi_arr_sched arrR arrL Harr sR sL Hs. rsi_jlfp pR pL Hp.
    apply ad_imp_correspondence; [exact (rsi_reflexive_rel pR pL Hp)|].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (rsi_receives_service_at_related sR sL Hs j _ _ Ht))|].
    exact (ad_not_correspondence _ _ (ad_bool_truth_correspondence _ _
      (rsi_interference_related sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht))).
  Qed.

  Definition src_instantiated_i_and_w_are_coherent_with_schedule : Prop :=
    ltac:(body_of (fun s : S.statement_instantiated_i_and_w_are_coherent_with_schedule => s Job jaR costR)).
  Definition tgt_instantiated_i_and_w_are_coherent_with_schedule : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_instantiated_i_and_w_are_coherent_with_schedule
      Job dJ jaL costL)).

  Theorem instantiated_i_and_w_are_coherent_with_schedule_correspondence :
    PropSPropRel src_instantiated_i_and_w_are_coherent_with_schedule
      tgt_instantiated_i_and_w_are_coherent_with_schedule.
  Proof.
    unfold src_instantiated_i_and_w_are_coherent_with_schedule,
      tgt_instantiated_i_and_w_are_coherent_with_schedule.
    idl_full arrR arrL Harr sR sL Hs pR pL Hp.
    idl_ready sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr.
    apply ad_imp_correspondence; [exact (rsi_reflexive_rel pR pL Hp)|].
    exact (arta_wc_rel Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr
      _ _ (rsi_interference_rel sR sL Hs arrR arrL Harr pR pL Hp)
      _ _ (rsi_workload_rel sR sL Hs arrR arrL Harr pR pL Hp)).
  Qed.

  Definition src_instantiated_interference_and_workload_consistent_with_sequential_tasks : Prop :=
    ltac:(body_of (fun s : S.statement_instantiated_interference_and_workload_consistent_with_sequential_tasks =>
      s Task Job jtR jaR costR)).
  Definition tgt_instantiated_interference_and_workload_consistent_with_sequential_tasks : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_instantiated_interference_and_workload_consistent_with_sequential_tasks
      Task dT Job dJ jtL jaL costL)).

  Theorem instantiated_interference_and_workload_consistent_with_sequential_tasks_correspondence :
    PropSPropRel src_instantiated_interference_and_workload_consistent_with_sequential_tasks
      tgt_instantiated_interference_and_workload_consistent_with_sequential_tasks.
  Proof.
    unfold src_instantiated_interference_and_workload_consistent_with_sequential_tasks,
      tgt_instantiated_interference_and_workload_consistent_with_sequential_tasks.
    idl_full arrR arrL Harr sR sL Hs pR pL Hp.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_imp_correspondence; [exact (rsi_policy_respects_sequential_rel pR pL Hp)|].
    exact (interference_and_workload_consistent_with_sequential_tasks_correspondence Task Job PStateR PStateL R
      jtR jtL Hjt jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr
      _ _ (rsi_interference_rel sR sL Hs arrR arrL Harr pR pL Hp)
      _ _ (rsi_workload_rel sR sL Hs arrR arrL Harr pR pL Hp) tsk).
  Qed.

  Definition src_instantiated_busy_intervals_are_bounded : Prop :=
    ltac:(body_of (fun s : S.statement_instantiated_busy_intervals_are_bounded => s Task tcR Job jtR jaR costR)).
  Definition tgt_instantiated_busy_intervals_are_bounded : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_Ideal_IwInstantiation_instantiated_busy_intervals_are_bounded
      Task dT Job dJ tcL jtL jaL costL)).

  Theorem instantiated_busy_intervals_are_bounded_correspondence :
    PropSPropRel src_instantiated_busy_intervals_are_bounded tgt_instantiated_busy_intervals_are_bounded.
  Proof.
    unfold src_instantiated_busy_intervals_are_bounded, tgt_instantiated_busy_intervals_are_bounded.
    idl_full arrR arrL Harr sR sL Hs pR pL Hp.
    apply ad_forall_identity_correspondence. intro tsk.
    idl_ready sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr.
    apply ibt_forall_ma. intros maR maL Hma.
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_imp_correspondence;
      [exact (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts
        maR maL Hma)|].
    apply ad_imp_correspondence; [exact (idl_all_jobs_from_taskset_rel arrR arrL Harr tsR tsL Hts)|].
    apply ad_forall_nat_correspondence. intros LR LL HL.
    apply ad_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL)|].
    apply ad_imp_correspondence;
      [exact (sub_nat_eq_correspondence _ _ _ _ HL
        (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts LR LL HL))|].
    apply ad_imp_correspondence;
      [exact (arta_valid_job_costs_rel Task Job tcR tcL Htc jtR jtL Hjt costR costL Hcost arrR arrL Harr)|].
    exact (arta_bounded_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL Hcost sR sL Hs
      arrR arrL Harr _ _ (rsi_interference_rel sR sL Hs arrR arrL Harr pR pL Hp)
      _ _ (rsi_workload_rel sR sL Hs arrR arrL Harr pR pL Hp) tsk LR LL HL).
  Qed.
End IdealIwInstantiation.
