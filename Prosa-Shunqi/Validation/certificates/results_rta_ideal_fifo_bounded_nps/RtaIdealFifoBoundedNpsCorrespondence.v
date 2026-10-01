(* Main certificate for results/rta/ideal/fifo/bounded_nps.v: the helper part (no statement correspondences) of the accepted
   certificates/analysis_abstract_ideal_iw_instantiation/IdealIwInstantiationCorrespondence.v (generator
   gen_idl_main.py), replayed at the ideal processor-model universe instance of this export, followed by the local
   helpers and the statement correspondences of this file.  Dropped helper blocks: ['rsi_policy_respects_sequential_rel'] (each names a constant this export does not contain, or is unused by this file; not used). *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import IdealIwInstantiationSemanticSource RtaIdealFifoBoundedNpsSemanticSource.
From prosa Require TaskPreemptionParametersSemanticSource PreemptionParameterSemanticSource
  PriorityDrivenSemanticSource.
From prosa Require Import analysis.abstract.search_space model.task.arrival.curves.
From prosa Require Import model.readiness.basic model.priority.fifo.
From prosa Require Import analysis.abstract.definitions model.job.properties
  model.processor.platform_properties model.processor.supply model.schedule.work_conserving
  analysis.definitions.work_bearing_readiness model.processor.ideal.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaIdealFifoBoundedNps ImportedSubadditivity.
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
  IdlInterferenceCorrespondence IdlPriorityInversionCorrespondence IdlPreemptionTimeCorrespondence.
From FoundationCertificates Require Import IdlIbfTaskFullHelpers IdlStateRel.
From FoundationCertificates Require Import IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence.

Module I := ImportedRtaIdealFifoBoundedNps.
Module S := IdealIwInstantiationSemanticSource.IdealIwInstantiationSemanticSource.
Module S2 := RtaIdealFifoBoundedNpsSemanticSource.RtaIdealFifoBoundedNpsSemanticSource.
Module PPC := FoundationCertificates.IdlPreemptionParameterCorrespondence.
Module TPPC := FoundationCertificates.IdlTaskPreemptionParametersCorrespondence.
Module PTC := FoundationCertificates.IdlPreemptionTimeCorrespondence.
Module TPP := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module PDS := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.
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

(** Statement correspondences for [results/rta/ideal/fifo/bounded_nps.v], on top of the helper part (no statement
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

  (** ** Statement correspondences for [results/rta/ideal/fifo/bounded_nps.v] *)

  Local Ltac imp H := apply ad_imp_correspondence; [exact H|].

  (** *** Task-set predicates, basic readiness and the JLFP policy at preemption points (as in the accepted ideal
      EDF bounded_nps certificate) *)

  Lemma rff_all_jobs_from_taskset_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
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

  Lemma rff_valid_taskset_curve_rel tsR tsL (Hts : ArListRel tsR tsL) maR maL
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

  Lemma rff_basic_ready_at sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL) :
    RsiJrAt sR sL
      (@prosa.model.readiness.basic.basic_ready_instance Job PStateR jaR costR)
      (I.Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job dJ PStateL jaL costL).
  Proof.
    intros j tR tL Ht. cbn.
    exact (ibt_pending Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs j tR tL Ht).
  Qed.

  Lemma rff_backlogged_rel sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL) jrR jrL
      (Hjr : RsiJrAt sR sL jrR jrL) (j : Job) tR tL (Ht : SubNatRel tR tL) :
    ArBoolRel (@prosa.behavior.ready.backlogged Job PStateR costR jaR jrR sR j tR)
      (I.Prosa_Behavior_Ready_backlogged_inst4 Job dJ PStateL costL jaL jrL sL j tL).
  Proof.
    unfold prosa.behavior.ready.backlogged. cbn [I.Prosa_Behavior_Ready_backlogged_inst4].
    exact (ar_bool_and_related _ _ _ _ (Hjr j tR tL Ht)
      (svc_bool_not_related _ _ (ibt_sched_at Job PStateR PStateL R sR sL Hs j tR tL Ht))).
  Qed.

  Lemma rff_respects_jlfp_rel sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL)
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
    imp (ar_bool_truth_correspondence _ _ (rff_backlogged_rel sR sL Hs jrR jrL Hjr j tR tL Ht)).
    imp (ar_bool_truth_correspondence _ _
      (PPC.pp_scheduled_at_related Job PStateR PStateL rsi_jsvc sR sL (rsi_hs_jsvc sR sL Hs) j_hp tR tL Ht)).
    exact (ar_bool_truth_correspondence _ _ (Hp j_hp j)).
  Qed.

  Lemma rff_decide_not (P : SProp) (d : I.Decidable P) :
    Lean.eq (I.Decidable_decide (I.Not P) (I.instDecidableNot P d))
      (I.Bool_not (I.Decidable_decide P d)).
  Proof. destruct d; exact (@Lean.eq_refl _ _). Qed.

  Lemma rff_nat_neqb_related aR aL bR bL :
    SubNatRel aR aL -> SubNatRel bR bL ->
    SvcBoolRel (aR != bR)
      (I.Decidable_decide (I.Ne Lean.Nat aL bL)
        (I.instDecidableNot (Lean.eq aL bL) (I.instDecidableEqNat aL bL))).
  Proof.
    intros Ha Hb. unfold SvcBoolRel.
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (rff_decide_not _ _))).
    exact (svc_bool_not_related _ _ (svc_decide_eq_related _ _ _ _ Ha Hb)).
  Qed.

  Section RffAny.
    Context (X : Type).
    Variable PR : X -> bool.
    Variable PL : X -> I.Bool.
    Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).

    Lemma rff_has_canonical (xs : seq X) :
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

    Lemma rff_has_related (xsR : seq X) (xsL : I.List X) :
      ArListRel xsR xsL -> ArBoolRel (has PR xsR) (I.List_any X xsL PL).
    Proof.
      intro Hxs.
      exact (sub_imported_eq_trans _ _ _ (rff_has_canonical xsR)
        (sub_imported_eq_congr (fun l => I.List_any X l PL) _ _ Hxs)).
    Qed.
  End RffAny.


  (** *** The FIFO policy (as in the accepted restricted-supply FIFO certificate) *)

  Let FR := @prosa.model.priority.fifo.FIFO Job jaR.
  Let FL := I.Prosa_Model_Priority_Fifo_FIFO Job dJ jaL.

  Lemma rff_fifo_rel : RsiJLFPRel FR FL.
  Proof. intros x y. exact (svc_decide_le_related _ _ _ _ (Hja x) (Hja y)). Qed.

  (** *** Section-level task parameters *)

  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : IbtMaxArrivalsRel Task maR maL.

  Variable rtcR : TPP.TaskRunToCompletionThreshold Task.
  Variable rtcL : I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task dT.
  Hypothesis Hrtc : forall tsk : Task,
    SubNatRel (@TPP.task_rtct Task rtcR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task dT rtcL tsk).

  Variable jpR : PP.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PPC.PpJobPreemptableRel Job jpR jpL.

  (** *** is_in_concrete_search_space *)

  Theorem is_in_concrete_search_space_correspondence tsR tsL (Hts : ArListRel tsR tsL) (LR AR : nat)
      (LL AL : Lean.Nat) :
    SubNatRel LR LL -> SubNatRel AR AL ->
    SvcBoolRel (@S2.is_in_concrete_search_space Task tcR maR tsR LR AR)
      (I.Prosa_Results_Rta_Ideal_Fifo_BoundedNps_is_in_concrete_search_space Task dT tcL maL tsL LL AL).
  Proof.
    intros HL HA. unfold S2.is_in_concrete_search_space.
    cbn [I.Prosa_Results_Rta_Ideal_Fifo_BoundedNps_is_in_concrete_search_space].
    refine (ar_bool_and_related _ _ _ _ (svc_decide_lt_related _ _ _ _ HA HL) _).
    apply rff_has_related; [|exact Hts]. intro tsko.
    exact (rff_nat_neqb_related _ _ _ _
      (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsko _ _ HA)
      (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsko _ _
        (svc_target_add_related _ _ _ _ HA (sub_nat_rel_canonical (S O))))).
  Qed.

  (** The interference bound function [IBF], related pointwise, and the abstract search space over it. *)

  Ltac rff_ibf tsR tsL Hts tsk :=
    let xR := fresh "xR" in let xL := fresh "xL" in let dR := fresh "dR" in let dL := fresh "dL" in
    let Hx := fresh "Hx" in let Hd := fresh "Hd" in
    intros xR xL dR dL Hx Hd;
    exact (arta_sub_related _ _ _ _
      (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts _ _
        (arta_add_related _ _ _ _ Hx (sub_nat_rel_canonical 1))) (Htc tsk)).

  Ltac rff_ss tsR tsL Hts tsk HL HA :=
    apply arta_search_space_rel; [rff_ibf tsR tsL Hts tsk|exact HL|exact HA].

  Ltac rff_rmax tsR tsL Hts LR LL HL RR RL HR :=
    let AR := fresh "AR" in let AL := fresh "AL" in let HA := fresh "HA" in
    let FR := fresh "FR" in let FL := fresh "FL" in let HF := fresh "HF" in
    apply ad_forall_nat_correspondence; intros AR AL HA;
    (apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _
      (is_in_concrete_search_space_correspondence tsR tsL Hts LR AR LL AL HL HA))|]);
    apply ad_exists_nat_correspondence; intros FR FL HF;
    apply ad_and_correspondence;
    [ exact (sub_nat_le_correspondence _ _ _ _
        (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts _ _
          (arta_add_related _ _ _ _ HA (sub_nat_rel_canonical 1))) (arta_add_related _ _ _ _ HA HF))
    | exact (sub_nat_le_correspondence _ _ _ _ HF HR) ].

  (** *** abstractly_work_conserving *)

  Definition src_abstractly_work_conserving : Prop :=
    ltac:(body_of (fun s : S2.statement_abstractly_work_conserving => s Job jaR costR)).
  Definition tgt_abstractly_work_conserving : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Fifo_BoundedNps_abstractly_work_conserving Job dJ jaL costL)).

  Theorem abstractly_work_conserving_correspondence :
    PropSPropRel src_abstractly_work_conserving tgt_abstractly_work_conserving.
  Proof.
    unfold src_abstractly_work_conserving, tgt_abstractly_work_conserving.
    apply rsi_forall_arr. intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply rsi_forall_sched. intros sR sL Hs.
    have Hjr := rff_basic_ready_at sR sL Hs.
    imp (rsi_valid_schedule_rel sR sL Hs arrR arrL Harr _ _ Hjr).
    imp (rsi_work_conserving_related sR sL Hs arrR arrL Harr _ _ Hjr).
    exact (arta_wc_rel Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr
      _ _ (rsi_interference_rel sR sL Hs arrR arrL Harr _ _ rff_fifo_rel)
      _ _ (rsi_workload_rel sR sL Hs arrR arrL Harr _ _ rff_fifo_rel)).
  Qed.

  (** *** busy_windows_are_bounded *)

  Definition src_busy_windows_are_bounded : Prop :=
    ltac:(body_of (fun s : S2.statement_busy_windows_are_bounded => s Task tcR maR Job jtR jaR costR)).
  Definition tgt_busy_windows_are_bounded : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Fifo_BoundedNps_busy_windows_are_bounded
      Task dT Job dJ tcL maL jtL jaL costL)).

  Theorem busy_windows_are_bounded_correspondence :
    PropSPropRel src_busy_windows_are_bounded tgt_busy_windows_are_bounded.
  Proof.
    unfold src_busy_windows_are_bounded, tgt_busy_windows_are_bounded.
    apply rsi_forall_arr. intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    imp (arta_valid_job_costs_rel Task Job tcR tcL Htc jtR jtL Hjt costR costL Hcost arrR arrL Harr).
    apply arta_forall_list. intros tsR tsL Hts.
    imp (rff_all_jobs_from_taskset_rel arrR arrL Harr tsR tsL Hts).
    imp (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma).
    apply ad_forall_identity_correspondence => tsk.
    apply rsi_forall_sched. intros sR sL Hs.
    have Hjr := rff_basic_ready_at sR sL Hs.
    imp (rsi_valid_schedule_rel sR sL Hs arrR arrL Harr _ _ Hjr).
    imp (rsi_work_conserving_related sR sL Hs arrR arrL Harr _ _ Hjr).
    apply ad_forall_nat_correspondence => LR LL HL.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    imp (sub_nat_eq_correspondence _ _ _ _ HL
      (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts LR LL HL)).
    exact (arta_bounded_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL Hcost sR sL Hs
      arrR arrL Harr _ _ (rsi_interference_rel sR sL Hs arrR arrL Harr _ _ rff_fifo_rel)
      _ _ (rsi_workload_rel sR sL Hs arrR arrL Harr _ _ rff_fifo_rel) tsk LR LL HL).
  Qed.

  (** *** no_priority_inversion *)

  Definition src_no_priority_inversion : Prop :=
    ltac:(body_of (fun s : S2.statement_no_priority_inversion => s Task Job jtR jaR costR jpR)).
  Definition tgt_no_priority_inversion : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Fifo_BoundedNps_no_priority_inversion
      Task dT Job dJ jtL jaL costL jpL)).

  Theorem no_priority_inversion_correspondence :
    PropSPropRel src_no_priority_inversion tgt_no_priority_inversion.
  Proof.
    unfold src_no_priority_inversion, tgt_no_priority_inversion.
    apply rsi_forall_arr. intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply ad_forall_identity_correspondence => tsk.
    apply rsi_forall_sched. intros sR sL Hs.
    have Hjr := rff_basic_ready_at sR sL Hs.
    imp (rsi_valid_schedule_rel sR sL Hs arrR arrL Harr _ _ Hjr).
    imp (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL rsi_jsvc
      sR sL (rsi_hs_jsvc sR sL Hs) arrR arrL Harr).
    imp (rff_respects_jlfp_rel sR sL Hs arrR arrL Harr jpR jpL Hjp _ _ Hjr _ _ rff_fifo_rel).
    apply ad_forall_identity_correspondence => j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt)).
    imp (ad_bool_truth_correspondence _ _ (arta_cost_positive_related Job costR costL Hcost j)).
    apply ad_forall_nat_correspondence => t1R t1L H1.
    apply ad_forall_nat_correspondence => t2R t2L H2.
    imp (rsi_ab_busy_interval_related sR sL Hs arrR arrL Harr _ _ rff_fifo_rel j _ _ _ _ H1 H2).
    apply ad_forall_nat_correspondence => dR dL Hd.
    have Hsum := arta_add_related _ _ _ _ H1 Hd.
    imp (sub_nat_lt_correspondence _ _ _ _ Hsum H2).
    exact (sub_nat_eq_correspondence _ _ _ _
      (PIC.cumulative_priority_inversion_correspondence Job PStateR PStateL rsi_jsvc arrR arrL Harr sR sL
        (rsi_hs_jsvc sR sL Hs) _ _ rff_fifo_rel j _ _ _ _ H1 Hsum) (sub_nat_rel_canonical O)).
  Qed.

  (** *** IBF_correct *)

  Definition src_IBF_correct : Prop :=
    ltac:(body_of (fun s : S2.statement_IBF_correct => s Task tcR maR Job jtR jaR costR jpR)).
  Definition tgt_IBF_correct : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Fifo_BoundedNps_IBF_correct
      Task dT Job dJ tcL maL jtL jaL costL jpL)).

  Theorem IBF_correct_correspondence : PropSPropRel src_IBF_correct tgt_IBF_correct.
  Proof.
    unfold src_IBF_correct, tgt_IBF_correct.
    apply rsi_forall_arr. intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    imp (arta_valid_job_costs_rel Task Job tcR tcL Htc jtR jtL Hjt costR costL Hcost arrR arrL Harr).
    apply arta_forall_list. intros tsR tsL Hts.
    imp (rff_all_jobs_from_taskset_rel arrR arrL Harr tsR tsL Hts).
    imp (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma).
    imp (rff_valid_taskset_curve_rel tsR tsL Hts maR maL Hma).
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply rsi_forall_sched. intros sR sL Hs.
    have Hjr := rff_basic_ready_at sR sL Hs.
    imp (rsi_valid_schedule_rel sR sL Hs arrR arrL Harr _ _ Hjr).
    imp (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL rsi_jsvc
      sR sL (rsi_hs_jsvc sR sL Hs) arrR arrL Harr).
    imp (rff_respects_jlfp_rel sR sL Hs arrR arrL Harr jpR jpL Hjp _ _ Hjr _ _ rff_fifo_rel).
    apply ad_forall_nat_correspondence => LR LL HL.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    imp (sub_nat_eq_correspondence _ _ _ _ HL
      (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts LR LL HL)).
    have HI := rsi_interference_rel sR sL Hs arrR arrL Harr _ _ rff_fifo_rel.
    have HW := rsi_workload_rel sR sL Hs arrR arrL Harr _ _ rff_fifo_rel.
    refine (arta_job_interference_bounded_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL Hcost
      sR sL Hs arrR arrL Harr _ _ HI _ _ HW tsk _ _ _ _ _
      (fun j xR xL Hx => relative_arrival_time_of_job_is_A_correspondence Job PStateR PStateL R jaR jaL Hja
        costR costL Hcost sR sL Hs _ _ HI _ _ HW j xR xL Hx)).
    rff_ibf tsR tsL Hts tsk.
  Qed.

  (** *** search_space_refinement *)

  Definition src_search_space_refinement : Prop :=
    ltac:(body_of (fun s : S2.statement_search_space_refinement => s Task tcR maR)).
  Definition tgt_search_space_refinement : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Fifo_BoundedNps_search_space_refinement Task dT tcL maL)).

  Theorem search_space_refinement_correspondence :
    PropSPropRel src_search_space_refinement tgt_search_space_refinement.
  Proof.
    unfold src_search_space_refinement, tgt_search_space_refinement.
    apply arta_forall_list. intros tsR tsL Hts.
    imp (rff_valid_taskset_curve_rel tsR tsL Hts maR maL Hma).
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply ad_forall_nat_correspondence => LR LL HL.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Htc tsk)).
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hma tsk _ _ (sub_nat_rel_canonical 1))).
    apply ad_forall_nat_correspondence => AR AL HA.
    apply ad_imp_correspondence; [rff_ss tsR tsL Hts tsk HL HA|].
    exact (ad_bool_truth_correspondence _ _ (is_in_concrete_search_space_correspondence tsR tsL Hts
      LR AR LL AL HL HA)).
  Qed.

  (** *** soln_abstract_response_time_recurrence *)

  Definition src_soln_abstract_response_time_recurrence : Prop :=
    ltac:(body_of (fun s : S2.statement_soln_abstract_response_time_recurrence =>
      s Task tcR maR rtcR Job jtR costR jpR)).
  Definition tgt_soln_abstract_response_time_recurrence : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Fifo_BoundedNps_soln_abstract_response_time_recurrence
      Task dT Job dJ tcL maL rtcL jtL costL jpL)).

  Theorem soln_abstract_response_time_recurrence_correspondence :
    PropSPropRel src_soln_abstract_response_time_recurrence tgt_soln_abstract_response_time_recurrence.
  Proof.
    unfold src_soln_abstract_response_time_recurrence, tgt_soln_abstract_response_time_recurrence.
    apply rsi_forall_arr. intros arrR arrL Harr.
    apply arta_forall_list. intros tsR tsL Hts.
    imp (rff_valid_taskset_curve_rel tsR tsL Hts maR maL Hma).
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    imp (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rtcR rtcL Hrtc
      jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk).
    apply ad_forall_nat_correspondence => LR LL HL.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    imp (sub_nat_eq_correspondence _ _ _ _ HL
      (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts LR LL HL)).
    apply ad_forall_nat_correspondence => RR RL HR.
    apply ad_imp_correspondence; [rff_rmax tsR tsL Hts LR LL HL RR RL HR|].
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Htc tsk)).
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hma tsk _ _ (sub_nat_rel_canonical 1))).
    apply ad_forall_nat_correspondence => AR AL HA.
    apply ad_imp_correspondence; [rff_ss tsR tsL Hts tsk HL HA|].
    apply ad_exists_nat_correspondence => FxR FxL HFx.
    have HAF := arta_add_related _ _ _ _ HA HFx.
    have Hcr := arta_sub_related _ _ _ _ (Htc tsk) (Hrtc tsk).
    apply ad_and_correspondence.
    - exact (sub_nat_le_correspondence _ _ _ _ (arta_add_related _ _ _ _ (Hrtc tsk)
        (arta_sub_related _ _ _ _ (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma
          tsR tsL Hts _ _ (arta_add_related _ _ _ _ HA (sub_nat_rel_canonical 1))) (Htc tsk))) HAF).
    - exact (sub_nat_le_correspondence _ _ _ _ (arta_add_related _ _ _ _ HFx Hcr) HR).
  Qed.

  (** *** uniprocessor_response_time_bound_FIFO *)

  Definition src_uniprocessor_response_time_bound_FIFO : Prop :=
    ltac:(body_of (fun s : S2.statement_uniprocessor_response_time_bound_FIFO =>
      s Task tcR maR rtcR Job jtR jaR costR jpR)).
  Definition tgt_uniprocessor_response_time_bound_FIFO : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Fifo_BoundedNps_uniprocessor_response_time_bound_FIFO
      Task dT Job dJ tcL maL rtcL jtL jaL costL jpL)).

  Theorem uniprocessor_response_time_bound_FIFO_correspondence :
    PropSPropRel src_uniprocessor_response_time_bound_FIFO tgt_uniprocessor_response_time_bound_FIFO.
  Proof.
    unfold src_uniprocessor_response_time_bound_FIFO, tgt_uniprocessor_response_time_bound_FIFO.
    apply rsi_forall_arr. intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    imp (arta_valid_job_costs_rel Task Job tcR tcL Htc jtR jtL Hjt costR costL Hcost arrR arrL Harr).
    apply arta_forall_list. intros tsR tsL Hts.
    imp (rff_all_jobs_from_taskset_rel arrR arrL Harr tsR tsL Hts).
    imp (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma).
    imp (rff_valid_taskset_curve_rel tsR tsL Hts maR maL Hma).
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    imp (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rtcR rtcL Hrtc
      jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk).
    apply rsi_forall_sched. intros sR sL Hs.
    have Hjr := rff_basic_ready_at sR sL Hs.
    imp (rsi_valid_schedule_rel sR sL Hs arrR arrL Harr _ _ Hjr).
    imp (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL rsi_jsvc
      sR sL (rsi_hs_jsvc sR sL Hs) arrR arrL Harr).
    imp (rff_respects_jlfp_rel sR sL Hs arrR arrL Harr jpR jpL Hjp _ _ Hjr _ _ rff_fifo_rel).
    imp (rsi_work_conserving_related sR sL Hs arrR arrL Harr _ _ Hjr).
    apply ad_forall_nat_correspondence => LR LL HL.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    imp (sub_nat_eq_correspondence _ _ _ _ HL
      (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts LR LL HL)).
    apply ad_forall_nat_correspondence => RR RL HR.
    apply ad_imp_correspondence; [rff_rmax tsR tsL Hts LR LL HL RR RL HR|].
    exact (arta_response_time_bound_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL Hcost
      sR sL Hs arrR arrL Harr tsk RR RL HR).
  Qed.
End IdealIwInstantiation.
