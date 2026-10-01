(* Main certificate for results/rta/ideal/gel/bounded_pi.v: the helper part (no statement correspondences) of the accepted
   certificates/analysis_abstract_ideal_iw_instantiation/IdealIwInstantiationCorrespondence.v (generator
   gen_idl_main.py), replayed at the ideal processor-model universe instance of this export, followed by the local
   helpers and the statement correspondences of this file.  Dropped helper blocks: ['rsi_policy_respects_sequential_rel'] (each names a constant this export does not contain, or is unused by this file; not used). *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From mathcomp Require Import order ssralg ssrnum ssrint.
From prosa Require Import IdealIwInstantiationSemanticSource RtaIdealGelBoundedPiSemanticSource.
From prosa Require TaskPreemptionParametersSemanticSource PreemptionParameterSemanticSource
  PriorityDrivenSemanticSource.
From prosa Require Import analysis.abstract.search_space model.task.arrival.curves.
From prosa Require Import model.readiness.basic util.int model.priority.gel.
From prosa Require Import analysis.abstract.definitions model.job.properties
  model.processor.platform_properties model.processor.supply model.schedule.work_conserving
  analysis.definitions.work_bearing_readiness model.processor.ideal.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaIdealGelBoundedPi ImportedSubadditivity.
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
From FoundationCertificates Require Import IdlEdfAthepBoundCorrespondence IdlNatSubCorrespondence IdlPcoBaseAdapter
  IdlPcoStaticOrder IdlPcoDynamicOrder IdlPriorityCoercionCorrespondence IdlPriorityGelHelpers.
From FoundationCertificates Require Import IdlIbfTaskFullHelpers IdlStateRel.
From FoundationCertificates Require Import IdlCurvesCorrespondence IdlRequestBoundFunctionCorrespondence.

Module I := ImportedRtaIdealGelBoundedPi.
Module S := IdealIwInstantiationSemanticSource.IdealIwInstantiationSemanticSource.
Module S2 := RtaIdealGelBoundedPiSemanticSource.RtaIdealGelBoundedPiSemanticSource.
Module PPC := FoundationCertificates.IdlPreemptionParameterCorrespondence.
Module TPPC := FoundationCertificates.IdlTaskPreemptionParametersCorrespondence.
Module PTC := FoundationCertificates.IdlPreemptionTimeCorrespondence.
Module TPP := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module PDS := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.
Import GRing.Theory Num.Theory Order.TTheory.
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

(** Statement correspondences for [results/rta/ideal/gel/bounded_pi.v], on top of the helper part (no statement
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

  (** ** Statement correspondences for [results/rta/ideal/gel/bounded_pi.v] *)

  Local Ltac imp H := apply ad_imp_correspondence; [exact H|].

  (** *** Task-set predicates, bound functions, basic readiness, the JLFP policy at preemption points and [has]
      (as in the accepted ideal EDF bounded_pi certificate) *)

  Lemma rgel_all_jobs_from_taskset_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
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

  Lemma rgel_valid_taskset_curve_rel tsR tsL (Hts : ArListRel tsR tsL) maR maL
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

  (** *** Priority-inversion bound functions, covered in both directions (as in the accepted ideal
      cumulative-bounds certificate) *)

  Definition rgel_fun_to_target (f : nat -> nat) : Lean.Nat -> Lean.Nat :=
    fun n => sub_nat_to_imported (f (sub_nat_to_rocq n)).
  Definition rgel_fun_to_source (f : Lean.Nat -> Lean.Nat) : nat -> nat :=
    fun n => sub_nat_to_rocq (f (sub_nat_to_imported n)).
  Definition RgelFunRel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) : SProp :=
    forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

  Lemma rgel_forall_fun (PR : (nat -> nat) -> Prop) (PL : (Lean.Nat -> Lean.Nat) -> SProp) :
    (forall fR fL, RgelFunRel fR fL -> PropSPropRel (PR fR) (PL fL)) ->
    PropSPropRel (forall f, PR f) (forall f, PL f).
  Proof.
    apply (arta_forall_cover _ _ RgelFunRel rgel_fun_to_target rgel_fun_to_source).
    - intros fR nR nL Hn. unfold rgel_fun_to_target. rewrite (arta_nat_input _ _ Hn).
      exact (sub_nat_rel_canonical _).
    - intros fL nR nL Hn. unfold rgel_fun_to_source. destruct Hn.
      exact (sub_nat_rel_surjective _).
  Qed.

  Lemma rgel_basic_ready_at sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL) :
    RsiJrAt sR sL
      (@prosa.model.readiness.basic.basic_ready_instance Job PStateR jaR costR)
      (I.Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job dJ PStateL jaL costL).
  Proof.
    intros j tR tL Ht. cbn.
    exact (ibt_pending Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs j tR tL Ht).
  Qed.

  Lemma rgel_backlogged_rel sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL) jrR jrL
      (Hjr : RsiJrAt sR sL jrR jrL) (j : Job) tR tL (Ht : SubNatRel tR tL) :
    ArBoolRel (@prosa.behavior.ready.backlogged Job PStateR costR jaR jrR sR j tR)
      (I.Prosa_Behavior_Ready_backlogged_inst4 Job dJ PStateL costL jaL jrL sL j tL).
  Proof.
    unfold prosa.behavior.ready.backlogged. cbn [I.Prosa_Behavior_Ready_backlogged_inst4].
    exact (ar_bool_and_related _ _ _ _ (Hjr j tR tL Ht)
      (svc_bool_not_related _ _ (ibt_sched_at Job PStateR PStateL R sR sL Hs j tR tL Ht))).
  Qed.

  Lemma rgel_respects_jlfp_rel sR sL (Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL)
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
    imp (ar_bool_truth_correspondence _ _ (rgel_backlogged_rel sR sL Hs jrR jrL Hjr j tR tL Ht)).
    imp (ar_bool_truth_correspondence _ _
      (PPC.pp_scheduled_at_related Job PStateR PStateL rsi_jsvc sR sL (rsi_hs_jsvc sR sL Hs) j_hp tR tL Ht)).
    exact (ar_bool_truth_correspondence _ _ (Hp j_hp j)).
  Qed.

  (** *** The four search-space definitions (restating the accepted restricted-supply EDF search-space definition
      certificate, with the priority-inversion bound in place of the blocking bound) *)

  Lemma rgel_decide_not (P : SProp) (d : I.Decidable P) :
    Lean.eq (I.Decidable_decide (I.Not P) (I.instDecidableNot P d))
      (I.Bool_not (I.Decidable_decide P d)).
  Proof. destruct d; exact (@Lean.eq_refl _ _). Qed.

  Lemma rgel_nat_neqb_related aR aL bR bL :
    SubNatRel aR aL -> SubNatRel bR bL ->
    SvcBoolRel (aR != bR)
      (I.Decidable_decide (I.Ne Lean.Nat aL bL)
        (I.instDecidableNot (Lean.eq aL bL) (I.instDecidableEqNat aL bL))).
  Proof.
    intros Ha Hb. unfold SvcBoolRel.
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (rgel_decide_not _ _))).
    exact (svc_bool_not_related _ _ (svc_decide_eq_related _ _ _ _ Ha Hb)).
  Qed.

  Section RgelAny.
    Context (X : Type).
    Variable PR : X -> bool.
    Variable PL : X -> I.Bool.
    Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).

    Lemma rgel_has_canonical (xs : seq X) :
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

    Lemma rgel_has_related (xsR : seq X) (xsL : I.List X) :
      ArListRel xsR xsL -> ArBoolRel (has PR xsR) (I.List_any X xsL PL).
    Proof.
      intro Hxs.
      exact (sub_imported_eq_trans _ _ _ (rgel_has_canonical xsR)
        (sub_imported_eq_congr (fun l => I.List_any X l PL) _ _ Hxs)).
    Qed.
  End RgelAny.


  (** *** Section-level task parameters and the GEL policy *)

  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : IbtMaxArrivalsRel Task maR maL.

  Variable ppR : prosa.model.priority.gel.PriorityPoint Task.
  Variable ppL : I.Prosa_Model_Priority_Gel_PriorityPoint Task dT.
  Hypothesis Hpp : GelPriorityPointRel Task ppR ppL.

  Variable rtcR : TPP.TaskRunToCompletionThreshold Task.
  Variable rtcL : I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task dT.
  Hypothesis Hrtc : forall tsk : Task,
    SubNatRel (@TPP.task_rtct Task rtcR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task dT rtcL tsk).

  Variable jpR : PP.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PPC.PpJobPreemptableRel Job jpR jpL.

  Let GR := @prosa.model.priority.gel.GEL Job Task ppR jaR jtR.
  Let GL := I.Prosa_Model_Priority_Gel_GEL Job dJ Task dT ppL jaL jtL.

  Lemma rgel_gel_rel : RsiJLFPRel GR GL.
  Proof. exact (GEL_correspondence Job Task ppR ppL Hpp jaR jaL Hja jtR jtL Hjt). Qed.

  (** *** Integers: the cast, subtraction, [`|Num.max 0 _|] (restated from the accepted ELF athep-bound definition
      certificate) and disequality (as in the accepted ELF search-space certificate) *)

  Notation P_sub_oo_le := I.Prosa_Validation_ElfAthepBoundInterface_production_int_sub_ofNat_ofNat_le.
  Notation P_sub_oo_gt := I.Prosa_Validation_ElfAthepBoundInterface_production_int_sub_ofNat_ofNat_gt.
  Notation P_sub_on := I.Prosa_Validation_ElfAthepBoundInterface_production_int_sub_ofNat_negSucc.
  Notation P_sub_no := I.Prosa_Validation_ElfAthepBoundInterface_production_int_sub_negSucc_ofNat.
  Notation P_sub_nn_le := I.Prosa_Validation_ElfAthepBoundInterface_production_int_sub_negSucc_negSucc_le.
  Notation P_sub_nn_gt := I.Prosa_Validation_ElfAthepBoundInterface_production_int_sub_negSucc_negSucc_gt.
  Notation P_abs_o := I.Prosa_Validation_ElfAthepBoundInterface_production_int_natAbs_max_ofNat.
  Notation P_abs_n := I.Prosa_Validation_ElfAthepBoundInterface_production_int_natAbs_max_negSucc.
  Notation P_int_ne := I.Prosa_Validation_RtaIdealGelBoundedPiInterface_production_int_decide_ne.

  Definition rgel_target_sub (x y : I.Int) : I.Int :=
    ltac:(let T := type of (P_sub_on (sub_nat_to_imported 0) (sub_nat_to_imported 0)) in
          match T with @Lean.eq _ (?f (I.Int_ofNat _) (I.Int_negSucc _)) _ => exact (f x y) end).

  Definition rgel_target_absmax (z : I.Int) : Lean.Nat :=
    ltac:(let T := type of (P_abs_o (sub_nat_to_imported 0)) in
          match T with @Lean.eq _ (?g (?h (I.Int_ofNat _))) _ => exact (g (h z)) end).

  Definition rgel_target_int_ne (a b : I.Int) : I.Bool :=
    ltac:(let T := type of (P_int_ne a b) in match T with @Lean.eq _ ?L _ => exact L end).

  Lemma rgel_subz_pp_le (m n : nat) : (n <= m)%N -> (Posz m - Posz n)%R = Posz (m - n).
  Proof. by move=> h; rewrite subzn. Qed.

  Lemma rgel_subz_pp_gt (m n : nat) : ~~ (n <= m)%N -> (Posz m - Posz n)%R = Negz (n - m - 1).
  Proof.
    rewrite -ltnNge => h. rewrite NegzE subn1 prednK ?subn_gt0 //.
    by rewrite -subzn ?opprB // ltnW.
  Qed.

  Lemma rgel_subz_pn (m n : nat) : (Posz m - Negz n)%R = Posz (m + n + 1).
  Proof. by rewrite NegzE opprK -!PoszD addn1 addnS. Qed.

  Lemma rgel_subz_np (m n : nat) : (Negz m - Posz n)%R = Negz (m + n).
  Proof. by rewrite !NegzE -opprD -PoszD addSn. Qed.

  Lemma rgel_subz_nn_le (m n : nat) : (m <= n)%N -> (Negz m - Negz n)%R = Posz (n - m).
  Proof. by move=> h; rewrite !NegzE opprK addrC subzn. Qed.

  Lemma rgel_subz_nn_gt (m n : nat) : ~~ (m <= n)%N -> (Negz m - Negz n)%R = Negz (m - n - 1).
  Proof.
    rewrite -ltnNge => h. rewrite !NegzE opprK subn1 prednK ?subn_gt0 //.
    rewrite -subzn ?(ltnW h) // opprB addrC -(addn1 n) -(addn1 m) !PoszD opprD addrACA subrr addr0.
    by [].
  Qed.

  Lemma rgel_absmax_p (n : nat) : `|Num.max 0%R (Posz n)| = n.
  Proof. by rewrite max_r. Qed.

  Lemma rgel_absmax_n (n : nat) : `|Num.max 0%R (Negz n)| = 0%N.
  Proof. by rewrite max_l. Qed.

  Lemma rgel_sub1_related (a b : nat) :
    SubNatRel (a - b - 1) (nat_target_sub (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
      (sub_nat_to_imported 1)).
  Proof.
    exact (nat_target_sub_correspondence _ _ _ _
      (nat_target_sub_correspondence _ _ _ _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b))
      (sub_nat_rel_canonical 1)).
  Qed.

  Lemma rgel_add1_related (a b : nat) :
    SubNatRel (a + b + 1) (nat_target_add (nat_target_add (sub_nat_to_imported a) (sub_nat_to_imported b))
      (sub_nat_to_imported 1)).
  Proof.
    exact (nat_target_add_correspondence _ _ _ _
      (nat_target_add_correspondence _ _ _ _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b))
      (sub_nat_rel_canonical 1)).
  Qed.

  Lemma rgel_sub_canonical (x y : int) :
    GelIntRel (x - y)%R (rgel_target_sub (gel_int_to_imported x) (gel_int_to_imported y)).
  Proof.
    unfold GelIntRel, rgel_target_sub.
    destruct x as [m|m], y as [n|n]; cbn [gel_int_to_imported].
    - have Hle := sub_nat_le_correspondence n (sub_nat_to_imported n) m (sub_nat_to_imported m)
        (sub_nat_rel_canonical n) (sub_nat_rel_canonical m).
      destruct (leq n m) eqn:E.
      + rewrite (rgel_subz_pp_le m n E). cbn [gel_int_to_imported].
        refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
          (P_sub_oo_le _ _ (prop_to_sprop _ _ Hle isT)))).
        exact (sub_imported_eq_congr I.Int_ofNat _ _
          (nat_target_sub_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical n))).
      + rewrite (rgel_subz_pp_gt m n (negbT E)). cbn [gel_int_to_imported].
        refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
          (P_sub_oo_gt _ _ (fun H => gel_coq_false_to_target
            (Bool.diff_false_true (sprop_to_prop _ _ Hle H)))))).
        exact (sub_imported_eq_congr I.Int_negSucc _ _ (rgel_sub1_related n m)).
    - rewrite rgel_subz_pn. cbn [gel_int_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (P_sub_on _ _))).
      exact (sub_imported_eq_congr I.Int_ofNat _ _ (rgel_add1_related m n)).
    - rewrite rgel_subz_np. cbn [gel_int_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (P_sub_no _ _))).
      exact (sub_imported_eq_congr I.Int_negSucc _ _
        (nat_target_add_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical n))).
    - have Hle := sub_nat_le_correspondence m (sub_nat_to_imported m) n (sub_nat_to_imported n)
        (sub_nat_rel_canonical m) (sub_nat_rel_canonical n).
      destruct (leq m n) eqn:E.
      + rewrite (rgel_subz_nn_le m n E). cbn [gel_int_to_imported].
        refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
          (P_sub_nn_le _ _ (prop_to_sprop _ _ Hle isT)))).
        exact (sub_imported_eq_congr I.Int_ofNat _ _
          (nat_target_sub_correspondence _ _ _ _ (sub_nat_rel_canonical n) (sub_nat_rel_canonical m))).
      + rewrite (rgel_subz_nn_gt m n (negbT E)). cbn [gel_int_to_imported].
        refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
          (P_sub_nn_gt _ _ (fun H => gel_coq_false_to_target
            (Bool.diff_false_true (sprop_to_prop _ _ Hle H)))))).
        exact (sub_imported_eq_congr I.Int_negSucc _ _ (rgel_sub1_related m n)).
  Qed.

  Lemma rgel_sub_related xR xL yR yL :
    GelIntRel xR xL -> GelIntRel yR yL -> GelIntRel (xR - yR)%R (rgel_target_sub xL yL).
  Proof.
    intros Hx Hy. unfold GelIntRel.
    exact (sub_imported_eq_trans _ _ _ (rgel_sub_canonical xR yR)
      (sub_imported_eq_congr2 rgel_target_sub _ _ _ _ Hx Hy)).
  Qed.

  Lemma rgel_absmax_canonical (z : int) :
    SubNatRel `|Num.max 0%R z| (rgel_target_absmax (gel_int_to_imported z)).
  Proof.
    unfold rgel_target_absmax.
    destruct z as [n|n]; cbn [gel_int_to_imported].
    - rewrite rgel_absmax_p.
      exact (sub_imported_eq_trans _ _ _ (sub_nat_rel_canonical n) (sub_imported_eq_sym _ _ (P_abs_o _))).
    - rewrite rgel_absmax_n.
      exact (sub_imported_eq_trans _ _ _ (sub_nat_rel_canonical 0) (sub_imported_eq_sym _ _ (P_abs_n _))).
  Qed.

  Lemma rgel_absmax_related zR zL :
    GelIntRel zR zL -> SubNatRel `|Num.max 0%R zR| (rgel_target_absmax zL).
  Proof.
    intro Hz.
    exact (sub_imported_eq_trans _ _ _ (rgel_absmax_canonical zR)
      (sub_imported_eq_congr rgel_target_absmax _ _ Hz)).
  Qed.

  Lemma rgel_int_neq_le (x y : int) : (x != y) = ~~ ((x <= y)%R && (y <= x)%R).
  Proof. by rewrite eq_le. Qed.

  Lemma rgel_int_neq_related xR xL yR yL :
    GelIntRel xR xL -> GelIntRel yR yL -> ArBoolRel (xR != yR) (rgel_target_int_ne xL yL).
  Proof.
    intros Hx Hy. rewrite rgel_int_neq_le. unfold ArBoolRel, rgel_target_int_ne.
    exact (sub_imported_eq_trans _ _ _
      (pd_bool_not_related _ _ (pd_bool_and_related _ _ _ _ (gel_le_related _ _ _ _ Hx Hy)
        (gel_le_related _ _ _ _ Hy Hx)))
      (sub_imported_eq_sym _ _ (P_int_ne xL yL))).
  Qed.

  Lemma rgel_cast_related nR nL :
    SubNatRel nR nL -> GelIntRel (nR%:R)%R (I.Nat_cast_inst1 I.Int I.instNatCastInt nL).
  Proof.
    intro Hn. rewrite natz. unfold GelIntRel. cbn [gel_int_to_imported].
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_congr I.Int_ofNat _ _ Hn)
      (sub_imported_eq_sym _ _ (P_cast nL))).
  Qed.

  (** The integer interval [(A + ε)%:R + PP tsk - PP tsk_o] and its clipped length. *)

  Notation rgel_interval_rel tsk tsk_o HA :=
    (rgel_sub_related _ _ _ _
      (gel_add_related _ _ _ _ (arta_add_related _ _ _ _ HA (sub_nat_rel_canonical 1)) (Hpp tsk)) (Hpp tsk_o))
    (only parsing).

  (** The higher-or-equal-priority workload of the jobs of [tsk_o]. *)

  Local Ltac rgel_hepw arrR arrL Harr j tsk_o H1 H2 :=
    exact (workload_of_jobs_correspondence Job costR costL Hcost _ _
      (fun jo => ar_bool_and_related _ _ _ _ (rgel_gel_rel jo j)
        (ad_job_of_task_related Job Task jtR jtL tsk_o jo Hjt))
      _ _ (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2)).

  Local Ltac rgel_sum tsR tsL Hts tsk HA HD :=
    apply rbf_sum_filtered_related; [| |exact Hts];
    [ let o := fresh "o" in intro o;
      exact (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma o _ _
        (eab_min_related _ _ _ _ (rgel_absmax_related _ _ (rgel_interval_rel tsk o HA)) HD))
    | let o := fresh "o" in intro o; exact (rbf_neq_related Task o tsk) ].

  (** *** total_workload_shorten_range *)

  Definition src_total_workload_shorten_range : Prop :=
    ltac:(body_of (fun s : S2.statement_total_workload_shorten_range => s Task tcR maR Job jtR jaR costR ppR)).
  Definition tgt_total_workload_shorten_range : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_total_workload_shorten_range
      Task dT Job dJ tcL maL jtL jaL costL ppL)).

  Local Ltac rgel_busy_prefix arrR arrL Harr tsR tsL Hts tsk LR LL HL j t1R t1L H1 t2R t2L H2 dR dL Hd :=
    apply ad_forall_nat_correspondence; intros LR LL HL;
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL);
    imp (sub_nat_eq_correspondence _ _ _ _ HL
      (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts LR LL HL));
    apply ad_forall_identity_correspondence; intro j;
    imp (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt));
    imp (ad_bool_truth_correspondence _ _ (arta_cost_positive_related Job costR costL Hcost j));
    apply ad_forall_nat_correspondence; intros t1R t1L H1;
    apply ad_forall_nat_correspondence; intros t2R t2L H2;
    apply ad_forall_nat_correspondence; intros dR dL Hd;
    imp (sub_nat_lt_correspondence _ _ _ _ (arta_add_related _ _ _ _ H1 Hd) H2).

  Theorem total_workload_shorten_range_correspondence :
    PropSPropRel src_total_workload_shorten_range tgt_total_workload_shorten_range.
  Proof.
    unfold src_total_workload_shorten_range, tgt_total_workload_shorten_range.
    apply rsi_forall_arr. intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    rgel_busy_prefix arrR arrL Harr tsR tsL Hts tsk LR LL HL j t1R t1L H1 t2R t2L H2 dR dL Hd.
    apply ad_forall_identity_correspondence => tsk_o.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk_o _ _ Hts)).
    imp (ad_bool_truth_correspondence _ _ (rbf_neq_related Task tsk_o tsk)).
    have HA := arta_sub_related _ _ _ _ (Hja j) H1.
    imp (ad_bool_truth_correspondence _ _
      (gel_le_related _ _ _ _ (rgel_interval_rel tsk tsk_o HA) (rgel_cast_related _ _ Hd))).
    apply sub_nat_le_correspondence.
    - rgel_hepw arrR arrL Harr j tsk_o H1 (arta_add_related _ _ _ _ H1 Hd).
    - rgel_hepw arrR arrL Harr j tsk_o H1
        (rgel_absmax_related _ _ (gel_add_related _ _ _ _ H1 (rgel_interval_rel tsk tsk_o HA))).
  Qed.

  (** *** sum_of_workloads_is_at_most_bound_on_total_hep_workload *)

  Definition src_sum_of_workloads_is_at_most_bound_on_total_hep_workload : Prop :=
    ltac:(body_of (fun s : S2.statement_sum_of_workloads_is_at_most_bound_on_total_hep_workload =>
      s Task tcR maR Job jtR jaR costR ppR)).
  Definition tgt_sum_of_workloads_is_at_most_bound_on_total_hep_workload : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_sum_of_workloads_is_at_most_bound_on_total_hep_workload
      Task dT Job dJ tcL maL jtL jaL costL ppL)).

  Theorem sum_of_workloads_is_at_most_bound_on_total_hep_workload_correspondence :
    PropSPropRel src_sum_of_workloads_is_at_most_bound_on_total_hep_workload
      tgt_sum_of_workloads_is_at_most_bound_on_total_hep_workload.
  Proof.
    unfold src_sum_of_workloads_is_at_most_bound_on_total_hep_workload,
      tgt_sum_of_workloads_is_at_most_bound_on_total_hep_workload.
    apply rsi_forall_arr. intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    imp (arta_valid_job_costs_rel Task Job tcR tcL Htc jtR jtL Hjt costR costL Hcost arrR arrL Harr).
    apply arta_forall_list. intros tsR tsL Hts.
    imp (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma).
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    rgel_busy_prefix arrR arrL Harr tsR tsL Hts tsk LR LL HL j t1R t1L H1 t2R t2L H2 dR dL Hd.
    have HA := arta_sub_related _ _ _ _ (Hja j) H1.
    apply sub_nat_le_correspondence.
    - apply rbf_sum_filtered_related; [| |exact Hts].
      + intro o. rgel_hepw arrR arrL Harr j o H1 (arta_add_related _ _ _ _ H1 Hd).
      + intro o. exact (rbf_neq_related Task o tsk).
    - rgel_sum tsR tsL Hts tsk HA Hd.
  Qed.

  (** *** instantiated_task_interference_is_bounded *)

  Definition src_instantiated_task_interference_is_bounded : Prop :=
    ltac:(body_of (fun s : S2.statement_instantiated_task_interference_is_bounded =>
      s Task tcR maR Job jtR jaR costR ppR)).
  Definition tgt_instantiated_task_interference_is_bounded : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_instantiated_task_interference_is_bounded
      Task dT Job dJ tcL maL jtL jaL costL ppL)).

  Theorem instantiated_task_interference_is_bounded_correspondence :
    PropSPropRel src_instantiated_task_interference_is_bounded tgt_instantiated_task_interference_is_bounded.
  Proof.
    unfold src_instantiated_task_interference_is_bounded, tgt_instantiated_task_interference_is_bounded.
    apply rsi_forall_arr. intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply rsi_forall_sched. intros sR sL Hs.
    have Hjr := rgel_basic_ready_at sR sL Hs.
    imp (rsi_valid_schedule_rel sR sL Hs arrR arrL Harr _ _ Hjr).
    imp (arta_valid_job_costs_rel Task Job tcR tcL Htc jtR jtL Hjt costR costL Hcost arrR arrL Harr).
    apply arta_forall_list. intros tsR tsL Hts.
    imp (rgel_all_jobs_from_taskset_rel arrR arrL Harr tsR tsL Hts).
    imp (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma).
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply rgel_forall_fun. intros pR pL Hp.
    imp (PIC.priority_inversion_is_bounded_by_correspondence Task Job jtR jtL Hjt jaR jaL Hja costR costL Hcost
      PStateR PStateL rsi_jsvc arrR arrL Harr sR sL (rsi_hs_jsvc sR sL Hs) _ _ rgel_gel_rel tsk _ _ Hp).
    apply ad_forall_nat_correspondence => LR LL HL.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    imp (sub_nat_eq_correspondence _ _ _ _ HL
      (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts LR LL HL)).
    refine (task_interference_is_bounded_by_correspondence Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja
      costR costL Hcost sR sL Hs arrR arrL Harr _ _ (rsi_interference_rel sR sL Hs arrR arrL Harr _ _ rgel_gel_rel)
      _ _ (rsi_workload_rel sR sL Hs arrR arrL Harr _ _ rgel_gel_rel) tsk _ _ _).
    intros xR xL dR dL Hx Hd.
    refine (arta_add_related _ _ _ _ (Hp _ _ Hx) _).
    rgel_sum tsR tsL Hts tsk Hx Hd.
  Qed.

  (** *** The four search-space definitions *)

  Theorem task_rbf_changes_at_correspondence (tsk : Task) (AR : nat) (AL : Lean.Nat) :
    SubNatRel AR AL ->
    SvcBoolRel (@S2.task_rbf_changes_at Task tcR maR tsk AR)
      (I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_task_rbf_changes_at Task dT tcL maL tsk AL).
  Proof.
    intro HA. unfold S2.task_rbf_changes_at.
    cbn [I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_task_rbf_changes_at].
    exact (rgel_nat_neqb_related _ _ _ _
      (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _ HA)
      (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
        (svc_target_add_related _ _ _ _ HA (sub_nat_rel_canonical (S O))))).
  Qed.

  Theorem bound_on_total_hep_workload_changes_at_correspondence tsR tsL (Hts : ArListRel tsR tsL) (tsk : Task)
      (AR : nat) (AL : Lean.Nat) :
    SubNatRel AR AL ->
    SvcBoolRel (@S2.bound_on_total_hep_workload_changes_at Task ppR tsR tsk AR)
      (I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_bound_on_total_hep_workload_changes_at Task dT ppL tsL tsk AL).
  Proof.
    intro HA. unfold S2.bound_on_total_hep_workload_changes_at.
    cbn [I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_bound_on_total_hep_workload_changes_at].
    apply rgel_has_related; [|exact Hts]. intro tsko.
    exact (ar_bool_and_related _ _ _ _ (rbf_neq_related Task tsk tsko)
      (rgel_int_neq_related _ _ _ _
        (rgel_interval_rel tsk tsko (svc_target_sub_related _ _ _ _ HA (sub_nat_rel_canonical (S O))))
        (rgel_interval_rel tsk tsko HA))).
  Qed.

  Theorem priority_inversion_changes_at_correspondence pR pL (Hp : RgelFunRel pR pL) (AR : nat) (AL : Lean.Nat) :
    SubNatRel AR AL ->
    SvcBoolRel (@S2.priority_inversion_changes_at pR AR)
      (I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_priority_inversion_changes_at pL AL).
  Proof.
    intro HA. unfold S2.priority_inversion_changes_at.
    cbn [I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_priority_inversion_changes_at].
    exact (rgel_nat_neqb_related _ _ _ _ (Hp _ _ (svc_target_sub_related _ _ _ _ HA (sub_nat_rel_canonical (S O))))
      (Hp _ _ HA)).
  Qed.

  Theorem is_in_search_space_correspondence tsR tsL (Hts : ArListRel tsR tsL) (tsk : Task) pR pL
      (Hp : RgelFunRel pR pL) (LR AR : nat) (LL AL : Lean.Nat) :
    SubNatRel LR LL -> SubNatRel AR AL ->
    SvcBoolRel (@S2.is_in_search_space Task tcR maR ppR tsR tsk pR LR AR)
      (I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_is_in_search_space Task dT tcL maL ppL tsL tsk pL LL AL).
  Proof.
    intros HL HA. unfold S2.is_in_search_space.
    cbn [I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_is_in_search_space].
    refine (ar_bool_and_related _ _ _ _ (svc_decide_lt_related _ _ _ _ HA HL) _).
    refine (PPC.pp_bool_or_related _ _ _ _ (PPC.pp_bool_or_related _ _ _ _ _ _) _).
    - exact (priority_inversion_changes_at_correspondence pR pL Hp AR AL HA).
    - exact (task_rbf_changes_at_correspondence tsk AR AL HA).
    - exact (bound_on_total_hep_workload_changes_at_correspondence tsR tsL Hts tsk AR AL HA).
  Qed.

  (** *** The abstract search space over the total interference bound *)

  Local Ltac rgel_ss tsR tsL Hts tsk pR pL Hp HL HA :=
    apply arta_search_space_rel; [|exact HL|exact HA];
    let xR := fresh "xR" in let xL := fresh "xL" in let dR := fresh "dR" in let dL := fresh "dL" in
    let Hx := fresh "Hx" in let Hd := fresh "Hd" in
    intros xR xL dR dL Hx Hd;
    refine (arta_add_related _ _ _ _ (arta_sub_related _ _ _ _
      (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
        (arta_add_related _ _ _ _ Hx (sub_nat_rel_canonical 1))) (Htc tsk))
      (arta_add_related _ _ _ _ (Hp _ _ Hx) _));
    rgel_sum tsR tsL Hts tsk Hx Hd.

  Local Ltac rgel_rmax tsR tsL Hts tsk pR pL Hp LR LL HL RR RL HR :=
    let AR := fresh "AR" in let AL := fresh "AL" in let HA := fresh "HA" in
    let FR := fresh "FR" in let FL := fresh "FL" in let HF := fresh "HF" in
    apply ad_forall_nat_correspondence; intros AR AL HA;
    (apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _
      (is_in_search_space_correspondence tsR tsL Hts tsk pR pL Hp LR AR LL AL HL HA))|]);
    apply ad_exists_nat_correspondence; intros FR FL HF;
    apply ad_and_correspondence;
    [ apply sub_nat_le_correspondence; [|exact (arta_add_related _ _ _ _ HA HF)];
      refine (arta_add_related _ _ _ _ (arta_add_related _ _ _ _ (Hp _ _ HA)
        (arta_sub_related _ _ _ _ (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
          (arta_add_related _ _ _ _ HA (sub_nat_rel_canonical 1))) (arta_sub_related _ _ _ _ (Htc tsk) (Hrtc tsk)))) _);
      rgel_sum tsR tsL Hts tsk HA (arta_add_related _ _ _ _ HA HF)
    | exact (sub_nat_le_correspondence _ _ _ _
        (arta_add_related _ _ _ _ HF (arta_sub_related _ _ _ _ (Htc tsk) (Hrtc tsk))) HR) ].

  (** *** A_is_in_concrete_search_space *)

  Definition src_A_is_in_concrete_search_space : Prop :=
    ltac:(body_of (fun s : S2.statement_A_is_in_concrete_search_space => s Task tcR maR ppR)).
  Definition tgt_A_is_in_concrete_search_space : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_A_is_in_concrete_search_space
      Task dT tcL maL ppL)).

  Theorem A_is_in_concrete_search_space_correspondence :
    PropSPropRel src_A_is_in_concrete_search_space tgt_A_is_in_concrete_search_space.
  Proof.
    unfold src_A_is_in_concrete_search_space, tgt_A_is_in_concrete_search_space.
    apply arta_forall_list. intros tsR tsL Hts.
    imp (rgel_valid_taskset_curve_rel tsR tsL Hts maR maL Hma).
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply rgel_forall_fun. intros pR pL Hp.
    apply ad_forall_nat_correspondence => LR LL HL.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Htc tsk)).
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hma tsk _ _ (sub_nat_rel_canonical 1))).
    apply ad_forall_nat_correspondence => AR AL HA.
    apply ad_imp_correspondence; [rgel_ss tsR tsL Hts tsk pR pL Hp HL HA|].
    exact (ad_bool_truth_correspondence _ _
      (is_in_search_space_correspondence tsR tsL Hts tsk pR pL Hp LR AR LL AL HL HA)).
  Qed.

  (** *** correct_search_space *)

  Definition src_correct_search_space : Prop :=
    ltac:(body_of (fun s : S2.statement_correct_search_space => s Task tcR rtcR maR ppR)).
  Definition tgt_correct_search_space : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_correct_search_space Task dT tcL rtcL maL ppL)).

  Theorem correct_search_space_correspondence :
    PropSPropRel src_correct_search_space tgt_correct_search_space.
  Proof.
    unfold src_correct_search_space, tgt_correct_search_space.
    apply arta_forall_list. intros tsR tsL Hts.
    imp (rgel_valid_taskset_curve_rel tsR tsL Hts maR maL Hma).
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply rgel_forall_fun. intros pR pL Hp.
    apply ad_forall_nat_correspondence => LR LL HL.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    apply ad_forall_nat_correspondence => RR RL HR.
    apply ad_imp_correspondence; [rgel_rmax tsR tsL Hts tsk pR pL Hp LR LL HL RR RL HR|].
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Htc tsk)).
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hma tsk _ _ (sub_nat_rel_canonical 1))).
    apply ad_forall_nat_correspondence => AR AL HA.
    apply ad_imp_correspondence; [rgel_ss tsR tsL Hts tsk pR pL Hp HL HA|].
    apply ad_exists_nat_correspondence => FR FL HF.
    have HAF := arta_add_related _ _ _ _ HA HF.
    have Hcr := arta_sub_related _ _ _ _ (Htc tsk) (Hrtc tsk).
    apply ad_and_correspondence.
    - apply sub_nat_le_correspondence; [|exact HAF].
      refine (arta_add_related _ _ _ _ (arta_sub_related _ _ _ _
        (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
          (arta_add_related _ _ _ _ HA (sub_nat_rel_canonical 1))) Hcr) (arta_add_related _ _ _ _ (Hp _ _ HA) _)).
      rgel_sum tsR tsL Hts tsk HA HAF.
    - exact (sub_nat_le_correspondence _ _ _ _ (arta_add_related _ _ _ _ HF Hcr) HR).
  Qed.

  (** *** uniprocessor_response_time_bound_edf *)

  Definition src_uniprocessor_response_time_bound_edf : Prop :=
    ltac:(body_of (fun s : S2.statement_uniprocessor_response_time_bound_edf =>
      s Task tcR rtcR maR Job jtR jaR costR jpR ppR)).
  Definition tgt_uniprocessor_response_time_bound_edf : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Rta_Ideal_Gel_BoundedPi_uniprocessor_response_time_bound_edf
      Task dT Job dJ tcL rtcL maL jtL jaL costL jpL ppL)).

  Theorem uniprocessor_response_time_bound_edf_correspondence :
    PropSPropRel src_uniprocessor_response_time_bound_edf tgt_uniprocessor_response_time_bound_edf.
  Proof.
    unfold src_uniprocessor_response_time_bound_edf, tgt_uniprocessor_response_time_bound_edf.
    apply rsi_forall_arr. intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply rsi_forall_sched. intros sR sL Hs.
    have Hjr := rgel_basic_ready_at sR sL Hs.
    imp (rsi_valid_schedule_rel sR sL Hs arrR arrL Harr _ _ Hjr).
    imp (rgel_respects_jlfp_rel sR sL Hs arrR arrL Harr jpR jpL Hjp _ _ Hjr _ _ rgel_gel_rel).
    imp (arta_valid_job_costs_rel Task Job tcR tcL Htc jtR jtL Hjt costR costL Hcost arrR arrL Harr).
    apply arta_forall_list. intros tsR tsL Hts.
    imp (rgel_all_jobs_from_taskset_rel arrR arrL Harr tsR tsL Hts).
    imp (rgel_valid_taskset_curve_rel tsR tsL Hts maR maL Hma).
    imp (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma).
    apply ad_forall_identity_correspondence => tsk.
    imp (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    imp (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL rsi_jsvc
      sR sL (rsi_hs_jsvc sR sL Hs) arrR arrL Harr).
    imp (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rtcR rtcL Hrtc
      jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk).
    apply rgel_forall_fun. intros pR pL Hp.
    imp (PIC.priority_inversion_is_bounded_by_correspondence Task Job jtR jtL Hjt jaR jaL Hja costR costL Hcost
      PStateR PStateL rsi_jsvc arrR arrL Harr sR sL (rsi_hs_jsvc sR sL Hs) _ _ rgel_gel_rel tsk _ _ Hp).
    imp (rsi_work_conserving_related sR sL Hs arrR arrL Harr _ _ Hjr).
    apply ad_forall_nat_correspondence => LR LL HL.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
    imp (sub_nat_eq_correspondence _ _ _ _ HL
      (total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts LR LL HL)).
    apply ad_forall_nat_correspondence => RR RL HR.
    apply ad_imp_correspondence; [rgel_rmax tsR tsL Hts tsk pR pL Hp LR LL HL RR RL HR|].
    exact (arta_response_time_bound_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL Hcost
      sR sL Hs arrR arrL Harr tsk RR RL HR).
  Qed.
End IdealIwInstantiation.
