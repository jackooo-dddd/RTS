(* Helper-only copy of the accepted certificates/analysis_abstract_restricted_supply_iw_readiness/IwReadinessCorrespondence.v,
   re-bound to this export: the statement correspondences (whose statements are not exported here) and
   rsi_exists_identity / rsi_work_conserving_related (Lean Exists is not in this export; unused here) are
   removed; every kept block is byte-identical. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import IwReadinessSemanticSource.
From prosa Require Import analysis.abstract.definitions analysis.definitions.readiness_interference model.job.properties
  model.processor.platform_properties model.processor.supply model.schedule.work_conserving
  analysis.definitions.work_bearing_readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskIbfReadiness ImportedSubadditivity.
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
  SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations
  SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskPreemptionParametersCorrespondence SequentialityCorrespondence
  IbfTaskHelpers IbfSupplyTaskCorrespondence ServiceInversionPredCorrespondence
  InterferenceCorrespondence AbstractDefinitionsBusyInterval PriorityBaseAdapter
  ReadinessInterferenceCorrespondence ReadinessAwareCorrespondence.
From FoundationCertificates Require Import IbfTaskFullHelpers.

Module I := ImportedTaskIbfReadiness.
Module S := IwReadinessSemanticSource.IwReadinessSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module SUP := FoundationCertificates.SupplyScheduleOperations.
Module SUPC := FoundationCertificates.SupplyCorrespondence.
Module JSO := FoundationCertificates.JitterSvcScheduleOperations.
Module IBST := FoundationCertificates.IbfSupplyTaskCorrespondence.
Module SIPC := FoundationCertificates.ServiceInversionPredCorrespondence.
Module IFC := FoundationCertificates.InterferenceCorrespondence.
Module B := BusyIntervalClassicalSemanticSource.BusyIntervalClassicalSemanticSource.
Module SIP := ServiceInversionPredSemanticSource.ServiceInversionPredSemanticSource.
Module IFS := InterferenceSemanticSource.InterferenceSemanticSource.
Module IBTS := IbfTaskSemanticSource.IbfTaskSemanticSource.
Module RA := ReadinessAwareSemanticSource.ReadinessAwareSemanticSource.

(** Statement correspondences for
    [analysis/abstract/restricted_supply/iw_readiness.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.
    Inputs: processor states by the accepted two-sided [SvcProcessorStateRel]
    together with the pointwise [supply_on] relation, from which the
    preemption and supply family relations are built ([rsi_jsvc], [rsi_sup]),
    exactly as in the accepted restricted-supply iw_instantiation certificate;
    [job_arrival], [job_cost] pointwise; [JobTask] by [AdJobTaskRel].  Arrival
    sequences, schedules, JLFP policies (pointwise on Booleans), jobs, tasks and
    instants are covered in both directions.  The readiness instance is
    quantified before the arrival sequence and the schedule; each statement is
    first rewritten by a pure binder reordering (a Prop/SProp equivalence on
    both sides; no functional extensionality) so that the readiness instance
    is quantified after the schedule, and is then covered at the statement's
    schedule pair (the accepted pair cover: [job_ready] related on the pair,
    completed on either side by [&& pending]).

    The two section-local instances are related field by field: blackout by
    the accepted supply certificate, the higher-or-equal-priority interference
    and interfering workload by the accepted interference definition
    certificate, the readiness-aware service inversion by the accepted
    readiness-aware certificate, and [has_supply && ~~ some_hep_job_ready] by
    the accepted supply and readiness-interference certificates; Booleans
    counted as naturals by the accepted bool-to-nat lemmas.  The explicit
    interval sums of the statements are related by the accepted interval-sum
    relation (the Lean side is the kernel-guarded list form of the
    [Finset.Ico] sum).  The abstract notions are the accepted
    abstract-definitions and IBF/task certificates over these instance
    relations; the classical ones are related by unfolding over the accepted
    completion and scheduling observations of the schedule pair.  No source or
    target theorem is used. *)

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

Section IwReadiness.
  Context (Task Job : eqType).
  Let dT := ad_decidable_eq Task.
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SSO.SvcProcessorStateRel Job PStateR PStateL.
  Hypothesis Hsupply_on : forall sR sL cR,
    SSO.svc_ps_state_rel Job PStateR PStateL R sR sL ->
    SubNatRel (@prosa.behavior.schedule.supply_on Job PStateR sR cR)
      (SUP.supply_target_supply_on Job PStateL sL (SSO.svc_ps_core_to_target Job PStateR PStateL R cR)).
  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.

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
      (PL : I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PStateL -> SProp) :
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

  Lemma rsi_unit_supply_rel :
    PropSPropRel (@prosa.model.processor.platform_properties.unit_supply_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.unit_supply_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model].
    apply rsi_forall_state. intros sR sL Hs.
    exact (sub_nat_le_correspondence _ _ _ _ (SUP.supply_ps_supply_in_related Job PStateR PStateL rsi_sup sR sL Hs)
      (sub_nat_rel_canonical 1)).
  Qed.

  Lemma rsi_fully_consuming_rel :
    PropSPropRel (@prosa.model.processor.platform_properties.fully_consuming_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.fully_consuming_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model].
    apply ad_forall_identity_correspondence. intro j.
    apply rsi_forall_sched. intros sR sL Hs.
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (ibt_sched_at Job PStateR PStateL R sR sL Hs j _ _ Ht))|].
    exact (sub_nat_eq_correspondence _ _ _ _ (ad_service_at_related Job PStateR PStateL R sR sL Hs j tR tL Ht)
      (SUPC.supply_at_correspondence Job PStateR PStateL rsi_sup sR sL (rsi_hs_sup sR sL Hs) tR tL Ht)).
  Qed.

  (** *** Binder reordering (both sides, no extensionality) *)

  Lemma iwr_reorder_va {JR JL AR AL SR SL : Type} (VR : AR -> Prop) (VL : AL -> SProp)
      (PR : JR -> AR -> SR -> Prop) (PL : JL -> AL -> SL -> SProp) :
    PropSPropRel (forall a, VR a -> forall s (jr : JR), PR jr a s)
      (forall a, VL a -> forall s (jr : JL), PL jr a s) ->
    PropSPropRel (forall (jr : JR) a, VR a -> forall s, PR jr a s)
      (forall (jr : JL) a, VL a -> forall s, PL jr a s).
  Proof.
    intros [f g]. split.
    - intros HR jr a hv s. exact (f (fun a hv s jr => HR jr a hv s) a hv s jr).
    - intros HL jr a hv s. exact (g (fun a hv s jr => HL jr a hv s) a hv s jr).
  Qed.

  Lemma iwr_reorder_nv {JR JL AR AL SR SL : Type}
      (PR : JR -> AR -> SR -> Prop) (PL : JL -> AL -> SL -> SProp) :
    PropSPropRel (forall a s (jr : JR), PR jr a s) (forall a s (jr : JL), PL jr a s) ->
    PropSPropRel (forall (jr : JR) a s, PR jr a s) (forall (jr : JL) a s, PL jr a s).
  Proof.
    intros [f g]. split.
    - intros HR jr a s. exact (f (fun a s jr => HR jr a s) a s jr).
    - intros HL jr a s. exact (g (fun a s jr => HL jr a s) a s jr).
  Qed.

  (** *** Observations of a schedule pair *)

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL.

    Let Hsa := ibt_sched_at Job PStateR PStateL R sR sL Hs.
    Let COMPLETED := ibt_completed Job PStateR PStateL R costR costL Hcost sR sL Hs.
    Let PENDING := ibt_pending Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs.

    Lemma rsi_receives_service_at_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
      ArBoolRel (@prosa.behavior.service.receives_service_at Job PStateR sR j tR)
        (I.Prosa_Behavior_Service_receives_service_at Job dJ PStateL sL j tL).
    Proof.
      unfold prosa.behavior.service.receives_service_at.
      cbn [I.Prosa_Behavior_Service_receives_service_at].
      exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O)
        (ad_service_at_related Job PStateR PStateL R sR sL Hs j tR tL Ht)).
    Qed.

    (** **** Readiness at this schedule pair *)

    Definition RsiJrAt (jrR : @prosa.behavior.ready.JobReady Job PStateR costR jaR)
        (jrL : I.Prosa_Behavior_Ready_JobReady Job dJ PStateL costL jaL) : SProp :=
      forall j tR tL, SubNatRel tR tL ->
        ArBoolRel (@prosa.behavior.ready.job_ready Job PStateR costR jaR jrR sR j tR)
          (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PStateL costL jaL jrL sL j tL).

    Definition rsi_jr_to_target (jrR : @prosa.behavior.ready.JobReady Job PStateR costR jaR) :
        I.Prosa_Behavior_Ready_JobReady Job dJ PStateL costL jaL :=
      I.Prosa_Behavior_Ready_JobReady_mk Job dJ PStateL costL jaL
        (fun s j tL => I.Bool_and
          (ar_bool_to_imported (@prosa.behavior.ready.job_ready Job PStateR costR jaR jrR sR j
            (sub_nat_to_rocq tL)))
          (I.Prosa_Behavior_Service_pending Job dJ PStateL s costL jaL j tL))
        (fun s j t H => rsi_and_true_right _ _ H).

    Definition rsi_jr_to_source (jrL : I.Prosa_Behavior_Ready_JobReady Job dJ PStateL costL jaL) :
        @prosa.behavior.ready.JobReady Job PStateR costR jaR :=
      @prosa.behavior.ready.Build_JobReady Job PStateR costR jaR
        (fun s j t => ar_bool_to_rocq
          (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PStateL costL jaL jrL sL j
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
      have Hlaw := I.Prosa_Behavior_Ready_JobReady_ready_implies_pending Job dJ PStateL costL jaL jrL sL j tL.
      destruct Ht.
      apply rsi_and_absorb_source. intro Hr.
      exact (rsi_bool_true_of_rel _ _ Hpd (Hlaw Hr)).
    Qed.

    Lemma rsi_forall_jr (PRr : @prosa.behavior.ready.JobReady Job PStateR costR jaR -> Prop)
        (PLr : I.Prosa_Behavior_Ready_JobReady Job dJ PStateL costL jaL -> SProp) :
      (forall jrR jrL, RsiJrAt jrR jrL -> PropSPropRel (PRr jrR) (PLr jrL)) ->
      PropSPropRel (forall jr, PRr jr) (forall jr, PLr jr).
    Proof.
      exact (arta_forall_cover _ _ RsiJrAt rsi_jr_to_target rsi_jr_to_source
        rsi_jr_to_target_rel rsi_jr_to_source_rel PRr PLr).
    Qed.

    Section Arr.
      Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
      Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
      Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

      Section Ready.
        Variable jrR : @prosa.behavior.ready.JobReady Job PStateR costR jaR.
        Variable jrL : I.Prosa_Behavior_Ready_JobReady Job dJ PStateL costL jaL.
        Hypothesis Hjr : RsiJrAt jrR jrL.

        Lemma rsi_valid_schedule_rel :
          PropSPropRel (@prosa.behavior.ready.valid_schedule Job jaR PStateR sR costR jrR arrR)
            (I.Prosa_Behavior_Ready_valid_schedule Job dJ jaL PStateL sL costL jrL arrL).
        Proof.
          unfold prosa.behavior.ready.valid_schedule, prosa.behavior.ready.jobs_must_be_ready_to_execute.
          cbn [I.Prosa_Behavior_Ready_valid_schedule I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute].
          apply ar_and_correspondence;
            [exact (ibt_come_from Job PStateR PStateL R sR sL Hs arrR arrL Harr)|].
          apply ar_forall_identity_correspondence. intro j.
          apply ar_forall_nat_correspondence. intros tR tL Ht.
          apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j _ _ Ht))|].
          exact (ar_bool_truth_correspondence _ _ (Hjr j tR tL Ht)).
        Qed.

        Lemma rsi_backlogged_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
          ArBoolRel (@prosa.behavior.ready.backlogged Job PStateR costR jaR jrR sR j tR)
            (I.Prosa_Behavior_Ready_backlogged Job dJ PStateL costL jaL jrL sL j tL).
        Proof.
          unfold prosa.behavior.ready.backlogged. cbn [I.Prosa_Behavior_Ready_backlogged].
          exact (ar_bool_and_related _ _ _ _ (Hjr j tR tL Ht) (svc_bool_not_related _ _ (Hsa j tR tL Ht))).
        Qed.

        Section Policy.
          Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
          Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
          Hypothesis Hp : RsiJLFPRel pR pL.

          (** **** The instantiated interference and interfering workload *)

          Let IR := @S.rs_readiness_jlfp_interference Job jaR costR PStateR jrR arrR sR pR.
          Let IL := I.Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interference
            Job dJ jaL costL PStateL jrL arrL sL pL.
          Let WR := @S.rs_readiness_jlfp_interfering_workload Job jaR costR PStateR jrR arrR sR pR.
          Let WL := I.Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interfering_workload
            Job dJ jaL costL PStateL jrL arrL sL pL.

          Lemma rsi_some_hep_ready_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
            ArBoolRel (@some_hep_job_ready Job jaR costR PStateR jrR arrR sR pR j tR)
              (I.Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready
                Job dJ jaL costL PStateL jrL arrL sL pL j tL).
          Proof.
            exact (FoundationCertificates.ReadinessInterferenceCorrespondence.some_hep_job_ready_correspondence Job PStateR PStateL sR sL jaR jaL costR costL
              jrR jrL Hjr arrR arrL Harr pR pL Hp j tR tL Ht).
          Qed.

          Lemma rsi_ra_service_inversion_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
            ArBoolRel (@RA.service_inversion Job jaR costR PStateR jrR arrR sR pR j tR)
              (I.Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion
                Job dJ jaL costL PStateL jrL arrL sL pL j tL).
          Proof.
            exact (FoundationCertificates.ReadinessAwareCorrespondence.service_inversion_correspondence Job PStateR PStateL rsi_jsvc sR sL (rsi_hs_jsvc sR sL Hs)
              jaR jaL costR costL jrR jrL Hjr arrR arrL Harr pR pL Hp j tR tL Ht).
          Qed.

          Lemma rsi_readiness_pred_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
            ArBoolRel (@prosa.model.processor.supply.has_supply Job PStateR sR tR
                && ~~ @some_hep_job_ready Job jaR costR PStateR jrR arrR sR pR j tR)
              (I.Bool_and (I.Prosa_Model_Processor_Supply_has_supply Job dJ PStateL sL tL)
                (I.Bool_not (I.Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready
                  Job dJ jaL costL PStateL jrL arrL sL pL j tL))).
          Proof.
            exact (ar_bool_and_related _ _ _ _
              (SUPC.has_supply_correspondence Job PStateR PStateL rsi_sup sR sL (rsi_hs_sup sR sL Hs) _ _ Ht)
              (svc_bool_not_related _ _ (rsi_some_hep_ready_related j tR tL Ht))).
          Qed.

          Lemma rsi_interference_rel : AdInterferenceRel Job IR IL.
          Proof.
            intros j t. unfold AdBoolRel, IR, IL.
            cbn [I.Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interference
              I.Prosa_Analysis_Abstract_Definitions_Interference_interference].
            have Ht := sub_nat_rel_canonical t.
            apply IFC.if_bool_or_related; [apply IFC.if_bool_or_related; [apply IFC.if_bool_or_related|]|].
            - exact (SUPC.is_blackout_correspondence Job PStateR PStateL rsi_sup sR sL (rsi_hs_sup sR sL Hs) _ _ Ht).
            - exact (IFC.another_hep_job_interference_correspondence Job PStateR PStateL rsi_jsvc sR sL
                (rsi_hs_jsvc sR sL Hs) arrR arrL Harr pR pL Hp j _ _ Ht).
            - exact (rsi_ra_service_inversion_related j _ _ Ht).
            - exact (rsi_readiness_pred_related j _ _ Ht).
          Qed.

          Lemma rsi_workload_rel : AdInterferingWorkloadRel Job WR WL.
          Proof.
            intros j t. unfold WR, WL.
            cbn [I.Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interfering_workload
              I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload_interfering_workload].
            have Ht := sub_nat_rel_canonical t.
            apply arta_add_related; [apply arta_add_related; [apply arta_add_related|]|].
            - exact (ad_bool_to_nat_related _ _
                (SUPC.is_blackout_correspondence Job PStateR PStateL rsi_sup sR sL (rsi_hs_sup sR sL Hs) _ _ Ht)).
            - exact (IFC.other_hep_jobs_interfering_workload_correspondence Job costR costL Hcost arrR arrL Harr
                pR pL Hp j _ _ Ht).
            - exact (ad_bool_to_nat_related _ _ (rsi_ra_service_inversion_related j _ _ Ht)).
            - exact (ad_bool_to_nat_related _ _ (rsi_readiness_pred_related j _ _ Ht)).
          Qed.

          Lemma rsi_interference_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
            AdBoolRel (@prosa.analysis.abstract.definitions.interference Job IR j tR)
              (I.Prosa_Analysis_Abstract_Definitions_Interference_interference Job dJ IL j tL).
          Proof. destruct Ht. exact (rsi_interference_rel j tR). Qed.

          (** The explicit interval sum of the counted readiness predicate. *)
          Lemma rsi_readiness_sum_related (j : Job) t1R t1L t2R t2L :
            SubNatRel t1R t1L -> SubNatRel t2R t2L ->
            SubNatRel (\sum_(t1R <= t < t2R) (@prosa.model.processor.supply.has_supply Job PStateR sR t
                && ~~ @some_hep_job_ready Job jaR costR PStateR jrR arrR sR pR j t))
              (svc_target_interval_value t1L t2L (fun t => I.Bool_toNat
                (I.Bool_and (I.Prosa_Model_Processor_Supply_has_supply Job dJ PStateL sL t)
                  (I.Bool_not (I.Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready
                    Job dJ jaL costL PStateL jrL arrL sL pL j t))))).
          Proof.
            intros H1 H2.
            apply svc_interval_sum_related; [exact H1 | exact H2 |].
            intros tR tL Ht. exact (ad_bool_to_nat_related _ _ (rsi_readiness_pred_related j tR tL Ht)).
          Qed.

          Lemma rsi_ra_cumulative_service_inversion_related (j : Job) t1R t1L t2R t2L :
            SubNatRel t1R t1L -> SubNatRel t2R t2L ->
            SubNatRel (@RA.cumulative_service_inversion Job jaR costR PStateR jrR arrR sR pR j t1R t2R)
              (I.Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_cumulative_service_inversion
                Job dJ jaL costL PStateL jrL arrL sL pL j t1L t2L).
          Proof.
            exact (FoundationCertificates.ReadinessAwareCorrespondence.cumulative_service_inversion_correspondence Job PStateR PStateL rsi_jsvc sR sL
              (rsi_hs_jsvc sR sL Hs) jaR jaL costR costL jrR jrL Hjr arrR arrL Harr pR pL Hp j t1R t1L t2R t2L).
          Qed.

          (** **** Classical busy intervals *)

          Lemma rsi_quiet_time_related (j : Job) (tR : nat) (tL : Lean.Nat) :
            SubNatRel tR tL ->
            PropSPropRel (@B.quiet_time Job jaR costR PStateR arrR sR pR j tR)
              (I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time
                Job dJ jaL costL PStateL arrL sL pL j tL).
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

          Lemma rsi_busy_interval_prefix_related (j : Job) t1R t1L t2R t2L :
            SubNatRel t1R t1L -> SubNatRel t2R t2L ->
            PropSPropRel (@B.busy_interval_prefix Job jaR costR PStateR arrR sR pR j t1R t2R)
              (I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix
                Job dJ jaL costL PStateL arrL sL pL j t1L t2L).
          Proof.
            intros H1 H2. unfold B.busy_interval_prefix.
            cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix].
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
              (I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval
                Job dJ jaL costL PStateL arrL sL pL j t1L t2L).
          Proof.
            intros H1 H2. unfold B.busy_interval.
            cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval].
            apply ar_and_correspondence; [exact (rsi_busy_interval_prefix_related j _ _ _ _ H1 H2)|].
            exact (rsi_quiet_time_related j _ _ H2).
          Qed.

          (** **** Abstract busy intervals over the instantiation *)

          Lemma rsi_ab_quiet_time_related (j : Job) (tR : nat) (tL : Lean.Nat) :
            SubNatRel tR tL ->
            AdBoolRel (@prosa.analysis.abstract.definitions.quiet_time Job jaR costR PStateR sR IR WR j tR)
              (I.Prosa_Analysis_Abstract_Definitions_quiet_time Job dJ IL WL jaL costL PStateL sL j tL).
          Proof.
            exact (ad_quiet_time_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
              IR IL rsi_interference_rel WR WL rsi_workload_rel j tR tL).
          Qed.

          Lemma rsi_ab_busy_interval_prefix_related (j : Job) t1R t1L t2R t2L :
            SubNatRel t1R t1L -> SubNatRel t2R t2L ->
            PropSPropRel (@prosa.analysis.abstract.definitions.busy_interval_prefix Job jaR costR PStateR sR IR WR
                j t1R t2R)
              (I.Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job dJ IL WL jaL costL PStateL sL
                j t1L t2L).
          Proof.
            exact (ad_busy_interval_prefix_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL
              Hcost IR IL rsi_interference_rel WR WL rsi_workload_rel j t1R t2R t1L t2L).
          Qed.

          Lemma rsi_ab_busy_interval_related (j : Job) t1R t1L t2R t2L :
            SubNatRel t1R t1L -> SubNatRel t2R t2L ->
            PropSPropRel (@prosa.analysis.abstract.definitions.busy_interval Job jaR costR PStateR sR IR WR
                j t1R t2R)
              (I.Prosa_Analysis_Abstract_Definitions_busy_interval Job dJ IL WL jaL costL PStateL sL
                j t1L t2L).
          Proof.
            exact (ad_busy_interval_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL
              Hcost IR IL rsi_interference_rel WR WL rsi_workload_rel j t1R t2R t1L t2L).
          Qed.
        End Policy.
      End Ready.
    End Arr.
  End Sched.

End IwReadiness.
