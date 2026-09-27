From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import RsAbstractRtaSemanticSource.
From prosa Require Import analysis.abstract.definitions analysis.abstract.search_space model.job.properties
  model.processor.platform_properties model.processor.supply analysis.definitions.sbf.sbf
  analysis.definitions.sbf.pred analysis.abstract.restricted_supply.busy_sbf.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRsAbstractRta ImportedSubadditivity.
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
  SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations
  SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence
  IbfSupplyCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskPreemptionParametersCorrespondence PredCorrespondence BusySbfCorrespondence.

Module I := ImportedRsAbstractRta.
Module S := RsAbstractRtaSemanticSource.RsAbstractRtaSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module SUP := FoundationCertificates.SupplyScheduleOperations.
Module SUPC := FoundationCertificates.SupplyCorrespondence.
Module JSO := FoundationCertificates.JitterSvcScheduleOperations.
Module IBFS := FoundationCertificates.IbfSupplyCorrespondence.
Module PPC := FoundationCertificates.PreemptionParameterCorrespondence.
Module TPPC := FoundationCertificates.TaskPreemptionParametersCorrespondence.
Module PREDC := FoundationCertificates.PredCorrespondence.
Module BSBF := FoundationCertificates.BusySbfCorrespondence.
Module TPP := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.

(** Statement correspondences for
    [analysis/abstract/restricted_supply/abstract_rta.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.
    Inputs: processor states by the accepted two-sided [SvcProcessorStateRel]
    of the abstract-definitions family together with the pointwise relation
    of [supply_on] on related states (the supply field of the root
    processor-state relation).  From this one relation the preemption-parameter
    family's [SvcProcessorStateRel] ([rs_jsvc]) and the supply family's
    [SupplyProcessorStateRel] ([rs_sup]) are built field by field, so every
    family's certificates apply to one state relation and to every schedule
    related through it.  [job_arrival], [job_cost], [task_cost] and
    [task_rtct] pointwise by [SubNatRel]; [JobTask] by the accepted
    [AdJobTaskRel]; [JobPreemptable] by the accepted [PpJobPreemptableRel].
    Inputs quantified inside a statement are covered in both directions:
    processor states (platform properties), arrival sequences, schedules,
    task sets, [Interference] and [InterferingWorkload], supply-bound
    functions (by their field), interference-bound functions, tasks and jobs
    (identity), instants and durations.  Supply, blackouts, intra-supply
    interference, the busy SBF, unit SBFs, preemption and
    run-to-completion validity, work conservation, busy intervals, the
    interference bounds, the search space and the response-time bound are
    related by the accepted certificates of their families.  No source or
    target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section RsAbstractRta.
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

  Definition rs_jsvc : JSO.SvcProcessorStateRel Job PStateR PStateL := {|
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

  Definition rs_sup : SUP.SupplyProcessorStateRel Job PStateR PStateL := {|
    SUP.supply_ps_state_rel := SSO.svc_ps_state_rel Job PStateR PStateL R;
    SUP.supply_ps_core_to_target := SSO.svc_ps_core_to_target Job PStateR PStateL R;
    SUP.supply_ps_core_enumeration_rel := SSO.svc_ps_core_enumeration_rel Job PStateR PStateL R;
    SUP.supply_ps_supply_on_rel := Hsupply_on
  |}.

  Lemma rs_hs_sup sR sL :
    SSO.SvcScheduleRel Job PStateR PStateL R sR sL -> SUP.SupplyScheduleRel Job PStateR PStateL rs_sup sR sL.
  Proof. exact (fun Hs => Hs). Qed.

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

  Definition rs_sched_to_target (sR : SchedR) : SchedL :=
    fun tL => SSO.svc_ps_state_to_target Job PStateR PStateL R (sR (sub_nat_to_rocq tL)).
  Definition rs_sched_to_source (sL : SchedL) : SchedR :=
    fun tR => SSO.svc_ps_state_to_source Job PStateR PStateL R (sL (sub_nat_to_imported tR)).

  Lemma rs_forall_sched (PR : SchedR -> Prop) (PL : SchedL -> SProp) :
    (forall sR sL, SSO.SvcScheduleRel Job PStateR PStateL R sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    apply (arta_forall_cover _ _ (SSO.SvcScheduleRel Job PStateR PStateL R)
      rs_sched_to_target rs_sched_to_source).
    - intros sR tR tL Ht. unfold rs_sched_to_target. rewrite (arta_nat_input _ _ Ht).
      exact (SSO.svc_ps_state_rel_canonical Job PStateR PStateL R _).
    - intros sL tR tL Ht. destruct Ht.
      exact (SSO.svc_ps_state_rel_surjective Job PStateR PStateL R _).
  Qed.

  Definition rs_arr_to_source (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ) :
      prosa.behavior.arrival_sequence.arrival_sequence Job :=
    fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

  Lemma rs_forall_arr (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
      (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ -> SProp) :
    (forall aR aL, ArArrivalSequenceRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) ->
    PropSPropRel (forall a, PR a) (forall a, PL a).
  Proof.
    apply (arta_forall_cover _ _ (ArArrivalSequenceRel Job) (ar_arrival_sequence_to_imported Job)
      rs_arr_to_source (ar_arrival_sequence_canonical Job)).
    intros arrL tR tL Ht. unfold ArListRel, rs_arr_to_source.
    refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
    exact (sub_imported_eq_congr arrL _ _ Ht).
  Qed.

  Lemma rs_forall_state (PR : @prosa.behavior.schedule.State Job PStateR -> Prop)
      (PL : I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PStateL -> SProp) :
    (forall sR sL, SSO.svc_ps_state_rel Job PStateR PStateL R sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    exact (arta_forall_cover _ _ (SSO.svc_ps_state_rel Job PStateR PStateL R)
      (SSO.svc_ps_state_to_target Job PStateR PStateL R) (SSO.svc_ps_state_to_source Job PStateR PStateL R)
      (SSO.svc_ps_state_rel_canonical Job PStateR PStateL R)
      (SSO.svc_ps_state_rel_surjective Job PStateR PStateL R) PR PL).
  Qed.

  Definition rs_sbf_to_target (fR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction) :
      I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction :=
    I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_mk
      (fun dL => sub_nat_to_imported (fR (sub_nat_to_rocq dL))).
  Definition rs_sbf_to_source (sL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) :
      prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction :=
    ((fun dR => sub_nat_to_rocq
      (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL (sub_nat_to_imported dR)))
      : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction).

  Lemma rs_forall_sbf (PR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction -> Prop)
      (PL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction -> SProp) :
    (forall sR sL, PREDC.PredSbfClassRel sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    apply (arta_forall_cover _ _ PREDC.PredSbfClassRel rs_sbf_to_target rs_sbf_to_source).
    - intros fR nR nL Hn. unfold PREDC.PredSbfClassRel, rs_sbf_to_target. cbn.
      rewrite (arta_nat_input _ _ Hn). exact (sub_nat_rel_canonical _).
    - intros sL nR nL Hn. destruct Hn. exact (sub_nat_imported_roundtrip _).
  Qed.

  (** *** Observations *)

  Lemma rs_interference_related interR interL (Hinter : AdInterferenceRel Job interR interL) (j : Job) tR tL :
    SubNatRel tR tL ->
    AdBoolRel (@prosa.analysis.abstract.definitions.interference Job interR j tR)
      (I.Prosa_Analysis_Abstract_Definitions_Interference_interference Job dJ interL j tL).
  Proof. intro Ht. destruct Ht. exact (Hinter j tR). Qed.

  Lemma rs_unit_supply_rel :
    PropSPropRel (@prosa.model.processor.platform_properties.unit_supply_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.unit_supply_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model].
    apply rs_forall_state. intros sR sL Hs.
    exact (sub_nat_le_correspondence _ _ _ _ (SUP.supply_ps_supply_in_related Job PStateR PStateL rs_sup sR sL Hs)
      (sub_nat_rel_canonical 1)).
  Qed.

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL.

    Lemma rs_scheduled_at_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR sR j tR)
        (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL sL j tL).
    Proof.
      unfold prosa.behavior.service.scheduled_at.
      exact (SSO.svc_scheduled_in_related Job PStateR PStateL R j _ _ (Hs tR tL Ht)).
    Qed.

    Lemma rs_must_arrive_rel :
      PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PStateR sR)
        (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job dJ jaL PStateL sL).
    Proof.
      unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros tR tL Ht.
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (rs_scheduled_at_related j _ _ Ht))|].
      exact (ad_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
    Qed.

    Lemma rs_completed_dont_execute_rel :
      PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PStateR sR costR)
        (I.Prosa_Behavior_Ready_completed_jobs_dont_execute Job dJ PStateL sL costL).
    Proof.
      unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros tR tL Ht.
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (rs_scheduled_at_related j _ _ Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _
        (ad_service_related Job PStateR PStateL R sR sL Hs j tR tL Ht) (Hcost j)).
    Qed.
  End Sched.

  Lemma rs_fully_consuming_rel :
    PropSPropRel (@prosa.model.processor.platform_properties.fully_consuming_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.fully_consuming_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model].
    apply ad_forall_identity_correspondence. intro j.
    apply rs_forall_sched. intros sR sL Hs.
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (rs_scheduled_at_related sR sL Hs j _ _ Ht))|].
    exact (sub_nat_eq_correspondence _ _ _ _ (ad_service_at_related Job PStateR PStateL R sR sL Hs j tR tL Ht)
      (SUPC.supply_at_correspondence Job PStateR PStateL rs_sup sR sL (rs_hs_sup sR sL Hs) tR tL Ht)).
  Qed.

  Lemma rs_ibfp_rel (sbfR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction)
      (sbfL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) (Hsbf : PREDC.PredSbfClassRel sbfR sbfL)
      intraR intraL (Hintra : ArtaFunRel intraR intraL) :
    ArtaFunRel (fun A D => D - sbfR D + intraR A D)
      (fun A D => I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
        (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat) D
          (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sbfL D))
        (intraL A D)).
  Proof.
    intros xR xL dR dL Hx Hd.
    exact (arta_add_related _ _ _ _ (arta_sub_related _ _ _ _ Hd (Hsbf _ _ Hd)) (Hintra _ _ _ _ Hx Hd)).
  Qed.

  Lemma rs_ibfnp_rel (tsk : Task) (sbfR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction)
      (sbfL : I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) (Hsbf : PREDC.PredSbfClassRel sbfR sbfL) :
    ArtaFunRel (fun F D => F - @TPP.task_rtct Task rtcR tsk + (D - sbfR D - (F - sbfR F)))
      (fun F D => I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
        (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat) F
          (I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task dT rtcL tsk))
        (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
          (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat) D
            (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sbfL D))
          (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat) F
            (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sbfL F)))).
  Proof.
    intros FR FL DR DL HF HD.
    exact (arta_add_related _ _ _ _ (arta_sub_related _ _ _ _ HF (Hrtc tsk))
      (arta_sub_related _ _ _ _ (arta_sub_related _ _ _ _ HD (Hsbf _ _ HD))
        (arta_sub_related _ _ _ _ HF (Hsbf _ _ HF)))).
  Qed.

  (** Shared prefix of the auxiliary lemmas: from work conservation to the
      incompletion hypothesis, for fixed schedules, arrival sequence, task and
      abstract model; it leaves the conclusion, with [j], [t1R/t1L/H1],
      [t2R/t2L/H2], [dR/dL/Hd] in context. *)
  Ltac rs_aux_prefix sR sL Hs arrR arrL Harr tsk interR interL Hinter workloadR workloadL Hworkload :=
    (apply ad_imp_correspondence;
      [exact (arta_wc_rel Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr
        interR interL Hinter workloadR workloadL Hworkload)|]);
    apply ad_forall_identity_correspondence;
    let j := fresh "j" in intro j;
    (apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j Harr)|]);
    (apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|]);
    (apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (arta_cost_positive_related Job costR costL Hcost j))|]);
    apply ad_forall_nat_correspondence;
    let t1R := fresh "t1R" in let t1L := fresh "t1L" in let H1 := fresh "H1" in
    intros t1R t1L H1;
    apply ad_forall_nat_correspondence;
    let t2R := fresh "t2R" in let t2L := fresh "t2L" in let H2 := fresh "H2" in
    intros t2R t2L H2;
    (apply ad_imp_correspondence;
      [exact (ad_busy_interval_prefix_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL
        Hcost interR interL Hinter workloadR workloadL Hworkload j t1R t2R t1L t2L H1 H2)|]);
    apply ad_forall_nat_correspondence;
    let dR := fresh "dR" in let dL := fresh "dL" in let Hd := fresh "Hd" in
    intros dR dL Hd;
    (apply ad_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (arta_add_related _ _ _ _ H1 Hd) H2)|]);
    (apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (ad_completed_by_related Job PStateR PStateL R sR sL Hs costR costL Hcost j _ _
          (arta_add_related _ _ _ _ H1 Hd))))|]).

  Ltac rs_mem Hts tsk :=
    exact (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).

  Ltac rs_cover_model interR interL Hinter workloadR workloadL Hworkload :=
    apply arta_forall_inter; intros interR interL Hinter;
    apply arta_forall_iw; intros workloadR workloadL Hworkload.

  (** ** Statements with leading arrival sequence, schedule and task set *)

  Section Leading.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL.
    Variable tsR : seq Task.
    Variable tsL : I.List Task.
    Hypothesis Hts : ArListRel tsR tsL.

    (** *** blackout_impl_interference *)

    Definition src_blackout_impl_interference (tsk : Task) : Prop :=
      ltac:(body_of (fun s : S.statement_blackout_impl_interference =>
        s Task Job jtR jaR costR PStateR arrR sR tsR tsk)).
    Definition tgt_blackout_impl_interference (tsk : Task) : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_blackout_impl_interference
        Task dT Job dJ jtL jaL costL PStateL arrL sL tsL tsk)).

    Theorem blackout_impl_interference_correspondence (tsk : Task) :
      PropSPropRel (src_blackout_impl_interference tsk) (tgt_blackout_impl_interference tsk).
    Proof.
      unfold src_blackout_impl_interference, tgt_blackout_impl_interference.
      apply ad_imp_correspondence; [rs_mem Hts tsk|].
      rs_cover_model interR interL Hinter workloadR workloadL Hworkload.
      rs_aux_prefix sR sL Hs arrR arrL Harr tsk interR interL Hinter workloadR workloadL Hworkload.
      apply ad_forall_nat_correspondence. intros tR tL Ht.
      apply ad_imp_correspondence;
        [exact (ad_bool_truth_correspondence _ _ (svc_bool_and_related _ _ _ _
          (svc_decide_le_related _ _ _ _ H1 Ht) (svc_decide_lt_related _ _ _ _ Ht H2)))|].
      apply ad_imp_correspondence;
        [exact (ad_bool_truth_correspondence _ _
          (SUPC.is_blackout_correspondence Job PStateR PStateL rs_sup sR sL (rs_hs_sup sR sL Hs) tR tL Ht))|].
      exact (ad_bool_truth_correspondence _ _ (rs_interference_related interR interL Hinter j tR tL Ht)).
    Qed.

    (** *** blackout_plus_local_is_interference *)

    Definition src_blackout_plus_local_is_interference (tsk : Task) : Prop :=
      ltac:(body_of (fun s : S.statement_blackout_plus_local_is_interference =>
        s Task Job jtR jaR costR PStateR arrR sR tsR tsk)).
    Definition tgt_blackout_plus_local_is_interference (tsk : Task) : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_blackout_plus_local_is_interference
        Task dT Job dJ jtL jaL costL PStateL arrL sL tsL tsk)).

    Theorem blackout_plus_local_is_interference_correspondence (tsk : Task) :
      PropSPropRel (src_blackout_plus_local_is_interference tsk) (tgt_blackout_plus_local_is_interference tsk).
    Proof.
      unfold src_blackout_plus_local_is_interference, tgt_blackout_plus_local_is_interference.
      apply ad_imp_correspondence; [rs_mem Hts tsk|].
      rs_cover_model interR interL Hinter workloadR workloadL Hworkload.
      rs_aux_prefix sR sL Hs arrR arrL Harr tsk interR interL Hinter workloadR workloadL Hworkload.
      apply ad_forall_nat_correspondence. intros tR tL Ht.
      apply ad_imp_correspondence;
        [exact (ad_bool_truth_correspondence _ _ (svc_bool_and_related _ _ _ _
          (svc_decide_le_related _ _ _ _ H1 Ht) (svc_decide_lt_related _ _ _ _ Ht H2)))|].
      exact (sub_nat_eq_correspondence _ _ _ _
        (arta_add_related _ _ _ _
          (ad_bool_to_nat_related _ _
            (SUPC.is_blackout_correspondence Job PStateR PStateL rs_sup sR sL (rs_hs_sup sR sL Hs) tR tL Ht))
          (ad_bool_to_nat_related _ _
            (IBFS.intra_interference_correspondence Job PStateR PStateL rs_sup sR sL (rs_hs_sup sR sL Hs)
              interR interL Hinter j tR tL Ht)))
        (ad_bool_to_nat_related _ _ (rs_interference_related interR interL Hinter j tR tL Ht))).
    Qed.

    (** *** blackout_plus_local_is_interference_cumul *)

    Definition src_blackout_plus_local_is_interference_cumul (tsk : Task) : Prop :=
      ltac:(body_of (fun s : S.statement_blackout_plus_local_is_interference_cumul =>
        s Task Job jtR jaR costR PStateR arrR sR tsR tsk)).
    Definition tgt_blackout_plus_local_is_interference_cumul (tsk : Task) : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_blackout_plus_local_is_interference_cumul
        Task dT Job dJ jtL jaL costL PStateL arrL sL tsL tsk)).

    Theorem blackout_plus_local_is_interference_cumul_correspondence (tsk : Task) :
      PropSPropRel (src_blackout_plus_local_is_interference_cumul tsk)
        (tgt_blackout_plus_local_is_interference_cumul tsk).
    Proof.
      unfold src_blackout_plus_local_is_interference_cumul, tgt_blackout_plus_local_is_interference_cumul.
      apply ad_imp_correspondence; [rs_mem Hts tsk|].
      rs_cover_model interR interL Hinter workloadR workloadL Hworkload.
      rs_aux_prefix sR sL Hs arrR arrL Harr tsk interR interL Hinter workloadR workloadL Hworkload.
      have Hend := arta_add_related _ _ _ _ H1 Hd.
      exact (sub_nat_eq_correspondence _ _ _ _
        (arta_add_related _ _ _ _
          (SUPC.blackout_during_correspondence Job PStateR PStateL rs_sup sR sL (rs_hs_sup sR sL Hs)
            _ _ _ _ H1 Hend)
          (IBFS.cumul_intra_interference_correspondence Job PStateR PStateL rs_sup sR sL (rs_hs_sup sR sL Hs)
            interR interL Hinter j _ _ _ _ H1 Hend))
        (cumulative_interference_correspondence Job interR interL j _ _ _ _ Hinter H1 Hend)).
    Qed.

    (** *** IBF_P_sol_le_IBF_NP *)

    Definition src_IBF_P_sol_le_IBF_NP (tsk : Task) : Prop :=
      ltac:(body_of (fun s : S.statement_IBF_P_sol_le_IBF_NP =>
        s Task tcR rtcR Job jtR costR jpR arrR tsR tsk)).
    Definition tgt_IBF_P_sol_le_IBF_NP (tsk : Task) : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_IBF_P_sol_le_IBF_NP
        Task dT Job dJ tcL rtcL jtL costL jpL arrL tsL tsk)).

    Theorem IBF_P_sol_le_IBF_NP_correspondence (tsk : Task) :
      PropSPropRel (src_IBF_P_sol_le_IBF_NP tsk) (tgt_IBF_P_sol_le_IBF_NP tsk).
    Proof.
      unfold src_IBF_P_sol_le_IBF_NP, tgt_IBF_P_sol_le_IBF_NP.
      apply ad_imp_correspondence; [rs_mem Hts tsk|].
      apply ad_imp_correspondence;
        [exact (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rtcR rtcL Hrtc
          jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk)|].
      apply rs_forall_sbf. intros sbfR sbfL Hsbf.
      apply ad_forall_nat_correspondence. intros FR FL HF.
      apply ad_forall_nat_correspondence. intros DR DL HD.
      exact (sub_nat_le_correspondence _ _ _ _ HF
        (arta_add_related _ _ _ _ (Htc tsk) (rs_ibfnp_rel tsk sbfR sbfL Hsbf _ _ _ _ HF HD))).
    Qed.

    (** *** max_in_rs_hypothesis_impl_max_in_arta_hypothesis *)

    Definition src_max_in_rs_hypothesis_impl_max_in_arta_hypothesis (tsk : Task) : Prop :=
      ltac:(body_of (fun s : S.statement_max_in_rs_hypothesis_impl_max_in_arta_hypothesis =>
        s Task tcR rtcR Job jtR jaR costR jpR PStateR arrR sR tsR tsk)).
    Definition tgt_max_in_rs_hypothesis_impl_max_in_arta_hypothesis (tsk : Task) : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_max_in_rs_hypothesis_impl_max_in_arta_hypothesis
          Task dT Job dJ tcL rtcL jtL jaL costL jpL PStateL arrL sL tsL tsk)).

    Theorem max_in_rs_hypothesis_impl_max_in_arta_hypothesis_correspondence (tsk : Task) :
      PropSPropRel (src_max_in_rs_hypothesis_impl_max_in_arta_hypothesis tsk)
        (tgt_max_in_rs_hypothesis_impl_max_in_arta_hypothesis tsk).
    Proof.
      unfold src_max_in_rs_hypothesis_impl_max_in_arta_hypothesis,
        tgt_max_in_rs_hypothesis_impl_max_in_arta_hypothesis.
      apply ad_imp_correspondence; [rs_mem Hts tsk|].
      apply ad_imp_correspondence;
        [exact (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rtcR rtcL Hrtc
          jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk)|].
      rs_cover_model interR interL Hinter workloadR workloadL Hworkload.
      apply ad_forall_nat_correspondence. intros LR LL HL.
      apply rs_forall_sbf. intros sbfR sbfL Hsbf.
      apply ad_imp_correspondence;
        [exact (BSBF.valid_busy_sbf_correspondence Task Job PStateR PStateL rs_sup R sR sL (rs_hs_sup sR sL Hs) Hs
          arrR arrL Harr jaR jaL Hja costR costL Hcost jtR jtL Hjt interR interL Hinter workloadR workloadL
          Hworkload tsk sbfR _ Hsbf)|].
      apply ad_imp_correspondence; [exact (PREDC.pred_unit_supply_bound_function_correspondence sbfR _ Hsbf)|].
      apply arta_forall_fun. intros intraR intraL Hintra.
      apply ad_forall_nat_correspondence. intros RR RL HR.
      have HP := rs_ibfp_rel sbfR sbfL Hsbf intraR intraL Hintra.
      apply ad_imp_correspondence.
      { apply ad_forall_nat_correspondence. intros AR AL HA.
        apply ad_imp_correspondence; [exact (arta_search_space_rel _ _ _ _ _ _ HP HL HA)|].
        apply ad_exists_nat_correspondence. intros FR FL HF.
        have HAR := arta_add_related _ _ _ _ HA HR.
        apply ad_and_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ HF HAR)|].
        apply ad_and_correspondence.
        - exact (sub_nat_le_correspondence _ _ _ _
            (arta_add_related _ _ _ _ (Hrtc tsk) (Hintra _ _ _ _ HA HF)) (Hsbf _ _ HF)).
        - exact (sub_nat_le_correspondence _ _ _ _
            (arta_add_related _ _ _ _ (Hsbf _ _ HF) (arta_sub_related _ _ _ _ (Htc tsk) (Hrtc tsk)))
            (Hsbf _ _ HAR)). }
      apply ad_forall_nat_correspondence. intros AR AL HA.
      apply ad_imp_correspondence; [exact (arta_search_space_rel _ _ _ _ _ _ HP HL HA)|].
      apply ad_exists_nat_correspondence. intros FR FL HF.
      have HAR := arta_add_related _ _ _ _ HA HR.
      apply ad_and_correspondence.
      - exact (sub_nat_le_correspondence _ _ _ _
          (arta_add_related _ _ _ _ (Hrtc tsk)
            (arta_add_related _ _ _ _ (arta_sub_related _ _ _ _ HF (Hsbf _ _ HF)) (Hintra _ _ _ _ HA HF))) HF).
      - exact (sub_nat_le_correspondence _ _ _ _
          (arta_add_related _ _ _ _ (Htc tsk) (rs_ibfnp_rel tsk sbfR sbfL Hsbf _ _ _ _ HF HAR)) HAR).
    Qed.
  End Leading.

  (** ** Statements quantifying the arrival sequence and schedule inside *)

  (** *** cumulative_job_interference_bound *)

  Definition src_cumulative_job_interference_bound : Prop :=
    ltac:(body_of (fun s : S.statement_cumulative_job_interference_bound =>
      s Task Job jtR jaR costR PStateR)).
  Definition tgt_cumulative_job_interference_bound : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_cumulative_job_interference_bound
      Task dT Job dJ jtL jaL costL PStateL)).

  Theorem cumulative_job_interference_bound_correspondence :
    PropSPropRel src_cumulative_job_interference_bound tgt_cumulative_job_interference_bound.
  Proof.
    unfold src_cumulative_job_interference_bound, tgt_cumulative_job_interference_bound.
    apply ad_imp_correspondence; [exact rs_unit_supply_rel|].
    apply rs_forall_arr. intros arrR arrL Harr.
    apply rs_forall_sched. intros sR sL Hs.
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_imp_correspondence; [rs_mem Hts tsk|].
    rs_cover_model interR interL Hinter workloadR workloadL Hworkload.
    apply ad_imp_correspondence;
      [exact (arta_wc_rel Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr
        interR interL Hinter workloadR workloadL Hworkload)|].
    apply rs_forall_sbf. intros sbfR sbfL Hsbf.
    apply ad_imp_correspondence;
      [exact (BSBF.valid_busy_sbf_correspondence Task Job PStateR PStateL rs_sup R sR sL (rs_hs_sup sR sL Hs) Hs
        arrR arrL Harr jaR jaL Hja costR costL Hcost jtR jtL Hjt interR interL Hinter workloadR workloadL
        Hworkload tsk sbfR _ Hsbf)|].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j Harr)|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (arta_cost_positive_related Job costR costL Hcost j))|].
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_forall_nat_correspondence. intros t2R t2L H2.
    apply ad_imp_correspondence;
      [exact (ad_busy_interval_prefix_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL
        Hcost interR interL Hinter workloadR workloadL Hworkload j t1R t2R t1L t2L H1 H2)|].
    apply ad_forall_nat_correspondence. intros dR dL Hd.
    have Hend := arta_add_related _ _ _ _ H1 Hd.
    apply ad_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Hend H2)|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (ad_completed_by_related Job PStateR PStateL R sR sL Hs costR costL Hcost j _ _ Hend)))|].
    exact (sub_nat_le_correspondence _ _ _ _
      (cumulative_interference_correspondence Job interR interL j _ _ _ _ Hinter H1 Hend)
      (arta_add_related _ _ _ _ (arta_sub_related _ _ _ _ Hd (Hsbf _ _ Hd))
        (IBFS.cumul_intra_interference_correspondence Job PStateR PStateL rs_sup sR sL (rs_hs_sup sR sL Hs)
          interR interL Hinter j _ _ _ _ H1 Hend))).
  Qed.

  (** *** no_intra_interference_after_F *)

  Definition src_no_intra_interference_after_F : Prop :=
    ltac:(body_of (fun s : S.statement_no_intra_interference_after_F =>
      s Task tcR rtcR Job jtR jaR costR jpR PStateR)).
  Definition tgt_no_intra_interference_after_F : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_no_intra_interference_after_F
      Task dT Job dJ tcL rtcL jtL jaL costL jpL PStateL)).

  Theorem no_intra_interference_after_F_correspondence :
    PropSPropRel src_no_intra_interference_after_F tgt_no_intra_interference_after_F.
  Proof.
    unfold src_no_intra_interference_after_F, tgt_no_intra_interference_after_F.
    apply ad_imp_correspondence; [exact rs_fully_consuming_rel|].
    apply rs_forall_arr. intros arrR arrL Harr.
    apply rs_forall_sched. intros sR sL Hs.
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_imp_correspondence; [rs_mem Hts tsk|].
    apply ad_imp_correspondence;
      [exact (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL
        rs_jsvc sR sL Hs arrR arrL Harr)|].
    apply ad_imp_correspondence;
      [exact (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rtcR rtcL Hrtc
        jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk)|].
    rs_cover_model interR interL Hinter workloadR workloadL Hworkload.
    rs_aux_prefix sR sL Hs arrR arrL Harr tsk interR interL Hinter workloadR workloadL Hworkload.
    apply ad_forall_nat_correspondence. intros FR FL HF.
    apply ad_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ HF Hd)|].
    apply ad_imp_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _ (Hrtc tsk)
        (ad_service_related Job PStateR PStateL R sR sL Hs j _ _ (arta_add_related _ _ _ _ H1 HF)))|].
    exact (sub_nat_eq_correspondence _ _ _ _
      (IBFS.cumul_intra_interference_correspondence Job PStateR PStateL rs_sup sR sL (rs_hs_sup sR sL Hs)
        interR interL Hinter j _ _ _ _ (arta_add_related _ _ _ _ H1 HF) (arta_add_related _ _ _ _ H1 Hd))
      (sub_nat_rel_canonical O)).
  Qed.

  (** *** IBF_P_bounds_interference *)

  Definition src_IBF_P_bounds_interference : Prop :=
    ltac:(body_of (fun s : S.statement_IBF_P_bounds_interference =>
      s Task Job jtR jaR costR PStateR)).
  Definition tgt_IBF_P_bounds_interference : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_IBF_P_bounds_interference
      Task dT Job dJ jtL jaL costL PStateL)).

  Theorem IBF_P_bounds_interference_correspondence :
    PropSPropRel src_IBF_P_bounds_interference tgt_IBF_P_bounds_interference.
  Proof.
    unfold src_IBF_P_bounds_interference, tgt_IBF_P_bounds_interference.
    apply ad_imp_correspondence; [exact rs_unit_supply_rel|].
    apply rs_forall_arr. intros arrR arrL Harr.
    apply rs_forall_sched. intros sR sL Hs.
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_imp_correspondence; [rs_mem Hts tsk|].
    rs_cover_model interR interL Hinter workloadR workloadL Hworkload.
    apply ad_imp_correspondence;
      [exact (arta_wc_rel Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr
        interR interL Hinter workloadR workloadL Hworkload)|].
    apply rs_forall_sbf. intros sbfR sbfL Hsbf.
    apply ad_imp_correspondence;
      [exact (BSBF.valid_busy_sbf_correspondence Task Job PStateR PStateL rs_sup R sR sL (rs_hs_sup sR sL Hs) Hs
        arrR arrL Harr jaR jaL Hja costR costL Hcost jtR jtL Hjt interR interL Hinter workloadR workloadL
        Hworkload tsk sbfR _ Hsbf)|].
    apply arta_forall_fun. intros intraR intraL Hintra.
    apply ad_imp_correspondence;
      [exact (IBFS.intra_interference_is_bounded_by_correspondence Job PStateR PStateL R rs_sup sR sL Hs
        (rs_hs_sup sR sL Hs) interR interL Hinter Task jtR jtL Hjt jaR jaL Hja costR costL Hcost
        workloadR workloadL Hworkload arrR arrL Harr intraR intraL Hintra tsk)|].
    exact (arta_ibfp_bounded_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL Hcost
      sR sL Hs arrR arrL Harr interR interL Hinter workloadR workloadL Hworkload tsk _ _
      (rs_ibfp_rel sbfR sbfL Hsbf intraR intraL Hintra)).
  Qed.

  (** *** IBF_NP_bounds_interference *)

  Definition src_IBF_NP_bounds_interference : Prop :=
    ltac:(body_of (fun s : S.statement_IBF_NP_bounds_interference =>
      s Task tcR rtcR Job jtR jaR costR jpR PStateR)).
  Definition tgt_IBF_NP_bounds_interference : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_IBF_NP_bounds_interference
      Task dT Job dJ tcL rtcL jtL jaL costL jpL PStateL)).

  Theorem IBF_NP_bounds_interference_correspondence :
    PropSPropRel src_IBF_NP_bounds_interference tgt_IBF_NP_bounds_interference.
  Proof.
    unfold src_IBF_NP_bounds_interference, tgt_IBF_NP_bounds_interference.
    apply ad_imp_correspondence; [exact rs_unit_supply_rel|].
    apply ad_imp_correspondence; [exact rs_fully_consuming_rel|].
    apply rs_forall_arr. intros arrR arrL Harr.
    apply rs_forall_sched. intros sR sL Hs.
    apply ad_imp_correspondence; [exact (rs_must_arrive_rel sR sL Hs)|].
    apply ad_imp_correspondence; [exact (rs_completed_dont_execute_rel sR sL Hs)|].
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_imp_correspondence; [rs_mem Hts tsk|].
    apply ad_imp_correspondence;
      [exact (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL
        rs_jsvc sR sL Hs arrR arrL Harr)|].
    apply ad_imp_correspondence;
      [exact (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rtcR rtcL Hrtc
        jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk)|].
    rs_cover_model interR interL Hinter workloadR workloadL Hworkload.
    apply ad_imp_correspondence;
      [exact (arta_wc_rel Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr
        interR interL Hinter workloadR workloadL Hworkload)|].
    apply rs_forall_sbf. intros sbfR sbfL Hsbf.
    apply ad_imp_correspondence;
      [exact (BSBF.valid_busy_sbf_correspondence Task Job PStateR PStateL rs_sup R sR sL (rs_hs_sup sR sL Hs) Hs
        arrR arrL Harr jaR jaL Hja costR costL Hcost jtR jtL Hjt interR interL Hinter workloadR workloadL
        Hworkload tsk sbfR _ Hsbf)|].
    apply ad_imp_correspondence; [exact (PREDC.pred_unit_supply_bound_function_correspondence sbfR _ Hsbf)|].
    apply arta_forall_fun. intros intraR intraL Hintra.
    apply ad_imp_correspondence;
      [exact (IBFS.intra_interference_is_bounded_by_correspondence Job PStateR PStateL R rs_sup sR sL Hs
        (rs_hs_sup sR sL Hs) interR interL Hinter Task jtR jtL Hjt jaR jaL Hja costR costL Hcost
        workloadR workloadL Hworkload arrR arrL Harr intraR intraL Hintra tsk)|].
    exact (arta_ibfnp_bounded_rel Task Job PStateR PStateL R rtcR rtcL Hrtc jtR jtL Hjt jaR jaL Hja
      costR costL Hcost sR sL Hs arrR arrL Harr interR interL Hinter workloadR workloadL Hworkload tsk _ _
      (rs_ibfp_rel sbfR sbfL Hsbf intraR intraL Hintra) _ _ (rs_ibfnp_rel tsk sbfR sbfL Hsbf)).
  Qed.

  (** *** uniprocessor_response_time_bound_restricted_supply *)

  Definition src_uniprocessor_response_time_bound_restricted_supply : Prop :=
    ltac:(body_of (fun s : S.statement_uniprocessor_response_time_bound_restricted_supply =>
      s Task tcR rtcR Job jtR jaR costR jpR PStateR)).
  Definition tgt_uniprocessor_response_time_bound_restricted_supply : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_uniprocessor_response_time_bound_restricted_supply
        Task dT Job dJ tcL rtcL jtL jaL costL jpL PStateL)).

  Theorem uniprocessor_response_time_bound_restricted_supply_correspondence :
    PropSPropRel src_uniprocessor_response_time_bound_restricted_supply
      tgt_uniprocessor_response_time_bound_restricted_supply.
  Proof.
    unfold src_uniprocessor_response_time_bound_restricted_supply,
      tgt_uniprocessor_response_time_bound_restricted_supply.
    apply ad_imp_correspondence; [exact rs_unit_supply_rel|].
    apply ad_imp_correspondence; [exact rs_fully_consuming_rel|].
    apply rs_forall_arr. intros arrR arrL Harr.
    apply rs_forall_sched. intros sR sL Hs.
    apply ad_imp_correspondence; [exact (rs_must_arrive_rel sR sL Hs)|].
    apply ad_imp_correspondence; [exact (rs_completed_dont_execute_rel sR sL Hs)|].
    apply ad_imp_correspondence;
      [exact (arta_valid_job_costs_rel Task Job tcR tcL Htc jtR jtL Hjt costR costL Hcost arrR arrL Harr)|].
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_imp_correspondence; [rs_mem Hts tsk|].
    apply ad_imp_correspondence;
      [exact (PPC.valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL
        rs_jsvc sR sL Hs arrR arrL Harr)|].
    apply ad_imp_correspondence;
      [exact (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rtcR rtcL Hrtc
        jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk)|].
    rs_cover_model interR interL Hinter workloadR workloadL Hworkload.
    apply ad_imp_correspondence;
      [exact (arta_wc_rel Job PStateR PStateL R jaR jaL Hja costR costL Hcost sR sL Hs arrR arrL Harr
        interR interL Hinter workloadR workloadL Hworkload)|].
    apply ad_forall_nat_correspondence. intros LR LL HL.
    apply ad_imp_correspondence;
      [exact (arta_bounded_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL Hcost
        sR sL Hs arrR arrL Harr interR interL Hinter workloadR workloadL Hworkload tsk LR LL HL)|].
    apply rs_forall_sbf. intros sbfR sbfL Hsbf.
    apply ad_imp_correspondence;
      [exact (BSBF.valid_busy_sbf_correspondence Task Job PStateR PStateL rs_sup R sR sL (rs_hs_sup sR sL Hs) Hs
        arrR arrL Harr jaR jaL Hja costR costL Hcost jtR jtL Hjt interR interL Hinter workloadR workloadL
        Hworkload tsk sbfR _ Hsbf)|].
    apply ad_imp_correspondence; [exact (PREDC.pred_unit_supply_bound_function_correspondence sbfR _ Hsbf)|].
    apply arta_forall_fun. intros intraR intraL Hintra.
    apply ad_imp_correspondence;
      [exact (IBFS.intra_interference_is_bounded_by_correspondence Job PStateR PStateL R rs_sup sR sL Hs
        (rs_hs_sup sR sL Hs) interR interL Hinter Task jtR jtL Hjt jaR jaL Hja costR costL Hcost
        workloadR workloadL Hworkload arrR arrL Harr intraR intraL Hintra tsk)|].
    apply ad_forall_nat_correspondence. intros RR RL HR.
    have HP := rs_ibfp_rel sbfR sbfL Hsbf intraR intraL Hintra.
    apply ad_imp_correspondence.
    - apply ad_forall_nat_correspondence. intros AR AL HA.
      apply ad_imp_correspondence; [exact (arta_search_space_rel _ _ _ _ _ _ HP HL HA)|].
      apply ad_exists_nat_correspondence. intros FR FL HF.
      have HAR := arta_add_related _ _ _ _ HA HR.
      apply ad_and_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ HF HAR)|].
      apply ad_and_correspondence.
      + exact (sub_nat_le_correspondence _ _ _ _
          (arta_add_related _ _ _ _ (Hrtc tsk) (Hintra _ _ _ _ HA HF)) (Hsbf _ _ HF)).
      + exact (sub_nat_le_correspondence _ _ _ _
          (arta_add_related _ _ _ _ (Hsbf _ _ HF) (arta_sub_related _ _ _ _ (Htc tsk) (Hrtc tsk)))
          (Hsbf _ _ HAR)).
    - exact (arta_response_time_bound_rel Task Job PStateR PStateL R jtR jtL Hjt jaR jaL Hja costR costL
        Hcost sR sL Hs arrR arrL Harr tsk RR RL HR).
  Qed.
End RsAbstractRta.
