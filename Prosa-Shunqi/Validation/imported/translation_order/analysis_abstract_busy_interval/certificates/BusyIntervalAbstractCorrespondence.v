From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import BusyIntervalAbstractSemanticSource.
From prosa Require Import analysis.abstract.definitions model.aggregate.workload model.job.properties
  model.processor.platform_properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBusyIntervalAbstract ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  WorkloadCorrespondence
  AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations
  AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations
  AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums
  AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations
  AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations
  AbstractDefinitionsBusyIntervalHelpers.

Module I := ImportedBusyIntervalAbstract.
Module S := BusyIntervalAbstractSemanticSource.BusyIntervalAbstractSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.

(** Statement correspondences for [analysis/abstract/busy_interval.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.
    Inputs: processor states by the accepted two-sided [SvcProcessorStateRel]
    of the abstract-definitions family and schedules through it;
    [job_arrival] and [job_cost] pointwise by [SubNatRel]; [JobTask] by the
    accepted [AdJobTaskRel]; arrival sequences by the accepted
    [ArArrivalSequenceRel] (the abstract family's [AdArrivalSequenceRel] is
    the same relation, obtained by conversion); [Interference] and
    [InterferingWorkload] by the accepted abstract relations; jobs and tasks
    identity, instants and durations by [SubNatRel].  Inputs quantified
    inside a statement (instances, arrival sequences, schedules, processor
    states, tasks, jobs, instants) are covered in both directions by explicit
    conversions.  The abstract busy-interval notions are related by the
    accepted abstract-definitions certificates, the workload by the accepted
    workload certificate, the arrival-sequence properties by the accepted
    arrival certificates.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators *)

Lemma bia_forall_cover (A B : Type) (Rel : A -> B -> SProp)
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

Lemma ad_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intros [].
  - intro H. apply strictly_inhabits. exact (interpret_strict _ (ar_target_false_to_strict H)).
Qed.

Lemma bia_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p | q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intros [p | q]; apply strictly_inhabits.
    + left. exact (sprop_to_prop _ _ HP p).
    + right. exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma bia_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma bia_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma bia_succ_related (tR : nat) (tL : Lean.Nat) :
  SubNatRel tR tL ->
  SubNatRel tR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) tL
    (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Ht.
  have E : Logic.eq (tR + 1) tR.+1 := addn1 tR.
  destruct E. exact (sub_add_correspondence _ _ _ _ Ht (sub_nat_rel_canonical 1)).
Qed.

Lemma bia_add_related (aR : nat) (aL : Lean.Nat) (bR : nat) (bL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Section BusyInterval.
  Context (Task Job : eqType).
  Let dT := ad_decidable_eq Task.
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SSO.SvcProcessorStateRel Job PStateR PStateL.
  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.

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

  Definition bia_sched_to_target (sR : SchedR) : SchedL :=
    fun tL => SSO.svc_ps_state_to_target Job PStateR PStateL R (sR (sub_nat_to_rocq tL)).
  Definition bia_sched_to_source (sL : SchedL) : SchedR :=
    fun tR => SSO.svc_ps_state_to_source Job PStateR PStateL R (sL (sub_nat_to_imported tR)).

  Lemma bia_sched_to_target_rel sR : SSO.SvcScheduleRel Job PStateR PStateL R sR (bia_sched_to_target sR).
  Proof.
    intros tR tL Ht. unfold bia_sched_to_target. rewrite (bia_nat_input _ _ Ht).
    exact (SSO.svc_ps_state_rel_canonical Job PStateR PStateL R _).
  Qed.

  Lemma bia_sched_to_source_rel sL : SSO.SvcScheduleRel Job PStateR PStateL R (bia_sched_to_source sL) sL.
  Proof.
    intros tR tL Ht. destruct Ht.
    exact (SSO.svc_ps_state_rel_surjective Job PStateR PStateL R _).
  Qed.

  Lemma bia_forall_sched (PR : SchedR -> Prop) (PL : SchedL -> SProp) :
    (forall sR sL, SSO.SvcScheduleRel Job PStateR PStateL R sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    exact (bia_forall_cover _ _ (SSO.SvcScheduleRel Job PStateR PStateL R) bia_sched_to_target
      bia_sched_to_source bia_sched_to_target_rel bia_sched_to_source_rel PR PL).
  Qed.

  Definition bia_arr_to_source (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ) :
      prosa.behavior.arrival_sequence.arrival_sequence Job :=
    fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

  Lemma bia_arr_to_source_rel arrL : ArArrivalSequenceRel Job (bia_arr_to_source arrL) arrL.
  Proof.
    intros tR tL Ht. unfold ArListRel, bia_arr_to_source.
    refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
    exact (sub_imported_eq_congr arrL _ _ Ht).
  Qed.

  Lemma bia_forall_arr (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
      (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ -> SProp) :
    (forall aR aL, ArArrivalSequenceRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) ->
    PropSPropRel (forall a, PR a) (forall a, PL a).
  Proof.
    exact (bia_forall_cover _ _ (ArArrivalSequenceRel Job) (ar_arrival_sequence_to_imported Job)
      bia_arr_to_source (ar_arrival_sequence_canonical Job) bia_arr_to_source_rel PR PL).
  Qed.

  Definition bia_inter_to_target (iR : prosa.analysis.abstract.definitions.Interference Job) :
      I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ :=
    I.Prosa_Analysis_Abstract_Definitions_Interference_mk Job dJ
      (fun j tL => ad_bool_to_imported (@prosa.analysis.abstract.definitions.interference Job iR j
        (sub_nat_to_rocq tL))).
  Definition bia_inter_to_source (iL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ) :
      prosa.analysis.abstract.definitions.Interference Job :=
    ((fun j tR => ad_bool_to_rocq
      (I.Prosa_Analysis_Abstract_Definitions_Interference_interference Job dJ iL j (sub_nat_to_imported tR)))
      : prosa.analysis.abstract.definitions.Interference Job).

  Lemma bia_forall_inter (PR : prosa.analysis.abstract.definitions.Interference Job -> Prop)
      (PL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ -> SProp) :
    (forall iR iL, AdInterferenceRel Job iR iL -> PropSPropRel (PR iR) (PL iL)) ->
    PropSPropRel (forall i, PR i) (forall i, PL i).
  Proof.
    apply (bia_forall_cover _ _ (AdInterferenceRel Job) bia_inter_to_target bia_inter_to_source).
    - intros iR j t. unfold AdBoolRel. cbn. rewrite sub_nat_rocq_roundtrip. exact (@Lean.eq_refl _ _).
    - intros iL j t. exact (ad_bool_target_roundtrip _).
  Qed.

  Definition bia_iw_to_target (wR : prosa.analysis.abstract.definitions.InterferingWorkload Job) :
      I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ :=
    I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload_mk Job dJ
      (fun j tL => sub_nat_to_imported (@prosa.analysis.abstract.definitions.interfering_workload Job wR j
        (sub_nat_to_rocq tL))).
  Definition bia_iw_to_source (wL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ) :
      prosa.analysis.abstract.definitions.InterferingWorkload Job :=
    ((fun j tR => sub_nat_to_rocq
      (I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload_interfering_workload Job dJ wL j
        (sub_nat_to_imported tR)))
      : prosa.analysis.abstract.definitions.InterferingWorkload Job).

  Lemma bia_forall_iw (PR : prosa.analysis.abstract.definitions.InterferingWorkload Job -> Prop)
      (PL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ -> SProp) :
    (forall wR wL, AdInterferingWorkloadRel Job wR wL -> PropSPropRel (PR wR) (PL wL)) ->
    PropSPropRel (forall w, PR w) (forall w, PL w).
  Proof.
    apply (bia_forall_cover _ _ (AdInterferingWorkloadRel Job) bia_iw_to_target bia_iw_to_source).
    - intros wR j t. unfold SubNatRel. cbn. rewrite sub_nat_rocq_roundtrip. exact (@Lean.eq_refl _ _).
    - intros wL j t. exact (sub_nat_imported_roundtrip _).
  Qed.

  (** *** Observations on related schedules *)

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL.

    Lemma bia_scheduled_at_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR sR j tR)
        (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL sL j tL).
    Proof.
      unfold prosa.behavior.service.scheduled_at.
      exact (SSO.svc_scheduled_in_related Job PStateR PStateL R j _ _ (Hs tR tL Ht)).
    Qed.

    Lemma bia_pending_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
      SvcBoolRel (@prosa.behavior.service.pending Job PStateR sR costR jaR j tR)
        (I.Prosa_Behavior_Service_pending Job dJ PStateL sL costL jaL j tL).
    Proof.
      unfold prosa.behavior.service.pending.
      exact (svc_bool_and_related _ _ _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)
        (svc_bool_not_related _ _ (ad_completed_by_related Job PStateR PStateL R sR sL Hs costR costL Hcost j tR tL Ht))).
    Qed.

    Lemma bia_must_arrive_rel :
      PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PStateR sR)
        (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job dJ jaL PStateL sL).
    Proof.
      unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros tR tL Ht.
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (bia_scheduled_at_related j _ _ Ht))|].
      exact (ad_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
    Qed.

    Lemma bia_completed_dont_execute_rel :
      PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PStateR sR costR)
        (I.Prosa_Behavior_Ready_completed_jobs_dont_execute Job dJ PStateL sL costL).
    Proof.
      unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros tR tL Ht.
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (bia_scheduled_at_related j _ _ Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _
        (ad_service_related Job PStateR PStateL R sR sL Hs j tR tL Ht) (Hcost j)).
    Qed.
  End Sched.

  Lemma bia_cost_positive_related (j : Job) :
    SvcBoolRel (@prosa.model.job.properties.job_cost_positive Job costR j)
      (I.Prosa_Model_Job_Properties_job_cost_positive Job dJ costL j).
  Proof.
    unfold prosa.model.job.properties.job_cost_positive.
    exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost j)).
  Qed.

  Lemma bia_unit_service_rel :
    PropSPropRel (@prosa.model.processor.platform_properties.unit_service_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.unit_service_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model].
    apply ad_forall_identity_correspondence. intro j.
    apply (bia_forall_cover _ _ (SSO.svc_ps_state_rel Job PStateR PStateL R)
      (SSO.svc_ps_state_to_target Job PStateR PStateL R) (SSO.svc_ps_state_to_source Job PStateR PStateL R)
      (SSO.svc_ps_state_rel_canonical Job PStateR PStateL R) (SSO.svc_ps_state_rel_surjective Job PStateR PStateL R)).
    intros sR sL Hs.
    exact (sub_nat_le_correspondence _ _ _ _ (SSO.svc_service_in_related Job PStateR PStateL R j _ _ Hs)
      (sub_nat_rel_canonical 1)).
  Qed.

  (** *** Statements over a fixed abstract model *)

  Section Model.
    Variable interR : prosa.analysis.abstract.definitions.Interference Job.
    Variable interL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ.
    Hypothesis Hinter : AdInterferenceRel Job interR interL.
    Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
    Variable workloadL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ.
    Hypothesis Hworkload : AdInterferingWorkloadRel Job workloadR workloadL.

    Section SchedModel.
      Variable sR : SchedR.
      Variable sL : SchedL.
      Hypothesis Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL.

      Let BIP j t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :=
        ad_busy_interval_prefix_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
          interR interL Hinter workloadR workloadL Hworkload j t1R t2R t1L t2L H1 H2.
      Let BI j t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :=
        ad_busy_interval_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
          interR interL Hinter workloadR workloadL Hworkload j t1R t2R t1L t2L H1 H2.
      Let QT j tR tL (Ht : SubNatRel tR tL) :=
        ad_quiet_time_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
          interR interL Hinter workloadR workloadL Hworkload j tR tL Ht.

      Lemma bia_bip_rel j t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
        PropSPropRel (@prosa.analysis.abstract.definitions.busy_interval_prefix Job jaR costR PStateR sR
            interR workloadR j t1R t2R)
          (I.Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job dJ interL workloadL jaL costL
            PStateL sL j t1L t2L).
      Proof. exact (BIP j _ _ _ _ H1 H2). Qed.

      Lemma bia_bi_rel j t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
        PropSPropRel (@prosa.analysis.abstract.definitions.busy_interval Job jaR costR PStateR sR
            interR workloadR j t1R t2R)
          (I.Prosa_Analysis_Abstract_Definitions_busy_interval Job dJ interL workloadL jaL costL
            PStateL sL j t1L t2L).
      Proof. exact (BI j _ _ _ _ H1 H2). Qed.

      Lemma bia_not_quiet_rel j tR tL (Ht : SubNatRel tR tL) :
        PropSPropRel (~ @prosa.analysis.abstract.definitions.quiet_time Job jaR costR PStateR sR
            interR workloadR j tR)
          (I.Not (Lean.eq (I.Prosa_Analysis_Abstract_Definitions_quiet_time Job dJ interL workloadL jaL costL
            PStateL sL j tL) I.Bool_true)).
      Proof. exact (ad_not_correspondence _ _ (ad_bool_truth_correspondence _ _ (QT j _ _ Ht))). Qed.

      Lemma bia_open_closed_related t1R t1L tR tL dR dL (H1 : SubNatRel t1R t1L) (Ht : SubNatRel tR tL)
          (Hd : SubNatRel dR dL) :
        PropSPropRel (is_true (ltn t1R tR && leq tR (addn t1R dR)))
          (Lean.eq (I.Bool_and (svc_target_decide_lt t1L tL)
            (svc_target_decide_le tL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
              (I.instHAdd_inst1 Lean.Nat I.instAddNat) t1L dL))) I.Bool_true).
      Proof.
        exact (ad_bool_truth_correspondence _ _ (svc_bool_and_related _ _ _ _
          (svc_decide_lt_related _ _ _ _ H1 Ht) (svc_decide_le_related _ _ _ _ Ht (bia_add_related _ _ _ _ H1 Hd)))).
      Qed.
    End SchedModel.
  End Model.

  (** ** Statement correspondences *)


  Section Stmts.
    Variable interR : prosa.analysis.abstract.definitions.Interference Job.
    Variable interL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ.
    Hypothesis Hinter : AdInterferenceRel Job interR interL.
    Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
    Variable workloadL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ.
    Hypothesis Hworkload : AdInterferingWorkloadRel Job workloadR workloadL.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL.

    Let BIP := bia_bip_rel interR interL Hinter workloadR workloadL Hworkload sR sL Hs.
    Let BI := bia_bi_rel interR interL Hinter workloadR workloadL Hworkload sR sL Hs.

    (** *** busy_interval_prefix_case *)

    Definition src_busy_interval_prefix_case : Prop :=
      ltac:(body_of (fun s : S.statement_busy_interval_prefix_case =>
        s Job jaR costR PStateR interR workloadR sR)).
    Definition tgt_busy_interval_prefix_case : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_busy_interval_prefix_case
        Job dJ jaL costL PStateL interL workloadL sL)).

    Theorem busy_interval_prefix_case_correspondence :
      PropSPropRel src_busy_interval_prefix_case tgt_busy_interval_prefix_case.
    Proof.
      unfold src_busy_interval_prefix_case, tgt_busy_interval_prefix_case.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      exact (bia_or_correspondence _ _ _ _ (BIP j _ _ _ _ H1 H2)
        (ad_not_correspondence _ _ (BIP j _ _ _ _ H1 H2))).
    Qed.

    (** *** terminating_busy_prefix_is_busy_interval *)

    Definition src_terminating_busy_prefix_is_busy_interval : Prop :=
      ltac:(body_of (fun s : S.statement_terminating_busy_prefix_is_busy_interval =>
        s Job jaR costR PStateR interR workloadR sR)).
    Definition tgt_terminating_busy_prefix_is_busy_interval : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_terminating_busy_prefix_is_busy_interval
        Job dJ jaL costL PStateL interL workloadL sL)).

    Theorem terminating_busy_prefix_is_busy_interval_correspondence :
      PropSPropRel src_terminating_busy_prefix_is_busy_interval tgt_terminating_busy_prefix_is_busy_interval.
    Proof.
      unfold src_terminating_busy_prefix_is_busy_interval, tgt_terminating_busy_prefix_is_busy_interval.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (bia_cost_positive_related j))|].
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_forall_nat_correspondence. intros t2'R t2'L H2'.
      apply ad_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H2 H2')|].
      apply ad_imp_correspondence; [exact (BIP j _ _ _ _ H1 H2)|].
      apply ad_imp_correspondence; [exact (ad_not_correspondence _ _ (BIP j _ _ _ _ H1 H2'))|].
      apply ad_exists_nat_correspondence. intros tR tL Ht.
      exact (BI j _ _ _ _ H1 Ht).
    Qed.

    (** *** job_completes_within_busy_interval *)

    Definition src_job_completes_within_busy_interval : Prop :=
      ltac:(body_of (fun s : S.statement_job_completes_within_busy_interval =>
        s Job jaR costR PStateR interR workloadR sR)).
    Definition tgt_job_completes_within_busy_interval : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_job_completes_within_busy_interval
        Job dJ jaL costL PStateL interL workloadL sL)).

    Theorem job_completes_within_busy_interval_correspondence :
      PropSPropRel src_job_completes_within_busy_interval tgt_job_completes_within_busy_interval.
    Proof.
      unfold src_job_completes_within_busy_interval, tgt_job_completes_within_busy_interval.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BI j _ _ _ _ H1 H2)|].
      exact (ad_bool_truth_correspondence _ _
        (ad_completed_by_related Job PStateR PStateL R sR sL Hs costR costL Hcost j _ _ H2)).
    Qed.

    (** *** no_service_before_busy_interval *)

    Definition src_no_service_before_busy_interval : Prop :=
      ltac:(body_of (fun s : S.statement_no_service_before_busy_interval =>
        s Job jaR costR PStateR interR workloadR sR)).
    Definition tgt_no_service_before_busy_interval : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_no_service_before_busy_interval
        Job dJ jaL costL PStateL interL workloadL sL)).

    Theorem no_service_before_busy_interval_correspondence :
      PropSPropRel src_no_service_before_busy_interval tgt_no_service_before_busy_interval.
    Proof.
      unfold src_no_service_before_busy_interval, tgt_no_service_before_busy_interval.
      apply ad_imp_correspondence; [exact (bia_must_arrive_rel _ _ Hs)|].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (bia_cost_positive_related j))|].
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BI j _ _ _ _ H1 H2)|].
      apply ad_forall_nat_correspondence. intros tR tL Ht.
      exact (sub_nat_eq_correspondence _ _ _ _
        (ad_service_related Job PStateR PStateL R sR sL Hs j _ _ Ht)
        (ad_service_during_related Job PStateR PStateL R sR sL Hs j _ _ _ _ H1 Ht)).
    Qed.

    (** *** service_within_busy_interval_ge_job_cost *)

    Definition src_service_within_busy_interval_ge_job_cost : Prop :=
      ltac:(body_of (fun s : S.statement_service_within_busy_interval_ge_job_cost =>
        s Job jaR costR PStateR interR workloadR sR)).
    Definition tgt_service_within_busy_interval_ge_job_cost : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_service_within_busy_interval_ge_job_cost
        Job dJ jaL costL PStateL interL workloadL sL)).

    Theorem service_within_busy_interval_ge_job_cost_correspondence :
      PropSPropRel src_service_within_busy_interval_ge_job_cost tgt_service_within_busy_interval_ge_job_cost.
    Proof.
      unfold src_service_within_busy_interval_ge_job_cost, tgt_service_within_busy_interval_ge_job_cost.
      apply ad_imp_correspondence; [exact (bia_must_arrive_rel _ _ Hs)|].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (bia_cost_positive_related j))|].
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BI j _ _ _ _ H1 H2)|].
      exact (sub_nat_le_correspondence _ _ _ _ (Hcost j)
        (ad_service_during_related Job PStateR PStateL R sR sL Hs j _ _ _ _ H1 H2)).
    Qed.

    (** *** abstract_busy_interval_prefix_job_arrival / abstract_busy_interval_job_arrival *)

    Definition src_abstract_busy_interval_prefix_job_arrival : Prop :=
      ltac:(body_of (fun s : S.statement_abstract_busy_interval_prefix_job_arrival =>
        s Job jaR costR PStateR interR workloadR sR)).
    Definition tgt_abstract_busy_interval_prefix_job_arrival : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_abstract_busy_interval_prefix_job_arrival
        Job dJ jaL costL PStateL interL workloadL sL)).

    Theorem abstract_busy_interval_prefix_job_arrival_correspondence :
      PropSPropRel src_abstract_busy_interval_prefix_job_arrival tgt_abstract_busy_interval_prefix_job_arrival.
    Proof.
      unfold src_abstract_busy_interval_prefix_job_arrival, tgt_abstract_busy_interval_prefix_job_arrival.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BIP j _ _ _ _ H1 H2)|].
      exact (sub_nat_le_correspondence _ _ _ _ H1 (Hja j)).
    Qed.

    Definition src_abstract_busy_interval_job_arrival : Prop :=
      ltac:(body_of (fun s : S.statement_abstract_busy_interval_job_arrival =>
        s Job jaR costR PStateR interR workloadR sR)).
    Definition tgt_abstract_busy_interval_job_arrival : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_abstract_busy_interval_job_arrival
        Job dJ jaL costL PStateL interL workloadL sL)).

    Theorem abstract_busy_interval_job_arrival_correspondence :
      PropSPropRel src_abstract_busy_interval_job_arrival tgt_abstract_busy_interval_job_arrival.
    Proof.
      unfold src_abstract_busy_interval_job_arrival, tgt_abstract_busy_interval_job_arrival.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BI j _ _ _ _ H1 H2)|].
      exact (sub_nat_le_correspondence _ _ _ _ H1 (Hja j)).
    Qed.

    (** *** exists_busy_interval_prefix *)

    Definition src_exists_busy_interval_prefix : Prop :=
      ltac:(body_of (fun s : S.statement_exists_busy_interval_prefix =>
        s Job jaR costR PStateR interR workloadR sR)).
    Definition tgt_exists_busy_interval_prefix : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_exists_busy_interval_prefix
        Job dJ jaL costL PStateL interL workloadL sL)).

    Theorem exists_busy_interval_prefix_correspondence :
      PropSPropRel src_exists_busy_interval_prefix tgt_exists_busy_interval_prefix.
    Proof.
      unfold src_exists_busy_interval_prefix, tgt_exists_busy_interval_prefix.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros tbR tbL Htb.
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (bia_pending_related _ _ Hs j _ _ Htb))|].
      apply ad_exists_nat_correspondence. intros t1R t1L H1.
      apply ad_and_correspondence; [exact (BIP j _ _ _ _ H1 (bia_succ_related _ _ Htb))|].
      exact (ad_bool_truth_correspondence _ _ (svc_bool_and_related _ _ _ _
        (svc_decide_le_related _ _ _ _ H1 (Hja j)) (svc_decide_le_related _ _ _ _ (Hja j) Htb))).
    Qed.

    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Lemma bia_arr_ad : AdArrivalSequenceRel Job arrR arrL.
    Proof. exact Harr. Qed.

    (** *** abstract_busy_interval_arrivals_before *)

    Definition src_abstract_busy_interval_arrivals_before : Prop :=
      ltac:(body_of (fun s : S.statement_abstract_busy_interval_arrivals_before =>
        s Job jaR costR PStateR interR workloadR arrR sR)).
    Definition tgt_abstract_busy_interval_arrivals_before : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_abstract_busy_interval_arrivals_before
        Job dJ jaL costL PStateL interL workloadL arrL sL)).

    Theorem abstract_busy_interval_arrivals_before_correspondence :
      PropSPropRel src_abstract_busy_interval_arrivals_before tgt_abstract_busy_interval_arrivals_before.
    Proof.
      unfold src_abstract_busy_interval_arrivals_before, tgt_abstract_busy_interval_arrivals_before.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j bia_arr_ad)|].
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BI j _ _ _ _ H1 H2)|].
      apply ad_imp_correspondence;
        [exact (consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
      exact (ar_bool_truth_correspondence _ _
        (ar_decide_mem_related Job j _ _ (arrivals_before_correspondence_certificate Job arrR arrL Harr _ _ H2))).
    Qed.

    (** *** service_and_interference_bound *)

    Definition src_service_and_interference_bound : Prop :=
      ltac:(body_of (fun s : S.statement_service_and_interference_bound =>
        s Job jaR costR PStateR interR workloadR arrR sR)).
    Definition tgt_service_and_interference_bound : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_service_and_interference_bound
        Job dJ jaL costL PStateL interL workloadL arrL sL)).

    Theorem service_and_interference_bound_correspondence :
      PropSPropRel src_service_and_interference_bound tgt_service_and_interference_bound.
    Proof.
      unfold src_service_and_interference_bound, tgt_service_and_interference_bound.
      apply ad_imp_correspondence;
        [exact (ad_work_conserving_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
          interR interL Hinter workloadR workloadL Hworkload arrR arrL bia_arr_ad)|].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j bia_arr_ad)|].
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (bia_cost_positive_related j))|].
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BI j _ _ _ _ H1 H2)|].
      apply ad_imp_correspondence; [exact bia_unit_service_rel|].
      apply ad_forall_nat_correspondence. intros dR dL Hd.
      have Hend := bia_add_related _ _ _ _ H1 Hd.
      apply ad_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hend H2)|].
      exact (sub_nat_le_correspondence _ _ _ _
        (bia_add_related _ _ _ _ (ad_service_during_related Job PStateR PStateL R sR sL Hs j _ _ _ _ H1 Hend)
          (cumulative_interference_correspondence Job interR interL j _ _ _ _ Hinter H1 Hend)) Hd).
    Qed.

    (** *** busy_interval_has_uninterrupted_service *)

    Definition src_busy_interval_has_uninterrupted_service (tsk : Task) : Prop :=
      ltac:(body_of (fun s : S.statement_busy_interval_has_uninterrupted_service =>
        s Task Job jtR jaR costR PStateR interR workloadR arrR tsk sR)).
    Definition tgt_busy_interval_has_uninterrupted_service (tsk : Task) : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_busy_interval_has_uninterrupted_service
        Task dT Job dJ jtL jaL costL PStateL interL workloadL arrL tsk sL)).

    Lemma bia_no_quiet_rel j t1R t1L dR dL (H1 : SubNatRel t1R t1L) (Hd : SubNatRel dR dL) :
      PropSPropRel
        (forall t : nat, is_true (ltn t1R t && leq t (addn t1R dR)) ->
          ~ @prosa.analysis.abstract.definitions.quiet_time Job jaR costR PStateR sR interR workloadR j t)
        (forall t : Lean.Nat, Lean.eq (I.Bool_and (svc_target_decide_lt t1L t)
            (svc_target_decide_le t (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
              (I.instHAdd_inst1 Lean.Nat I.instAddNat) t1L dL))) I.Bool_true ->
          I.Not (Lean.eq (I.Prosa_Analysis_Abstract_Definitions_quiet_time Job dJ interL workloadL jaL costL
            PStateL sL j t) I.Bool_true)).
    Proof.
      apply ad_forall_nat_correspondence. intros tR tL Ht.
      apply ad_imp_correspondence;
        [exact (bia_open_closed_related _ _ _ _ _ _ H1 Ht Hd)|].
      exact (bia_not_quiet_rel interR interL Hinter workloadR workloadL Hworkload sR sL Hs j _ _ Ht).
    Qed.

    Theorem busy_interval_has_uninterrupted_service_correspondence (tsk : Task) :
      PropSPropRel (src_busy_interval_has_uninterrupted_service tsk)
        (tgt_busy_interval_has_uninterrupted_service tsk).
    Proof.
      unfold src_busy_interval_has_uninterrupted_service, tgt_busy_interval_has_uninterrupted_service.
      apply ad_imp_correspondence;
        [exact (ad_work_conserving_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
          interR interL Hinter workloadR workloadL Hworkload arrR arrL bia_arr_ad)|].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j bia_arr_ad)|].
      apply ad_imp_correspondence;
        [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (bia_cost_positive_related j))|].
      apply ad_forall_nat_correspondence. intros tbR tbL Htb.
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_imp_correspondence; [exact (BIP j _ _ _ _ H1 (bia_succ_related _ _ Htb))|].
      apply ad_forall_nat_correspondence. intros dR dL Hd.
      have Hend := bia_add_related _ _ _ _ H1 Hd.
      apply ad_imp_correspondence; [exact (bia_no_quiet_rel j _ _ _ _ H1 Hd)|].
      exact (sub_nat_le_correspondence _ _ _ _ Hd
        (bia_add_related _ _ _ _ (ad_service_during_related Job PStateR PStateL R sR sL Hs j _ _ _ _ H1 Hend)
          (cumulative_interference_correspondence Job interR interL j _ _ _ _ Hinter H1 Hend))).
    Qed.

  End Stmts.

  Section TooMuch.
    Variable interR : prosa.analysis.abstract.definitions.Interference Job.
    Variable interL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ.
    Hypothesis Hinter : AdInterferenceRel Job interR interL.
    Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
    Variable workloadL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ.
    Hypothesis Hworkload : AdInterferingWorkloadRel Job workloadR workloadL.

  (** *** busy_interval_too_much_workload *)

  Definition src_busy_interval_too_much_workload : Prop :=
    ltac:(body_of (fun s : S.statement_busy_interval_too_much_workload => s Task Job jtR jaR costR PStateR interR workloadR)).
  Definition tgt_busy_interval_too_much_workload : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_busy_interval_too_much_workload
      Task dT Job dJ jtL jaL costL PStateL interL workloadL)).

  Theorem busy_interval_too_much_workload_correspondence :
    PropSPropRel src_busy_interval_too_much_workload tgt_busy_interval_too_much_workload.
  Proof.
    unfold src_busy_interval_too_much_workload, tgt_busy_interval_too_much_workload.
    apply ad_imp_correspondence;
      [exact (no_speculative_execution_correspondence Job interR interL workloadR workloadL Hinter Hworkload)|].
    apply bia_forall_arr. intros arrR arrL Harr.
    apply ad_imp_correspondence;
      [exact (consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ad_imp_correspondence; [exact (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr)|].
    apply ad_forall_identity_correspondence. intro tsk.
    apply bia_forall_sched. intros sR sL Hs.
    apply ad_imp_correspondence;
      [exact (ad_work_conserving_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
        interR interL Hinter workloadR workloadL Hworkload arrR arrL (bia_arr_ad arrR arrL Harr))|].
    apply ad_imp_correspondence; [exact (bia_must_arrive_rel sR sL Hs)|].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j (bia_arr_ad arrR arrL Harr))|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (bia_cost_positive_related j))|].
    apply ad_forall_nat_correspondence. intros tbR tbL Htb.
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_imp_correspondence;
      [exact (bia_bip_rel interR interL Hinter workloadR workloadL Hworkload sR sL Hs j _ _ _ _ H1
        (bia_succ_related _ _ Htb))|].
    apply ad_forall_nat_correspondence. intros dR dL Hd.
    have Hend := bia_add_related _ _ _ _ H1 Hd.
    apply ad_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd)|].
    apply ad_imp_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _
        (bia_add_related _ _ _ _ (workload_of_job_correspondence Job costR costL Hcost arrR arrL Harr j _ _ _ _ H1 Hend)
          (cumulative_interfering_workload_correspondence Job workloadR workloadL Hworkload j _ _ _ _ H1 Hend)) Hd)|].
    apply ad_imp_correspondence;
      [exact (bia_no_quiet_rel interR interL Hinter workloadR workloadL Hworkload sR sL Hs j _ _ _ _ H1 Hd)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (bia_add_related _ _ _ _ (Hcost j)
        (cumulative_interfering_workload_correspondence Job workloadR workloadL Hworkload j _ _ _ _ H1 Hend))
      (bia_add_related _ _ _ _ (ad_service_during_related Job PStateR PStateL R sR sL Hs j _ _ _ _ H1 Hend)
        (cumulative_interference_correspondence Job interR interL j _ _ _ _ Hinter H1 Hend))).
  Qed.
  End TooMuch.

  (** *** t1δ_is_quiet *)

  Definition src_t1δ_is_quiet : Prop :=
    ltac:(body_of (fun s : S.statement_t1δ_is_quiet => s Task Job jtR jaR costR PStateR)).
  Definition tgt_t1δ_is_quiet : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_t1_UU03b4__is_quiet
      Task dT Job dJ jtL jaL costL PStateL)).

  Theorem t1δ_is_quiet_correspondence : PropSPropRel src_t1δ_is_quiet tgt_t1δ_is_quiet.
  Proof.
    unfold src_t1δ_is_quiet, tgt_t1δ_is_quiet.
    apply ad_imp_correspondence; [exact bia_unit_service_rel|].
    apply bia_forall_inter. intros interR interL Hinter.
    apply bia_forall_iw. intros workloadR workloadL Hworkload.
    apply ad_imp_correspondence;
      [exact (no_speculative_execution_correspondence Job interR interL workloadR workloadL Hinter Hworkload)|].
    apply bia_forall_arr. intros arrR arrL Harr.
    apply ad_imp_correspondence;
      [exact (consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ad_imp_correspondence; [exact (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr)|].
    apply ad_forall_identity_correspondence. intro tsk.
    apply bia_forall_sched. intros sR sL Hs.
    apply ad_imp_correspondence;
      [exact (ad_work_conserving_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
        interR interL Hinter workloadR workloadL Hworkload arrR arrL (bia_arr_ad arrR arrL Harr))|].
    apply ad_imp_correspondence; [exact (bia_must_arrive_rel sR sL Hs)|].
    apply ad_imp_correspondence; [exact (bia_completed_dont_execute_rel sR sL Hs)|].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j (bia_arr_ad arrR arrL Harr))|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (bia_cost_positive_related j))|].
    apply ad_forall_nat_correspondence. intros tbR tbL Htb.
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (bia_pending_related sR sL Hs j _ _ Htb))|].
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_imp_correspondence;
      [exact (bia_bip_rel interR interL Hinter workloadR workloadL Hworkload sR sL Hs j _ _ _ _ H1
        (bia_succ_related _ _ Htb))|].
    apply ad_forall_nat_correspondence. intros dR dL Hd.
    have Hend := bia_add_related _ _ _ _ H1 Hd.
    apply ad_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd)|].
    apply ad_imp_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _
        (bia_add_related _ _ _ _ (workload_of_job_correspondence Job costR costL Hcost arrR arrL Harr j _ _ _ _ H1 Hend)
          (cumulative_interfering_workload_correspondence Job workloadR workloadL Hworkload j _ _ _ _ H1 Hend)) Hd)|].
    apply ad_imp_correspondence;
      [exact (bia_no_quiet_rel interR interL Hinter workloadR workloadL Hworkload sR sL Hs j _ _ _ _ H1 Hd)|].
    exact (ad_bool_truth_correspondence _ _
      (ad_quiet_time_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
        interR interL Hinter workloadR workloadL Hworkload j _ _ Hend)).
  Qed.

  (** *** t1δ_is_quiet_contra *)

  Definition src_t1δ_is_quiet_contra : Prop :=
    ltac:(body_of (fun s : S.statement_t1δ_is_quiet_contra => s Task Job jtR jaR costR PStateR)).
  Definition tgt_t1δ_is_quiet_contra : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_t1_UU03b4__is_quiet_contra
      Task dT Job dJ jtL jaL costL PStateL)).

  Theorem t1δ_is_quiet_contra_correspondence : PropSPropRel src_t1δ_is_quiet_contra tgt_t1δ_is_quiet_contra.
  Proof.
    unfold src_t1δ_is_quiet_contra, tgt_t1δ_is_quiet_contra.
    apply ad_imp_correspondence; [exact bia_unit_service_rel|].
    apply bia_forall_inter. intros interR interL Hinter.
    apply bia_forall_iw. intros workloadR workloadL Hworkload.
    apply ad_imp_correspondence;
      [exact (no_speculative_execution_correspondence Job interR interL workloadR workloadL Hinter Hworkload)|].
    apply bia_forall_arr. intros arrR arrL Harr.
    apply ad_imp_correspondence;
      [exact (consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ad_imp_correspondence; [exact (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr)|].
    apply ad_forall_identity_correspondence. intro tsk.
    apply bia_forall_sched. intros sR sL Hs.
    apply ad_imp_correspondence;
      [exact (ad_work_conserving_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
        interR interL Hinter workloadR workloadL Hworkload arrR arrL (bia_arr_ad arrR arrL Harr))|].
    apply ad_imp_correspondence; [exact (bia_must_arrive_rel sR sL Hs)|].
    apply ad_imp_correspondence; [exact (bia_completed_dont_execute_rel sR sL Hs)|].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j (bia_arr_ad arrR arrL Harr))|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (bia_cost_positive_related j))|].
    apply ad_forall_nat_correspondence. intros tbR tbL Htb.
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (bia_pending_related sR sL Hs j _ _ Htb))|].
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_imp_correspondence;
      [exact (bia_bip_rel interR interL Hinter workloadR workloadL Hworkload sR sL Hs j _ _ _ _ H1
        (bia_succ_related _ _ Htb))|].
    apply ad_forall_nat_correspondence. intros dR dL Hd.
    have Hend := bia_add_related _ _ _ _ H1 Hd.
    apply ad_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd)|].
    apply ad_imp_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _
        (bia_add_related _ _ _ _ (workload_of_job_correspondence Job costR costL Hcost arrR arrL Harr j _ _ _ _ H1 Hend)
          (cumulative_interfering_workload_correspondence Job workloadR workloadL Hworkload j _ _ _ _ H1 Hend)) Hd)|].
    apply ad_imp_correspondence;
      [exact (bia_no_quiet_rel interR interL Hinter workloadR workloadL Hworkload sR sL Hs j _ _ _ _ H1 Hd)|].
    exact ad_false_correspondence.
  Qed.

  (** *** busy_interval_is_bounded *)

  Definition src_busy_interval_is_bounded : Prop :=
    ltac:(body_of (fun s : S.statement_busy_interval_is_bounded => s Task Job jtR jaR costR PStateR)).
  Definition tgt_busy_interval_is_bounded : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_BusyInterval_busy_interval_is_bounded
      Task dT Job dJ jtL jaL costL PStateL)).

  Theorem busy_interval_is_bounded_correspondence : PropSPropRel src_busy_interval_is_bounded tgt_busy_interval_is_bounded.
  Proof.
    unfold src_busy_interval_is_bounded, tgt_busy_interval_is_bounded.
    apply ad_imp_correspondence; [exact bia_unit_service_rel|].
    apply bia_forall_inter. intros interR interL Hinter.
    apply bia_forall_iw. intros workloadR workloadL Hworkload.
    apply ad_imp_correspondence;
      [exact (no_speculative_execution_correspondence Job interR interL workloadR workloadL Hinter Hworkload)|].
    apply bia_forall_arr. intros arrR arrL Harr.
    apply ad_imp_correspondence;
      [exact (consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ad_imp_correspondence; [exact (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr)|].
    apply ad_forall_identity_correspondence. intro tsk.
    apply bia_forall_sched. intros sR sL Hs.
    apply ad_imp_correspondence;
      [exact (ad_work_conserving_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
        interR interL Hinter workloadR workloadL Hworkload arrR arrL (bia_arr_ad arrR arrL Harr))|].
    apply ad_imp_correspondence; [exact (bia_must_arrive_rel sR sL Hs)|].
    apply ad_imp_correspondence; [exact (bia_completed_dont_execute_rel sR sL Hs)|].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j (bia_arr_ad arrR arrL Harr))|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (bia_cost_positive_related j))|].
    apply ad_forall_nat_correspondence. intros tbR tbL Htb.
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (bia_pending_related sR sL Hs j _ _ Htb))|].
    apply ad_forall_nat_correspondence. intros t1R t1L H1.
    apply ad_imp_correspondence;
      [exact (bia_bip_rel interR interL Hinter workloadR workloadL Hworkload sR sL Hs j _ _ _ _ H1
        (bia_succ_related _ _ Htb))|].
    apply ad_forall_nat_correspondence. intros dR dL Hd.
    have Hend := bia_add_related _ _ _ _ H1 Hd.
    apply ad_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd)|].
    apply ad_imp_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _
        (bia_add_related _ _ _ _ (workload_of_job_correspondence Job costR costL Hcost arrR arrL Harr j _ _ _ _ H1 Hend)
          (cumulative_interfering_workload_correspondence Job workloadR workloadL Hworkload j _ _ _ _ H1 Hend)) Hd)|].
    apply ad_exists_nat_correspondence. intros t2R t2L H2.
    apply ad_and_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Htb H2)|].
    apply ad_and_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H2 Hend)|].
    exact (bia_bi_rel interR interL Hinter workloadR workloadL Hworkload sR sL Hs j _ _ _ _ H1 H2).
  Qed.
End BusyInterval.
