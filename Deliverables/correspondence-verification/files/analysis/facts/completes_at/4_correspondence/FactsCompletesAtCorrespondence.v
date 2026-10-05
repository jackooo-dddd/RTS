From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsCompletesAtSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.priority.classes.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsCompletesAt ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers
  BusyIntervalClassicalHelpers.

Module I := ImportedFactsCompletesAt.
Module S := FactsCompletesAtSemanticSource.FactsCompletesAtSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module PTS := PreemptionTimeSemanticSource.PreemptionTimeSemanticSource.

(** Statement correspondences for [analysis/facts/completes_at.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.
    Inputs: processor states by the accepted two-sided [SvcProcessorStateRel]
    of the preemption-parameter family, schedules through it; [job_arrival]
    by [ArJobArrivalRel]; [job_cost] by the accepted [SvcJobCostRel]; the JLFP
    policy by the accepted [BicJLFPRel]; arrival sequences by
    [ArArrivalSequenceRel]; jobs identity, instants by [SubNatRel].  Inputs
    quantified inside a statement are covered in both directions by explicit
    conversions: arrival sequences, schedules (through the state relation),
    [JobPreemptable] instances (the accepted total conversions), Boolean job
    predicates, jobs (identity) and instants.  [completes_at] is related
    through the accepted completion certificate; the interval sum by the
    accepted interval-sum certificate (the Lean statement's [Finset.Ico] sum
    is exported in the accepted [List.foldr] form after its kernel [rfl]
    guard); the filtered list sum by induction over related lists; the
    classical busy-interval prefix by the accepted classical busy-interval
    certificate; preemption time, preemption-model validity and the
    uniprocessor property by the accepted preemption-parameter,
    preemption-time and processor-cover certificates.  No source or target
    theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fca_bool_to_nat_related (bR : bool) (bL : I.Bool) :
  ArBoolRel bR bL -> SubNatRel (nat_of_bool bR) (I.Bool_toNat bL).
Proof.
  intro Hb. unfold ArBoolRel in Hb. destruct Hb.
  destruct bR; cbn; [exact (sub_nat_rel_canonical 1) | exact (sub_nat_rel_canonical O)].
Qed.

Lemma fca_sum_filter_related (T : Type) (PR : T -> bool) (PL : T -> I.Bool)
    (HP : forall x, ArBoolRel (PR x) (PL x))
    (FR : T -> nat) (FL : T -> Lean.Nat) (HF : forall x, SubNatRel (FR x) (FL x))
    (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered T xsL PL FL).
Proof.
  intro Hxs. unfold ArListRel in Hxs. destruct Hxs.
  induction xsR as [|x xs IH].
  - rewrite big_nil. exact (@Lean.eq_refl _ _).
  - rewrite big_cons. have Hx := HP x. unfold ArBoolRel in Hx.
    unfold I.Prosa_Util_Sum_sumFiltered in *. cbn.
    destruct Hx. destruct (PR x); cbn.
    + exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact IH.
Qed.

Section CompletesAt.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.

  (** *** Covers *)

  Definition fca_sched_to_target (sR : SchedR) : SchedL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (sR (sub_nat_to_rocq tL)).
  Definition fca_sched_to_source (sL : SchedL) : SchedR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (sL (sub_nat_to_imported tR)).

  Lemma fca_forall_sched (PRs : SchedR -> Prop) (PLs : SchedL -> SProp) :
    (forall sR sL, SvcScheduleRel Job PStateR PStateL R sR sL -> PropSPropRel (PRs sR) (PLs sL)) ->
    PropSPropRel (forall s, PRs s) (forall s, PLs s).
  Proof.
    apply (isj_forall_cover_sprop _ _ (SvcScheduleRel Job PStateR PStateL R)
      fca_sched_to_target fca_sched_to_source).
    - intros sR tR tL Ht. unfold fca_sched_to_target. rewrite (isj_nat_input _ _ Ht).
      exact (svc_ps_state_rel_canonical Job PStateR PStateL R _).
    - intros sL tR tL Ht. destruct Ht.
      exact (svc_ps_state_rel_surjective Job PStateR PStateL R _).
  Qed.

  Lemma fca_forall_arr (PRa : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
      (PLa : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ -> SProp) :
    (forall aR aL, ArArrivalSequenceRel Job aR aL -> PropSPropRel (PRa aR) (PLa aL)) ->
    PropSPropRel (forall a, PRa a) (forall a, PLa a).
  Proof.
    exact (isj_forall_cover_sprop _ _ (ArArrivalSequenceRel Job) (ar_arrival_sequence_to_imported Job)
      (isj_arrival_sequence_to_source Job) (ar_arrival_sequence_canonical Job)
      (isj_arrival_sequence_to_source_rel Job) PRa PLa).
  Qed.

  Lemma fca_forall_jp (PRj : PP.JobPreemptable Job -> Prop)
      (PLj : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ -> SProp) :
    (forall jpR jpL, PpJobPreemptableRel Job jpR jpL -> PropSPropRel (PRj jpR) (PLj jpL)) ->
    PropSPropRel (forall jp, PRj jp) (forall jp, PLj jp).
  Proof.
    exact (isj_forall_cover_sprop _ _ (PpJobPreemptableRel Job)
      (fun jpR => I.Prosa_Model_Preemption_Parameter_JobPreemptable_mk Job dJ
        (fun j nL => ar_bool_to_imported (jpR j (sub_nat_to_rocq nL))))
      (fun jpL => ((fun j n => ar_bool_to_rocq
        (I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job dJ jpL j
          (sub_nat_to_imported n))) : PP.JobPreemptable Job))
      (JobPreemptable_source_total Job) (JobPreemptable_target_total Job) PRj PLj).
  Qed.

  Lemma fca_forall_pred (PRp : pred Job -> Prop) (PLp : (Job -> I.Bool) -> SProp) :
    (forall pR pL, (forall x, ArBoolRel (pR x) (pL x)) -> PropSPropRel (PRp pR) (PLp pL)) ->
    PropSPropRel (forall p, PRp p) (forall p, PLp p).
  Proof.
    apply (isj_forall_cover_sprop _ _ (fun (pR : pred Job) (pL : Job -> I.Bool) =>
        forall x, ArBoolRel (pR x) (pL x))
      (fun pR x => ar_bool_to_imported (pR x)) (fun pL x => ar_bool_to_rocq (pL x))).
    - intros pR x. exact (@Lean.eq_refl _ _).
    - intros pL x. exact (ar_bool_target_roundtrip _).
  Qed.

  (** *** Observations over a related schedule pair *)

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : SvcScheduleRel Job PStateR PStateL R sR sL.

    Let Hsa := pp_scheduled_at_related Job PStateR PStateL R sR sL Hs.

    Lemma fca_completes_at_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
      ArBoolRel (@prosa.behavior.service.completes_at Job PStateR sR costR j tR)
        (I.Prosa_Behavior_Service_completes_at Job dJ PStateL sL costL j tL).
    Proof.
      unfold prosa.behavior.service.completes_at.
      cbn [I.Prosa_Behavior_Service_completes_at].
      rewrite -subn1.
      apply ar_bool_and_related.
      - apply pp_bool_or_related.
        + exact (svc_bool_not_related _ _ (pp_completed_by_related Job costR costL Hcost PStateR PStateL R sR sL Hs
            j _ _ (svc_target_sub_related _ _ _ _ Ht (sub_nat_rel_canonical 1)))).
        + exact (pp_nat_eqb_related _ _ _ _ Ht (sub_nat_rel_canonical O)).
      - exact (pp_completed_by_related Job costR costL Hcost PStateR PStateL R sR sL Hs j tR tL Ht).
    Qed.

    Lemma fca_completed_dont_execute_rel :
      PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PStateR sR costR)
        (I.Prosa_Behavior_Ready_completed_jobs_dont_execute Job dJ PStateL sL costL).
    Proof.
      unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j tR tL Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _
        (pp_service_related Job PStateR PStateL R sR sL Hs j tR tL Ht) (Hcost j)).
    Qed.
  End Sched.

  (** ** Statements over a leading schedule *)

  Section LeadingSched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : SvcScheduleRel Job PStateR PStateL R sR sL.

    Definition src_scheduled_at_precedes_completes_at : Prop :=
      ltac:(body_of (fun s : S.statement_scheduled_at_precedes_completes_at => s Job costR PStateR sR)).
    Definition tgt_scheduled_at_precedes_completes_at : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_CompletesAt_scheduled_at_precedes_completes_at
        Job dJ costL PStateL sL)).

    Theorem scheduled_at_precedes_completes_at_correspondence :
      PropSPropRel src_scheduled_at_precedes_completes_at tgt_scheduled_at_precedes_completes_at.
    Proof.
      unfold src_scheduled_at_precedes_completes_at, tgt_scheduled_at_precedes_completes_at.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Ht)|].
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (fca_completes_at_related sR sL Hs j tR tL Ht))|].
      rewrite -subn1.
      exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related Job PStateR PStateL R sR sL Hs j _ _
        (svc_target_sub_related _ _ _ _ Ht (sub_nat_rel_canonical 1)))).
    Qed.

    Definition src_job_completes_at_most_once : Prop :=
      ltac:(body_of (fun s : S.statement_job_completes_at_most_once => s Job costR PStateR sR)).
    Definition tgt_job_completes_at_most_once : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_CompletesAt_job_completes_at_most_once
        Job dJ costL PStateL sL)).

    Theorem job_completes_at_most_once_correspondence :
      PropSPropRel src_job_completes_at_most_once tgt_job_completes_at_most_once.
    Proof.
      unfold src_job_completes_at_most_once, tgt_job_completes_at_most_once.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros t1R t1L H1.
      apply ar_forall_nat_correspondence. intros t2R t2L H2.
      exact (sub_nat_le_correspondence _ _ _ _
        (svc_interval_sum_related t1R t2R t1L t2L
          (fun t => nat_of_bool (@prosa.behavior.service.completes_at Job PStateR sR costR j t))
          (fun t => I.Bool_toNat (I.Prosa_Behavior_Service_completes_at Job dJ PStateL sL costL j t))
          H1 H2 (fun tR tL Ht => fca_bool_to_nat_related _ _ (fca_completes_at_related sR sL Hs j tR tL Ht)))
        (sub_nat_rel_canonical 1)).
    Qed.
  End LeadingSched.

  (** ** Statements quantifying the arrival sequence and schedule inside *)

  Definition src_only_one_job_completes_at_a_time : Prop :=
    ltac:(body_of (fun s : S.statement_only_one_job_completes_at_a_time => s Job jaR costR PStateR)).
  Definition tgt_only_one_job_completes_at_a_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_CompletesAt_only_one_job_completes_at_a_time
      Job dJ jaL costL PStateL)).

  Theorem only_one_job_completes_at_a_time_correspondence :
    PropSPropRel src_only_one_job_completes_at_a_time tgt_only_one_job_completes_at_a_time.
  Proof.
    unfold src_only_one_job_completes_at_a_time, tgt_only_one_job_completes_at_a_time.
    apply ar_imp_correspondence; [exact (isj_uniprocessor_related Job PStateR PStateL R)|].
    apply fca_forall_arr. intros arrR arrL Harr.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply fca_forall_sched. intros sR sL Hs.
    apply fca_forall_pred. intros pR pL Hp.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros BR BL HB.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Ht)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (fca_sum_filter_related Job pR pL Hp _ _
        (fun j => fca_bool_to_nat_related _ _ (fca_completes_at_related sR sL Hs j tR tL Ht)) _ _
        (arrivals_before_correspondence_certificate Job arrR arrL Harr BR BL HB))
      (sub_nat_rel_canonical 1)).
  Qed.

  Definition src_completetion_time_is_preemption_time : Prop :=
    ltac:(body_of (fun s : S.statement_completetion_time_is_preemption_time => s Job jaR costR PStateR)).
  Definition tgt_completetion_time_is_preemption_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_CompletesAt_completetion_time_is_preemption_time
      Job dJ jaL costL PStateL)).

  Theorem completetion_time_is_preemption_time_correspondence :
    PropSPropRel src_completetion_time_is_preemption_time tgt_completetion_time_is_preemption_time.
  Proof.
    unfold src_completetion_time_is_preemption_time, tgt_completetion_time_is_preemption_time.
    apply ar_imp_correspondence; [exact (isj_uniprocessor_related Job PStateR PStateL R)|].
    apply fca_forall_arr. intros arrR arrL Harr.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply fca_forall_sched. intros sR sL Hs.
    have Hsa := pp_scheduled_at_related Job PStateR PStateL R sR sL Hs.
    apply ar_imp_correspondence; [exact (isj_jobs_come_from_related Job PStateR PStateL sR sL Hsa arrR arrL Harr)|].
    apply ar_imp_correspondence; [exact (isj_jobs_must_arrive_related Job PStateR PStateL sR sL Hsa jaR jaL Hja)|].
    apply ar_imp_correspondence; [exact (fca_completed_dont_execute_rel sR sL Hs)|].
    apply fca_forall_jp. intros jpR jpL Hjp.
    apply ar_imp_correspondence;
      [exact (valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL R
        sR sL Hs arrR arrL Harr)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (fca_completes_at_related sR sL Hs j tR tL Ht))|].
    exact (ar_bool_truth_correspondence _ _
      (preemption_time_correspondence Job jpR jpL Hjp PStateR PStateL R sR sL Hs arrR arrL Harr tR tL Ht)).
  Qed.

  (** ** The busy-prefix statement (leading policy and arrival sequence) *)

  Section LeadingPolicy.
    Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
    Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
    Hypothesis Hp : BicJLFPRel Job pR pL.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Definition src_no_early_hep_job_completes_during_busy_prefix : Prop :=
      ltac:(body_of (fun s : S.statement_no_early_hep_job_completes_during_busy_prefix =>
        s Job jaR costR pR PStateR arrR)).
    Definition tgt_no_early_hep_job_completes_during_busy_prefix : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_CompletesAt_no_early_hep_job_completes_during_busy_prefix
        Job dJ jaL costL pL PStateL arrL)).

    Theorem no_early_hep_job_completes_during_busy_prefix_correspondence :
      PropSPropRel src_no_early_hep_job_completes_during_busy_prefix
        tgt_no_early_hep_job_completes_during_busy_prefix.
    Proof.
      unfold src_no_early_hep_job_completes_during_busy_prefix,
        tgt_no_early_hep_job_completes_during_busy_prefix.
      apply ar_imp_correspondence;
        [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
      apply fca_forall_sched. intros sR sL Hs.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_nat_correspondence. intros t1R t1L H1.
      apply ar_forall_nat_correspondence. intros t2R t2L H2.
      apply ar_imp_correspondence;
        [exact (busy_interval_prefix_correspondence Job jaR jaL Hja costR costL Hcost PStateR PStateL R
          arrR arrL Harr sR sL Hs pR pL Hp j _ _ _ _ H1 H2)|].
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
          (ar_decide_lt_related _ _ _ _ H1 Ht) (ar_decide_le_related _ _ _ _ Ht H2)))|].
      apply ar_forall_identity_correspondence. intro jhp.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Job jhp _ _
          (arrivals_before_correspondence_certificate Job arrR arrL Harr t1R t1L H1)))|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp jhp j))|].
      exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (fca_completes_at_related sR sL Hs jhp tR tL Ht))).
    Qed.
  End LeadingPolicy.
End CompletesAt.
