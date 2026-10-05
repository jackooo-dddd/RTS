From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsRtcJobPreemptableSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsRtcJobPreemptable ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence.

Module I := ImportedFactsRtcJobPreemptable.
Module S := FactsRtcJobPreemptableSemanticSource.FactsRtcJobPreemptableSemanticSource.
Module G := prosa.GeneratedNondecreasingSource.GeneratedNondecreasingSource.
Module P := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.

(** Statement correspondences for
    [analysis/facts/preemption/rtc_threshold/job_preemptable.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (job type, job cost, preemption model, processor
    state, arrival sequence, schedule); target side: the imported Lean
    theorem types at related inputs ([SvcJobCostRel], the accepted
    [PpJobPreemptableRel], the accepted two-sided
    [SvcProcessorStateRel]/[SvcScheduleRel], [ArArrivalSequenceRel]).
    Jobs are identity carriers, Nats are covered in both directions.  The
    preemption points, segment lengths, run-to-completion threshold,
    validity and membership are closed by the accepted
    [PreemptionParameterCorrespondence]; list length, [nthD] and
    [nondecreasing_sequence] replay the accepted limited-preemptive helpers;
    list equality goes through the source-side list roundtrip.  No source
    or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma frtc_length_canonical (xs : seq nat) :
  SubNatRel (size xs) (I.List_length_inst1 Lean.Nat (svc_nat_list_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero).
  - cbn [svc_nat_list_to_imported].
    exact (sub_imported_eq_congr Lean.Nat_succ _ _ IH).
Qed.

Lemma frtc_length_related xsR xsL : SvcNatListRel xsR xsL ->
  SubNatRel (size xsR) (I.List_length_inst1 Lean.Nat xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _ (frtc_length_canonical xsR)
    (sub_imported_eq_congr (I.List_length_inst1 Lean.Nat) _ _ Hxs)).
Qed.

Lemma frtc_nthD_canonical (xs : seq nat) (n : nat) :
  SubNatRel (nth O xs n)
    (I.Prosa_Validation_NondecreasingInterface_nthD (svc_nat_list_to_imported xs)
      (sub_nat_to_imported n)).
Proof.
  revert n. induction xs as [|x xs IH]; intro n; destruct n;
    cbn [svc_nat_list_to_imported sub_nat_to_imported];
    try exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero);
    try exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported x));
    exact (IH n).
Qed.

Lemma frtc_nthD_related xsR xsL nR nL :
  SvcNatListRel xsR xsL -> SubNatRel nR nL ->
  SubNatRel (nth O xsR nR) (I.Prosa_Validation_NondecreasingInterface_nthD xsL nL).
Proof.
  intros Hxs Hn. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _ (frtc_nthD_canonical xsR nR)
    (sub_imported_eq_congr2 I.Prosa_Validation_NondecreasingInterface_nthD _ _ _ _ Hxs Hn)).
Qed.

Lemma frtc_nondecreasing_sequence_related xsR xsL :
  SvcNatListRel xsR xsL ->
  PropSPropRel (G.nondecreasing_sequence xsR)
    (I.Prosa_Util_Nondecreasing_nondecreasing_sequence xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intros HR n1L n2L HboundsL.
    set n1R := sub_nat_to_rocq n1L.
    set n2R := sub_nat_to_rocq n2L.
    have Hn1 : SubNatRel n1R n1L := sub_nat_rel_surjective n1L.
    have Hn2 : SubNatRel n2R n2L := sub_nat_rel_surjective n2L.
    destruct HboundsL as [HleL HltL].
    apply (prop_to_sprop _ _
      (sub_nat_le_correspondence _ _ _ _
        (frtc_nthD_related xsR xsL n1R n1L Hxs Hn1)
        (frtc_nthD_related xsR xsL n2R n2L Hxs Hn2))).
    apply HR. apply/andP; split.
    + exact (sprop_to_prop _ _ (sub_nat_le_correspondence _ _ _ _ Hn1 Hn2) HleL).
    + exact (sprop_to_prop _ _
        (sub_nat_lt_correspondence _ _ _ _ Hn2 (frtc_length_related xsR xsL Hxs)) HltL).
  - intro HL. apply strictly_inhabits.
    intros n1R n2R HboundsR.
    move: HboundsR => /andP [HleR HltR].
    have Hn1 := sub_nat_rel_canonical n1R.
    have Hn2 := sub_nat_rel_canonical n2R.
    exact (sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _
        (frtc_nthD_related xsR xsL n1R (sub_nat_to_imported n1R) Hxs Hn1)
        (frtc_nthD_related xsR xsL n2R (sub_nat_to_imported n2R) Hxs Hn2))
      (HL (sub_nat_to_imported n1R) (sub_nat_to_imported n2R)
        (Lean.And_intro _ _
          (prop_to_sprop _ _ (sub_nat_le_correspondence _ _ _ _ Hn1 Hn2) HleR)
          (prop_to_sprop _ _
            (sub_nat_lt_correspondence _ _ _ _ Hn2 (frtc_length_related xsR xsL Hxs)) HltR)))).
Qed.

Fixpoint frtc_nat_list_to_rocq (xs : I.List_inst1 Lean.Nat) : seq nat :=
  match xs with
  | I.List_nil_inst1 => [::]
  | I.List_cons_inst1 x tail => sub_nat_to_rocq x :: frtc_nat_list_to_rocq tail
  end.

Lemma frtc_nat_list_source_roundtrip (xs : seq nat) :
  frtc_nat_list_to_rocq (svc_nat_list_to_imported xs) = xs.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  cbn [svc_nat_list_to_imported frtc_nat_list_to_rocq].
  by rewrite sub_nat_rocq_roundtrip IH.
Qed.

Lemma frtc_list_eq_correspondence xsR xsL ysR ysL :
  SvcNatListRel xsR xsL -> SvcNatListRel ysR ysL ->
  PropSPropRel (xsR = ysR) (Lean.eq xsL ysL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro E. destruct E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hx) Hy).
  - intro EL. apply strictly_inhabits.
    have E := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hx (sub_imported_eq_trans _ _ _ EL (sub_imported_eq_sym _ _ Hy))).
    have E2 := f_equal frtc_nat_list_to_rocq E.
    by rewrite !frtc_nat_list_source_roundtrip in E2.
Qed.

Section Rtc.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jpR : P.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.

  Let PTS := job_preemption_points_correspondence Job costR costL Hcost jpR jpL Hjp.
  Let MAX := job_max_nonpreemptive_segment_correspondence Job costR costL Hcost jpR jpL Hjp.
  Let LAST := job_last_nonpreemptive_segment_correspondence Job costR costL Hcost jpR jpL Hjp.
  Let RTCT := job_rtct_correspondence Job costR costL Hcost jpR jpL Hjp.

  Lemma frtc_cost_positive_related (j : Job) :
    ArBoolRel (@prosa.model.job.properties.job_cost_positive Job costR j)
      (I.Prosa_Model_Job_Properties_job_cost_positive Job dJ costL j).
  Proof.
    unfold prosa.model.job.properties.job_cost_positive.
    cbn [I.Prosa_Model_Job_Properties_job_cost_positive].
    exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost j)).
  Qed.

  Definition src_preemption_points_nondecreasing : Prop :=
    ltac:(body_of (fun s : S.statement_preemption_points_nondecreasing => s Job costR jpR)).
  Definition tgt_preemption_points_nondecreasing : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_preemption_points_nondecreasing
      Job dJ costL jpL)).
  Theorem preemption_points_nondecreasing_correspondence :
    PropSPropRel src_preemption_points_nondecreasing tgt_preemption_points_nondecreasing.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    exact (frtc_nondecreasing_sequence_related _ _ (PTS j)).
  Qed.

  Definition src_job_run_to_completion_threshold_le_job_cost : Prop :=
    ltac:(body_of (fun s : S.statement_job_run_to_completion_threshold_le_job_cost => s Job costR jpR)).
  Definition tgt_job_run_to_completion_threshold_le_job_cost : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_run_to_completion_threshold_le_job_cost
      Job dJ costL jpL)).
  Theorem job_run_to_completion_threshold_le_job_cost_correspondence :
    PropSPropRel src_job_run_to_completion_threshold_le_job_cost tgt_job_run_to_completion_threshold_le_job_cost.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    exact (sub_nat_le_correspondence _ _ _ _ (RTCT j) (Hcost j)).
  Qed.

  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Let VALID := valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp
    PStateR PStateL R schedR schedL Hsched arrR arrL Harr.
  Let ARR (j : Job) := arrives_in_correspondence_certificate Job arrR arrL j Harr.

  Ltac frtc_prefix :=
    apply ar_imp_correspondence; [exact VALID|];
    apply ar_forall_identity_correspondence;
    let j := fresh "j" in intro j;
    apply ar_imp_correspondence; [exact (ARR j)|].

  Definition src_preemption_points_of_zero_cost_job : Prop :=
    ltac:(body_of (fun s : S.statement_preemption_points_of_zero_cost_job => s Job costR jpR PStateR arrR schedR)).
  Definition tgt_preemption_points_of_zero_cost_job : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_preemption_points_of_zero_cost_job
      Job dJ costL jpL PStateL arrL schedL)).
  Theorem preemption_points_of_zero_cost_job_correspondence :
    PropSPropRel src_preemption_points_of_zero_cost_job tgt_preemption_points_of_zero_cost_job.
  Proof.
    frtc_prefix.
    apply ar_imp_correspondence;
      [exact (sub_nat_eq_correspondence _ _ _ _ (Hcost j) (sub_nat_rel_canonical O))|].
    exact (frtc_list_eq_correspondence _ _ [:: O] _ (PTS j) (@Lean.eq_refl _ _)).
  Qed.

  Definition src_zero_in_preemption_points : Prop :=
    ltac:(body_of (fun s : S.statement_zero_in_preemption_points => s Job costR jpR PStateR arrR schedR)).
  Definition tgt_zero_in_preemption_points : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_zero_in_preemption_points
      Job dJ costL jpL PStateL arrL schedL)).
  Theorem zero_in_preemption_points_correspondence :
    PropSPropRel src_zero_in_preemption_points tgt_zero_in_preemption_points.
  Proof.
    frtc_prefix.
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))|].
    exact (pp_mem_related _ _ _ _ (sub_nat_rel_canonical O) (PTS j)).
  Qed.

  Definition src_job_cost_in_preemption_points : Prop :=
    ltac:(body_of (fun s : S.statement_job_cost_in_preemption_points => s Job costR jpR PStateR arrR schedR)).
  Definition tgt_job_cost_in_preemption_points : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_cost_in_preemption_points
      Job dJ costL jpL PStateL arrL schedL)).
  Theorem job_cost_in_preemption_points_correspondence :
    PropSPropRel src_job_cost_in_preemption_points tgt_job_cost_in_preemption_points.
  Proof.
    frtc_prefix.
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))|].
    exact (pp_mem_related _ _ _ _ (Hcost j) (PTS j)).
  Qed.

  Definition src_size_of_preemption_points : Prop :=
    ltac:(body_of (fun s : S.statement_size_of_preemption_points => s Job costR jpR PStateR arrR schedR)).
  Definition tgt_size_of_preemption_points : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_size_of_preemption_points
      Job dJ costL jpL PStateL arrL schedL)).
  Theorem size_of_preemption_points_correspondence :
    PropSPropRel src_size_of_preemption_points tgt_size_of_preemption_points.
  Proof.
    frtc_prefix.
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 1) (frtc_length_related _ _ (PTS j))).
  Qed.

  Definition src_job_cost_is_last_element_of_preemption_points : Prop :=
    ltac:(body_of (fun s : S.statement_job_cost_is_last_element_of_preemption_points => s Job costR jpR PStateR arrR schedR)).
  Definition tgt_job_cost_is_last_element_of_preemption_points : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_cost_is_last_element_of_preemption_points
      Job dJ costL jpL PStateL arrL schedL)).
  Theorem job_cost_is_last_element_of_preemption_points_correspondence :
    PropSPropRel src_job_cost_is_last_element_of_preemption_points tgt_job_cost_is_last_element_of_preemption_points.
  Proof.
    frtc_prefix.
    exact (sub_nat_eq_correspondence _ _ _ _ (Hcost j) (pp_last0_related _ _ (PTS j))).
  Qed.

  Definition src_job_last_nonpreemptive_segment_positive : Prop :=
    ltac:(body_of (fun s : S.statement_job_last_nonpreemptive_segment_positive => s Job costR jpR PStateR arrR schedR)).
  Definition tgt_job_last_nonpreemptive_segment_positive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_last_nonpreemptive_segment_positive
      Job dJ costL jpL PStateL arrL schedL)).
  Theorem job_last_nonpreemptive_segment_positive_correspondence :
    PropSPropRel src_job_last_nonpreemptive_segment_positive tgt_job_last_nonpreemptive_segment_positive.
  Proof.
    frtc_prefix.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (frtc_cost_positive_related j))|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (LAST j)).
  Qed.

  Definition src_job_max_nonpreemptive_segment_positive : Prop :=
    ltac:(body_of (fun s : S.statement_job_max_nonpreemptive_segment_positive => s Job costR jpR PStateR arrR schedR)).
  Definition tgt_job_max_nonpreemptive_segment_positive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_max_nonpreemptive_segment_positive
      Job dJ costL jpL PStateL arrL schedL)).
  Theorem job_max_nonpreemptive_segment_positive_correspondence :
    PropSPropRel src_job_max_nonpreemptive_segment_positive tgt_job_max_nonpreemptive_segment_positive.
  Proof.
    frtc_prefix.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (frtc_cost_positive_related j))|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (MAX j)).
  Qed.

  Definition src_job_max_nonpreemptive_segment_le_job_cost : Prop :=
    ltac:(body_of (fun s : S.statement_job_max_nonpreemptive_segment_le_job_cost => s Job costR jpR PStateR arrR schedR)).
  Definition tgt_job_max_nonpreemptive_segment_le_job_cost : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_max_nonpreemptive_segment_le_job_cost
      Job dJ costL jpL PStateL arrL schedL)).
  Theorem job_max_nonpreemptive_segment_le_job_cost_correspondence :
    PropSPropRel src_job_max_nonpreemptive_segment_le_job_cost tgt_job_max_nonpreemptive_segment_le_job_cost.
  Proof.
    frtc_prefix.
    exact (sub_nat_le_correspondence _ _ _ _ (MAX j) (Hcost j)).
  Qed.

  Definition src_job_last_nonpreemptive_segment_le_job_cost : Prop :=
    ltac:(body_of (fun s : S.statement_job_last_nonpreemptive_segment_le_job_cost => s Job costR jpR PStateR arrR schedR)).
  Definition tgt_job_last_nonpreemptive_segment_le_job_cost : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_last_nonpreemptive_segment_le_job_cost
      Job dJ costL jpL PStateL arrL schedL)).
  Theorem job_last_nonpreemptive_segment_le_job_cost_correspondence :
    PropSPropRel src_job_last_nonpreemptive_segment_le_job_cost tgt_job_last_nonpreemptive_segment_le_job_cost.
  Proof.
    frtc_prefix.
    exact (sub_nat_le_correspondence _ _ _ _ (LAST j) (Hcost j)).
  Qed.

  Definition src_job_run_to_completion_threshold_positive : Prop :=
    ltac:(body_of (fun s : S.statement_job_run_to_completion_threshold_positive => s Job costR jpR PStateR arrR schedR)).
  Definition tgt_job_run_to_completion_threshold_positive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_run_to_completion_threshold_positive
      Job dJ costL jpL PStateL arrL schedL)).
  Theorem job_run_to_completion_threshold_positive_correspondence :
    PropSPropRel src_job_run_to_completion_threshold_positive tgt_job_run_to_completion_threshold_positive.
  Proof.
    frtc_prefix.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (frtc_cost_positive_related j))|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (RTCT j)).
  Qed.

  Definition src_job_cannot_be_preempted_within_last_segment : Prop :=
    ltac:(body_of (fun s : S.statement_job_cannot_be_preempted_within_last_segment => s Job costR jpR PStateR arrR schedR)).
  Definition tgt_job_cannot_be_preempted_within_last_segment : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_cannot_be_preempted_within_last_segment
      Job dJ costL jpL PStateL arrL schedL)).
  Theorem job_cannot_be_preempted_within_last_segment_correspondence :
    PropSPropRel src_job_cannot_be_preempted_within_last_segment tgt_job_cannot_be_preempted_within_last_segment.
  Proof.
    frtc_prefix.
    apply ar_forall_nat_correspondence. intros rR rL Hr.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
        (ar_decide_le_related _ _ _ _ (RTCT j) Hr) (ar_decide_lt_related _ _ _ _ Hr (Hcost j))))|].
    exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hjp j _ _ Hr))).
  Qed.

  Definition src_job_nonpreemptive_after_run_to_completion_threshold : Prop :=
    ltac:(body_of (fun s : S.statement_job_nonpreemptive_after_run_to_completion_threshold => s Job costR jpR PStateR arrR schedR)).
  Definition tgt_job_nonpreemptive_after_run_to_completion_threshold : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_nonpreemptive_after_run_to_completion_threshold
      Job dJ costL jpL PStateL arrL schedL)).
  Theorem job_nonpreemptive_after_run_to_completion_threshold_correspondence :
    PropSPropRel src_job_nonpreemptive_after_run_to_completion_threshold tgt_job_nonpreemptive_after_run_to_completion_threshold.
  Proof.
    frtc_prefix.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros uR uL Hu.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Hu)|].
    apply ar_imp_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _ (RTCT j)
        (pp_service_related Job PStateR PStateL R schedR schedL Hsched j _ _ Ht))|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (pp_completed_by_related Job costR costL Hcost PStateR PStateL R schedR schedL Hsched j _ _ Hu)))|].
    exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j _ _ Hu)).
  Qed.
End Rtc.
