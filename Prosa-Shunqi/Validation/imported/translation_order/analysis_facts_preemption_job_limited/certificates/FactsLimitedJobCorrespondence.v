From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsLimitedJobSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsLimitedJob ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  LimitedPreemptiveCorrespondence ScheduleLimitedPreemptiveCorrespondence.

Module I := ImportedFactsLimitedJob.
Module S := FactsLimitedJobSemanticSource.FactsLimitedJobSemanticSource.
Module LP := LimitedPreemptiveSemanticSource.LimitedPreemptiveSemanticSource.
Module L := prosa.util.list.ListSemanticSource.

(** Statement correspondences for [analysis/facts/preemption/job/limited.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (the job type, the cost and preemption-point
    classes, the arrival sequence and, for the last statement, the processor
    state type and the schedule); target side: the imported Lean theorem
    types.  Inputs: [job_cost] by the accepted [SvcJobCostRel], the
    preemption points by the accepted [LpJobPreemptionPointsRel], arrival
    sequences by [ArArrivalSequenceRel], processor states by the accepted
    two-sided [SvcProcessorStateRel] and schedules by [SvcScheduleRel]; jobs
    identity, Nats by [SubNatRel].  The section-local instance
    [limited_preemptive_job_model] is related by the accepted
    [lp_limited_preemptive_job_model_related]; membership, [last0], [size],
    [nth], nondecreasing sequences and the valid limited-preemptive model by
    the accepted limited-preemptive certificate; [distances], [max0],
    [filter], [job_preemption_points] and the valid preemption model by the
    accepted preemption-parameter certificate; the schedule's respect of the
    preemption model by the accepted limited-preemptive schedule certificate.
    [first0] is related here by structural recursion on the converted list.
    No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma flj_first0_canonical (xs : seq nat) :
  SubNatRel (L.first0 xs) (I.Prosa_Util_List_first0 (svc_nat_list_to_imported xs)).
Proof.
  destruct xs as [|x xs]; cbn; exact (@Lean.eq_refl _ _).
Qed.

Lemma flj_first0_related xsR xsL :
  SvcNatListRel xsR xsL -> SubNatRel (L.first0 xsR) (I.Prosa_Util_List_first0 xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _ (flj_first0_canonical xsR)
    (sub_imported_eq_congr I.Prosa_Util_List_first0 _ _ Hxs)).
Qed.

Section Limited.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable ppR : LP.JobPreemptionPoints Job.
  Variable ppL : I.Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job dJ.
  Hypothesis Hpp : LpJobPreemptionPointsRel Job ppR ppL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let jpR := @LP.limited_preemptive_job_model Job ppR.
  Let jpL := I.Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job dJ ppL.
  Let Hjp : PpJobPreemptableRel Job jpR jpL :=
    fun j nR nL Hn => lp_limited_preemptive_job_model_related Job ppR ppL Hpp j nR nL Hn.
  Let VLP := valid_limited_preemptions_job_model_correspondence Job costR costL Hcost ppR ppL Hpp
    arrR arrL Harr.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Definition src_zero_in_preemption_points : Prop :=
    ltac:(body_of (fun s : S.statement_zero_in_preemption_points => s Job costR ppR arrR)).
  Definition tgt_zero_in_preemption_points : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_Job_Limited_zero_in_preemption_points
      Job dJ costL ppL arrL)).

  Theorem zero_in_preemption_points_correspondence :
    PropSPropRel src_zero_in_preemption_points tgt_zero_in_preemption_points.
  Proof.
    unfold src_zero_in_preemption_points, tgt_zero_in_preemption_points. (imp VLP; apply
      ar_forall_identity_correspondence => j; imp (arrives_in_correspondence_certificate Job arrR arrL j
      Harr)).
    exact (ar_bool_truth_correspondence _ _
      (lp_mem_bool_related _ _ _ _ (sub_nat_rel_canonical O) (Hpp j))).
  Qed.

  Definition src_zero_is_first_element : Prop :=
    ltac:(body_of (fun s : S.statement_zero_is_first_element => s Job costR ppR arrR)).
  Definition tgt_zero_is_first_element : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_Job_Limited_zero_is_first_element
      Job dJ costL ppL arrL)).

  Theorem zero_is_first_element_correspondence :
    PropSPropRel src_zero_is_first_element tgt_zero_is_first_element.
  Proof.
    unfold src_zero_is_first_element, tgt_zero_is_first_element. (imp VLP; apply
      ar_forall_identity_correspondence => j; imp (arrives_in_correspondence_certificate Job arrR arrL j
      Harr)).
    exact (sub_nat_eq_correspondence _ _ _ _ (flj_first0_related _ _ (Hpp j)) (sub_nat_rel_canonical O)).
  Qed.

  Definition src_list_of_preemption_point_is_not_empty : Prop :=
    ltac:(body_of (fun s : S.statement_list_of_preemption_point_is_not_empty => s Job costR ppR arrR)).
  Definition tgt_list_of_preemption_point_is_not_empty : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_Job_Limited_list_of_preemption_point_is_not_empty
        Job dJ costL ppL arrL)).

  Theorem list_of_preemption_point_is_not_empty_correspondence :
    PropSPropRel src_list_of_preemption_point_is_not_empty tgt_list_of_preemption_point_is_not_empty.
  Proof.
    unfold src_list_of_preemption_point_is_not_empty, tgt_list_of_preemption_point_is_not_empty. (imp
      VLP; apply ar_forall_identity_correspondence => j; imp (arrives_in_correspondence_certificate Job
      arrR arrL j Harr)).
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (lp_length_related _ _ (Hpp j))).
  Qed.

  Definition src_job_cost_in_nonpreemptive_points : Prop :=
    ltac:(body_of (fun s : S.statement_job_cost_in_nonpreemptive_points => s Job costR ppR arrR)).
  Definition tgt_job_cost_in_nonpreemptive_points : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_Job_Limited_job_cost_in_nonpreemptive_points
        Job dJ costL ppL arrL)).

  Theorem job_cost_in_nonpreemptive_points_correspondence :
    PropSPropRel src_job_cost_in_nonpreemptive_points tgt_job_cost_in_nonpreemptive_points.
  Proof.
    unfold src_job_cost_in_nonpreemptive_points, tgt_job_cost_in_nonpreemptive_points. (imp VLP; apply
      ar_forall_identity_correspondence => j; imp (arrives_in_correspondence_certificate Job arrR arrL j
      Harr)).
    exact (ar_bool_truth_correspondence _ _ (lp_mem_bool_related _ _ _ _ (Hcost j) (Hpp j))).
  Qed.

  Lemma flj_job_cost_positive_related (j : Job) :
    ArBoolRel (@prosa.model.job.properties.job_cost_positive Job costR j)
      (I.Prosa_Model_Job_Properties_job_cost_positive Job dJ costL j).
  Proof.
    unfold prosa.model.job.properties.job_cost_positive.
    cbn [I.Prosa_Model_Job_Properties_job_cost_positive].
    exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost j)).
  Qed.

  Definition src_number_of_preemption_points_at_least_two : Prop :=
    ltac:(body_of (fun s : S.statement_number_of_preemption_points_at_least_two =>
      s Job costR ppR arrR)).
  Definition tgt_number_of_preemption_points_at_least_two : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_Job_Limited_number_of_preemption_points_at_least_two
        Job dJ costL ppL arrL)).

  Theorem number_of_preemption_points_at_least_two_correspondence :
    PropSPropRel src_number_of_preemption_points_at_least_two
      tgt_number_of_preemption_points_at_least_two.
  Proof.
    unfold src_number_of_preemption_points_at_least_two, tgt_number_of_preemption_points_at_least_two.
    (imp VLP; apply ar_forall_identity_correspondence => j; imp (arrives_in_correspondence_certificate
      Job arrR arrL j Harr)). imp (ar_bool_truth_correspondence _ _ (flj_job_cost_positive_related j)).
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 1) (lp_length_related _ _ (Hpp j))).
  Qed.


  Definition src_antidensity_of_preemption_points : Prop :=
    ltac:(body_of (fun s : S.statement_antidensity_of_preemption_points => s Job costR ppR arrR)).
  Definition tgt_antidensity_of_preemption_points : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_Job_Limited_antidensity_of_preemption_points
        Job dJ costL ppL arrL)).

  Theorem antidensity_of_preemption_points_correspondence :
    PropSPropRel src_antidensity_of_preemption_points tgt_antidensity_of_preemption_points.
  Proof.
    unfold src_antidensity_of_preemption_points, tgt_antidensity_of_preemption_points. ((imp VLP; apply
      ar_forall_identity_correspondence => j; imp (arrives_in_correspondence_certificate Job arrR arrL j
      Harr)); apply ar_forall_nat_correspondence => rR rL Hr; imp (sub_nat_le_correspondence _ _ _ _ Hr
      (Hcost j)); imp (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (lp_mem_bool_related _
      _ _ _ Hr (Hpp j))))).
    exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_le_related _ _ _ _ (flj_first0_related _ _ (Hpp j)) Hr)
      (ar_decide_lt_related _ _ _ _ Hr (lp_last0_related _ _ (Hpp j))))).
  Qed.

  Definition src_work_belongs_to_some_nonpreemptive_segment : Prop :=
    ltac:(body_of (fun s : S.statement_work_belongs_to_some_nonpreemptive_segment =>
      s Job costR ppR arrR)).
  Definition tgt_work_belongs_to_some_nonpreemptive_segment : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_Job_Limited_work_belongs_to_some_nonpreemptive_segment
        Job dJ costL ppL arrL)).

  Theorem work_belongs_to_some_nonpreemptive_segment_correspondence :
    PropSPropRel src_work_belongs_to_some_nonpreemptive_segment
      tgt_work_belongs_to_some_nonpreemptive_segment.
  Proof.
    unfold src_work_belongs_to_some_nonpreemptive_segment,
      tgt_work_belongs_to_some_nonpreemptive_segment. ((imp VLP; apply ar_forall_identity_correspondence
        => j; imp (arrives_in_correspondence_certificate Job arrR arrL j Harr)); apply
        ar_forall_nat_correspondence => rR rL Hr; imp (sub_nat_le_correspondence _ _ _ _ Hr (Hcost j));
        imp (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (lp_mem_bool_related _ _ _ _ Hr
        (Hpp j))))).
    apply ar_exists_nat_correspondence => nR nL Hn.
    have Hn1 := pp_succ_related nR nL Hn.
    apply ar_and_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ Hn1 (lp_length_related _ _ (Hpp j)))|].
    exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_lt_related _ _ _ _ (lp_nthD_related _ _ _ _ (Hpp j) Hn) Hr)
      (ar_decide_lt_related _ _ _ _ Hr (lp_nthD_related _ _ _ _ (Hpp j) Hn1)))).
  Qed.

  Let PPTS j := job_preemption_points_correspondence Job costR costL Hcost jpR jpL Hjp j.

  Definition src_job_parameters_last_np_to_job_limited : Prop :=
    ltac:(body_of (fun s : S.statement_job_parameters_last_np_to_job_limited => s Job costR ppR arrR)).
  Definition tgt_job_parameters_last_np_to_job_limited : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_Job_Limited_job_parameters_last_np_to_job_limited
        Job dJ costL ppL arrL)).

  Theorem job_parameters_last_np_to_job_limited_correspondence :
    PropSPropRel src_job_parameters_last_np_to_job_limited tgt_job_parameters_last_np_to_job_limited.
  Proof.
    unfold src_job_parameters_last_np_to_job_limited, tgt_job_parameters_last_np_to_job_limited. (imp
      VLP; apply ar_forall_identity_correspondence => j; imp (arrives_in_correspondence_certificate Job
      arrR arrL j Harr)).
    exact (sub_nat_eq_correspondence _ _ _ _
      (pp_last0_related _ _ (pp_distances_related _ _ (PPTS j)))
      (pp_last0_related _ _ (pp_filter_related _ _
        (fun nR nL Hn => svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) Hn) _ _
        (pp_distances_related _ _ (Hpp j))))).
  Qed.

  Definition src_job_parameters_max_np_to_job_limited : Prop :=
    ltac:(body_of (fun s : S.statement_job_parameters_max_np_to_job_limited => s Job costR ppR arrR)).
  Definition tgt_job_parameters_max_np_to_job_limited : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_Job_Limited_job_parameters_max_np_to_job_limited
        Job dJ costL ppL arrL)).

  Theorem job_parameters_max_np_to_job_limited_correspondence :
    PropSPropRel src_job_parameters_max_np_to_job_limited tgt_job_parameters_max_np_to_job_limited.
  Proof.
    unfold src_job_parameters_max_np_to_job_limited, tgt_job_parameters_max_np_to_job_limited. (imp VLP;
      apply ar_forall_identity_correspondence => j; imp (arrives_in_correspondence_certificate Job arrR
      arrL j Harr)).
    exact (sub_nat_eq_correspondence _ _ _ _
      (pp_max0_related _ _ (pp_distances_related _ _ (PPTS j)))
      (pp_max0_related _ _ (pp_distances_related _ _ (Hpp j)))).
  Qed.

  Section Sched.
    Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
    Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
    Variable R : SvcProcessorStateRel Job PStateR PStateL.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Definition src_valid_fixed_preemption_points_model_lemma : Prop :=
      ltac:(body_of (fun s : S.statement_valid_fixed_preemption_points_model_lemma =>
        s Job costR ppR arrR PStateR schedR)).
    Definition tgt_valid_fixed_preemption_points_model_lemma : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_Preemption_Job_Limited_valid_fixed_preemption_points_model_lemma
          Job dJ costL ppL arrL PStateL schedL)).

    Theorem valid_fixed_preemption_points_model_lemma_correspondence :
      PropSPropRel src_valid_fixed_preemption_points_model_lemma
        tgt_valid_fixed_preemption_points_model_lemma.
    Proof.
      unfold src_valid_fixed_preemption_points_model_lemma,
        tgt_valid_fixed_preemption_points_model_lemma.
      imp (schedule_respects_preemption_model_correspondence Job jpR jpL Hjp PStateR PStateL R
        schedR schedL Hsched arrR arrL Harr).
      imp VLP.
      exact (valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp PStateR PStateL R
        schedR schedL Hsched arrR arrL Harr).
    Qed.
  End Sched.
End Limited.
