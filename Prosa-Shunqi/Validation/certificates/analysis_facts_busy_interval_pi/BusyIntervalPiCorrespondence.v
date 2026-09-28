From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import BusyIntervalPiSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes model.job.properties analysis.definitions.work_bearing_readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBusyIntervalPi ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers
  TaskPreemptionParametersCorrespondence.

Module I := ImportedBusyIntervalPi.
Module S := BusyIntervalPiSemanticSource.BusyIntervalPiSemanticSource.
Module TPS := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module PPS := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module PIS := PriorityInversionSemanticSource.PriorityInversionSemanticSource.

(** Correspondence for [analysis/facts/busy_interval/pi.v].

    Source side: the extracted definition block [max_lp_nonpreemptive_segment]
    and the extracted statements [S.statement_X] specialised at their leading
    inputs (task and job types, job-task, arrival and cost classes, arrival
    sequence); target side: the compiled Lean definition and the imported
    Lean theorem types.  Inputs: [job_arrival] by [ArJobArrivalRel],
    [job_cost] by the accepted [SvcJobCostRel], [job_task] by [Lean.eq],
    arrival sequences by [ArArrivalSequenceRel].  Inputs quantified inside a
    statement are covered in both directions by the accepted conversions:
    processor models ([isj_cover_pstate]), schedules through the
    processor-model relation ([fpre_forall_sched]), JLFP policies
    ([fpre_forall_jlfp]), [JobPreemptable] instances ([fpre_forall_jp]),
    [TaskMaxNonpreemptiveSegment] instances (the accepted two-way totals of
    [TppMaxSegmentRel]), the readiness instance on the statement's schedule
    pair ([fpre_forall_jr]), jobs (identity) and instants.  The conditional
    maximum is related to [bigMaxListCond] through its kernel-checked
    constructor equations (replaying the accepted blocking-bound
    certificate).  Busy prefixes, quiet times, priority inversion and its
    cumulative sum are the accepted busy-interval-existence helpers;
    preemption times, schedule validity, preemption-model validity and the
    JLFP-at-preemption-point policy are the accepted preemption-facts helpers;
    the bounded-nonpreemptive-segment model is the accepted
    task-preemption-parameters certificate (its preemption-model part
    through the preemption-facts helper).  No source or target theorem is
    used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section BigMax.
  Context (X : Type).
  Variable PR : X -> bool.
  Variable PL : X -> I.Bool.
  Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).
  Variable FR : X -> nat.
  Variable FL : X -> Lean.Nat.
  Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

  (** Replayed from the accepted blocking-bound certificate. *)
  Lemma bpi_bigmax_canonical (xs : seq X) :
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
          (sub_imported_eq_sym _ _ (pp_max_canonical (FR x) (\max_(y <- xs | PR y) FR y))) _).
        exact (sub_imported_eq_congr2 I.Nat_max _ _ _ _ (HF x) IH).
      + refine (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
          (I.Prosa_Validation_PiInterface_production_bigMaxListCond_cons_false
            X PL FL x (ar_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
  Qed.

  Lemma bpi_bigmax_related (xsR : seq X) (xsL : I.List X) :
    ArListRel xsR xsL ->
    SubNatRel (\max_(x <- xsR | PR x) FR x) (I.Prosa_Util_Minmax_bigMaxListCond X xsL PL FL).
  Proof.
    intro Hxs.
    exact (sub_imported_eq_trans _ _ _ (bpi_bigmax_canonical xsR)
      (sub_imported_eq_congr (fun l => I.Prosa_Util_Minmax_bigMaxListCond X l PL FL) _ _ Hxs)).
  Qed.
End BigMax.

Lemma bpi_forall_tms (Task : eqType)
    (PRm : TPS.TaskMaxNonpreemptiveSegment Task -> Prop)
    (PLm : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task (ar_decidable_eq Task)
      -> SProp) :
  (forall mR mL, TppMaxSegmentRel Task mR mL -> PropSPropRel (PRm mR) (PLm mL)) ->
  PropSPropRel (forall m, PRm m) (forall m, PLm m).
Proof.
  exact (isj_forall_cover_sprop _ _ (TppMaxSegmentRel Task)
    (fun cR => I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_mk Task
      (ar_decidable_eq Task) (fun tsk => sub_nat_to_imported (@TPS.task_max_nonpreemptive_segment Task
        cR tsk)))
    (fun cL => ((fun tsk => sub_nat_to_rocq
      (I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment
        Task (ar_decidable_eq Task) cL tsk)) : TPS.TaskMaxNonpreemptiveSegment Task))
    (TaskMaxNonpreemptiveSegment_source_total Task) (TaskMaxNonpreemptiveSegment_target_total Task)
    PRm PLm).
Qed.

Section BusyIntervalPi.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  (** ** The definition *)

  Theorem max_lp_nonpreemptive_segment_correspondence pR pL (Hp : FpreJLFPRel Job pR pL)
      jpR jpL (Hjp : PpJobPreemptableRel Job jpR jpL) (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@S.max_lp_nonpreemptive_segment Job costR arrR pR jpR j tR)
      (I.Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment Job dJ costL arrL pL jpL j tL).
  Proof.
    intro Ht. unfold S.max_lp_nonpreemptive_segment.
    cbn [I.Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment].
    apply bpi_bigmax_related.
    - intro x. exact (ar_bool_and_related _ _ _ _ (svc_bool_not_related _ _ (Hp x j))
        (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost x))).
    - intro x. exact (svc_target_sub_related _ _ _ _
        (job_max_nonpreemptive_segment_correspondence Job costR costL Hcost jpR jpL Hjp x)
        (sub_nat_rel_canonical 1)).
    - exact (arrivals_before_correspondence_certificate Job arrR arrL Harr _ _ Ht).
  Qed.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].
  Local Ltac M_va := imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
  Local Ltac M_ps := apply (isj_cover_pstate Job); intros PR PL X.
  Local Ltac M_jlfp := apply fpre_forall_jlfp; intros pR pL Hp.
  Local Ltac M_jp := apply fpre_forall_jp; intros jpR jpL Hjp.

  Definition src_lower_priority_job_scheduled_implies_no_preemption_time : Prop :=
    ltac:(body_of (fun s : S.statement_lower_priority_job_scheduled_implies_no_preemption_time =>
      s Job jaR costR arrR)).
  Definition tgt_lower_priority_job_scheduled_implies_no_preemption_time : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_Pi_lower_priority_job_scheduled_implies_no_preemption_time
      Job dJ jaL costL arrL)).

  Theorem lower_priority_job_scheduled_implies_no_preemption_time_correspondence :
    PropSPropRel src_lower_priority_job_scheduled_implies_no_preemption_time
      tgt_lower_priority_job_scheduled_implies_no_preemption_time.
  Proof.
    unfold src_lower_priority_job_scheduled_implies_no_preemption_time,
      tgt_lower_priority_job_scheduled_implies_no_preemption_time.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (hap_transitive_rel Job pR pL Hp); M_jp; imp
      (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL
      Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL
      Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
      Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply ar_forall_identity_correspondence; intro
      j; imp (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp
      (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j)); (apply
      ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_forall_nat_correspondence; intros t2R
      t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
      arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))). (apply ar_forall_identity_correspondence; intro
      jlp; imp (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hp jlp j))); apply
      ar_forall_nat_correspondence; intros tR tL Ht; imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _
      Ht Ht2))); imp (ar_bool_truth_correspondence _ _ (fpre_scheduled_at_related Job PR PL X sR sL Hs
      jlp _ _ Ht))).
    apply ar_forall_nat_correspondence. intros uR uL Hu.
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1
      Hu) (ar_decide_le_related _ _ _ _ Hu Ht))). exact (ar_bool_truth_correspondence _ _
      (svc_bool_not_related _ _ (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL Harr jpR
      jpL Hjp _ _ Hu))).
  Qed.

  Definition src_lower_priority_job_continuously_scheduled : Prop :=
    ltac:(body_of (fun s : S.statement_lower_priority_job_continuously_scheduled => s Job jaR costR arrR)).
  Definition tgt_lower_priority_job_continuously_scheduled : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_lower_priority_job_continuously_scheduled
      Job dJ jaL costL arrL)).

  Theorem lower_priority_job_continuously_scheduled_correspondence :
    PropSPropRel src_lower_priority_job_continuously_scheduled tgt_lower_priority_job_continuously_scheduled.
  Proof.
    unfold src_lower_priority_job_continuously_scheduled, tgt_lower_priority_job_continuously_scheduled.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (hap_transitive_rel Job pR pL Hp); M_jp; imp
      (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL
      Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL
      Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
      Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply ar_forall_identity_correspondence; intro
      j; imp (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp
      (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j)); (apply
      ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_forall_nat_correspondence; intros t2R
      t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
      arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))). (apply ar_forall_identity_correspondence; intro
      jlp; imp (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hp jlp j))); apply
      ar_forall_nat_correspondence; intros tR tL Ht; imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _
      Ht Ht2))); imp (ar_bool_truth_correspondence _ _ (fpre_scheduled_at_related Job PR PL X sR sL Hs
      jlp _ _ Ht))).
    apply ar_forall_nat_correspondence. intros uR uL Hu.
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1
      Hu) (ar_decide_le_related _ _ _ _ Hu Ht))). exact (ar_bool_truth_correspondence _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs jlp _ _ Hu)).
  Qed.

  Definition src_low_priority_job_arrives_before_busy_interval_prefix : Prop :=
    ltac:(body_of (fun s : S.statement_low_priority_job_arrives_before_busy_interval_prefix =>
      s Job jaR costR arrR)).
  Definition tgt_low_priority_job_arrives_before_busy_interval_prefix : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_Pi_low_priority_job_arrives_before_busy_interval_prefix
      Job dJ jaL costL arrL)).

  Theorem low_priority_job_arrives_before_busy_interval_prefix_correspondence :
    PropSPropRel src_low_priority_job_arrives_before_busy_interval_prefix
      tgt_low_priority_job_arrives_before_busy_interval_prefix.
  Proof.
    unfold src_low_priority_job_arrives_before_busy_interval_prefix,
      tgt_low_priority_job_arrives_before_busy_interval_prefix.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (hap_transitive_rel Job pR pL Hp); M_jp; imp
      (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL
      Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL
      Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
      Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply ar_forall_identity_correspondence; intro
      j; imp (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp
      (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j)); (apply
      ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_forall_nat_correspondence; intros t2R
      t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
      arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))). (apply ar_forall_identity_correspondence; intro
      jlp; imp (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hp jlp j))); apply
      ar_forall_nat_correspondence; intros tR tL Ht; imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _
      Ht Ht2))); imp (ar_bool_truth_correspondence _ _ (fpre_scheduled_at_related Job PR PL X sR sL Hs
      jlp _ _ Ht))).
    exact (sub_nat_lt_correspondence _ _ _ _ (Hja jlp) Ht1).
  Qed.

  Definition src_low_priority_job_scheduled_before_busy_interval_prefix : Prop :=
    ltac:(body_of (fun s : S.statement_low_priority_job_scheduled_before_busy_interval_prefix =>
      s Job jaR costR arrR)).
  Definition tgt_low_priority_job_scheduled_before_busy_interval_prefix : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_Pi_low_priority_job_scheduled_before_busy_interval_prefix
      Job dJ jaL costL arrL)).

  Theorem low_priority_job_scheduled_before_busy_interval_prefix_correspondence :
    PropSPropRel src_low_priority_job_scheduled_before_busy_interval_prefix
      tgt_low_priority_job_scheduled_before_busy_interval_prefix.
  Proof.
    unfold src_low_priority_job_scheduled_before_busy_interval_prefix,
      tgt_low_priority_job_scheduled_before_busy_interval_prefix.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (hap_transitive_rel Job pR pL Hp); M_jp; imp
      (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL
      Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL
      Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
      Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply ar_forall_identity_correspondence; intro
      j; imp (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp
      (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j)); (apply
      ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_forall_nat_correspondence; intros t2R
      t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
      arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))). (apply ar_forall_identity_correspondence; intro
      jlp; imp (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hp jlp j))); apply
      ar_forall_nat_correspondence; intros tR tL Ht; imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _
      Ht Ht2))); imp (ar_bool_truth_correspondence _ _ (fpre_scheduled_at_related Job PR PL X sR sL Hs
      jlp _ _ Ht))).
    apply ar_exists_nat_correspondence. intros uR uL Hu.
    apply ar_and_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Hu Ht1)|].
    exact (ar_bool_truth_correspondence _ _ (fpre_scheduled_at_related Job PR PL X sR sL Hs jlp _ _ Hu)).
  Qed.

  Definition src_lp_job_should_arrive_early_for_pi : Prop :=
    ltac:(body_of (fun s : S.statement_lp_job_should_arrive_early_for_pi => s Job jaR costR arrR)).
  Definition tgt_lp_job_should_arrive_early_for_pi : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_lp_job_should_arrive_early_for_pi
      Job dJ jaL costL arrL)).

  Theorem lp_job_should_arrive_early_for_pi_correspondence :
    PropSPropRel src_lp_job_should_arrive_early_for_pi tgt_lp_job_should_arrive_early_for_pi.
  Proof.
    unfold src_lp_job_should_arrive_early_for_pi, tgt_lp_job_should_arrive_early_for_pi.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (hap_transitive_rel Job pR pL Hp); M_jp; imp
      (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL
      Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL
      Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
      Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply ar_forall_identity_correspondence; intro
      j; imp (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp
      (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j)); (apply
      ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_forall_nat_correspondence; intros t2R
      t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
      arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))).
    apply ar_forall_identity_correspondence. intro jlp. imp (ar_bool_truth_correspondence _ _
      (svc_bool_not_related _ _ (Hp jlp j))).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros aR aL Ha.
    imp (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Job jlp _ _
      (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht1 Ha))).
    imp (sub_nat_le_correspondence _ _ _ _ Ha Ht2).
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1
      Ht) (ar_decide_lt_related _ _ _ _ Ht Ha))).
    exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs jlp _ _ Ht))).
  Qed.

  Definition src_lower_priority_jobs_never_scheduled_if_no_inversion : Prop :=
    ltac:(body_of (fun s : S.statement_lower_priority_jobs_never_scheduled_if_no_inversion =>
      s Job jaR costR arrR)).
  Definition tgt_lower_priority_jobs_never_scheduled_if_no_inversion : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_Pi_lower_priority_jobs_never_scheduled_if_no_inversion
      Job dJ jaL costL arrL)).

  Theorem lower_priority_jobs_never_scheduled_if_no_inversion_correspondence :
    PropSPropRel src_lower_priority_jobs_never_scheduled_if_no_inversion
      tgt_lower_priority_jobs_never_scheduled_if_no_inversion.
  Proof.
    unfold src_lower_priority_jobs_never_scheduled_if_no_inversion,
      tgt_lower_priority_jobs_never_scheduled_if_no_inversion.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (fpre_reflexive_rel Job pR pL Hp); imp (hap_transitive_rel Job
      pR pL Hp); M_jp; imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR
      arrL Harr jpR jpL Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL
      Hs); intros jrR jrL Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X
      sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply
      ar_forall_identity_correspondence; intro j; imp (arrives_in_correspondence_certificate Job arrR
      arrL j Harr); imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL
      Hcost j)); (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))).
    apply ar_forall_identity_correspondence. intro jlp. imp (ar_bool_truth_correspondence _ _
      (svc_bool_not_related _ _ (Hp jlp j))).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1
      Ht) (ar_decide_lt_related _ _ _ _ Ht Ht2))).
    imp (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ ((ex_priority_inversion_related Job
      PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht1)))).
    exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs jlp _ _ Ht))).
  Qed.


  Definition src_no_preemption_time_before_pi : Prop :=
    ltac:(body_of (fun s : S.statement_no_preemption_time_before_pi => s Job jaR costR arrR)).
  Definition tgt_no_preemption_time_before_pi : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_no_preemption_time_before_pi
      Job dJ jaL costL arrL)).

  Theorem no_preemption_time_before_pi_correspondence :
    PropSPropRel src_no_preemption_time_before_pi tgt_no_preemption_time_before_pi.
  Proof.
    unfold src_no_preemption_time_before_pi, tgt_no_preemption_time_before_pi.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (fpre_reflexive_rel Job pR pL Hp); imp (hap_transitive_rel Job
      pR pL Hp); M_jp; imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR
      arrL Harr jpR jpL Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL
      Hs); intros jrR jrL Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X
      sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply
      ar_forall_identity_correspondence; intro j; imp (arrives_in_correspondence_certificate Job arrR
      arrL j Harr); imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL
      Hcost j)); (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))). (apply
      ar_forall_nat_correspondence; intros pR' pL' Hpi; imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Hpi) (ar_decide_lt_related _ _ _ _
      Hpi Ht2))); imp (ar_bool_truth_correspondence _ _ ((ex_priority_inversion_related Job PR PL X sR
      sL Hs arrR arrL Harr pR pL Hp j _ _ Hpi)))).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1
      Ht) (ar_decide_le_related _ _ _ _ Ht Hpi))). exact (ar_bool_truth_correspondence _ _
      (svc_bool_not_related _ _ (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL Harr jpR
      jpL Hjp _ _ Ht))).
  Qed.

  Definition src_pi_job_remains_scheduled : Prop :=
    ltac:(body_of (fun s : S.statement_pi_job_remains_scheduled => s Job jaR costR arrR)).
  Definition tgt_pi_job_remains_scheduled : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_pi_job_remains_scheduled
      Job dJ jaL costL arrL)).

  Theorem pi_job_remains_scheduled_correspondence :
    PropSPropRel src_pi_job_remains_scheduled tgt_pi_job_remains_scheduled.
  Proof.
    unfold src_pi_job_remains_scheduled, tgt_pi_job_remains_scheduled.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (fpre_reflexive_rel Job pR pL Hp); imp (hap_transitive_rel Job
      pR pL Hp); M_jp; imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR
      arrL Harr jpR jpL Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL
      Hs); intros jrR jrL Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X
      sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply
      ar_forall_identity_correspondence; intro j; imp (arrives_in_correspondence_certificate Job arrR
      arrL j Harr); imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL
      Hcost j)); (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))). (apply
      ar_forall_nat_correspondence; intros pR' pL' Hpi; imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Hpi) (ar_decide_lt_related _ _ _ _
      Hpi Ht2))); imp (ar_bool_truth_correspondence _ _ ((ex_priority_inversion_related Job PR PL X sR
      sL Hs arrR arrL Harr pR pL Hp j _ _ Hpi)))).
    apply ar_forall_identity_correspondence. intro jlp. imp (ar_bool_truth_correspondence _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs jlp _ _ Hpi)).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1
      Ht) (ar_decide_le_related _ _ _ _ Ht Hpi))). exact (ar_bool_truth_correspondence _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs jlp _ _ Ht)).
  Qed.

  Definition src_pi_continuous : Prop :=
    ltac:(body_of (fun s : S.statement_pi_continuous => s Job jaR costR arrR)).
  Definition tgt_pi_continuous : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_pi_continuous Job dJ jaL costL arrL)).

  Theorem pi_continuous_correspondence : PropSPropRel src_pi_continuous tgt_pi_continuous.
  Proof.
    unfold src_pi_continuous, tgt_pi_continuous.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (fpre_reflexive_rel Job pR pL Hp); imp (hap_transitive_rel Job
      pR pL Hp); M_jp; imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR
      arrL Harr jpR jpL Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL
      Hs); intros jrR jrL Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X
      sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply
      ar_forall_identity_correspondence; intro j; imp (arrives_in_correspondence_certificate Job arrR
      arrL j Harr); imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL
      Hcost j)); (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))). (apply
      ar_forall_nat_correspondence; intros pR' pL' Hpi; imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Hpi) (ar_decide_lt_related _ _ _ _
      Hpi Ht2))); imp (ar_bool_truth_correspondence _ _ ((ex_priority_inversion_related Job PR PL X sR
      sL Hs arrR arrL Harr pR pL Hp j _ _ Hpi)))).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1
      Ht) (ar_decide_le_related _ _ _ _ Ht Hpi))).
    exact (ar_bool_truth_correspondence _ _ ((ex_priority_inversion_related Job PR PL X sR sL Hs arrR
      arrL Harr pR pL Hp j _ _ Ht))).
  Qed.

  Definition src_only_one_pi_job : Prop :=
    ltac:(body_of (fun s : S.statement_only_one_pi_job => s Job jaR costR arrR)).
  Definition tgt_only_one_pi_job : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_only_one_pi_job Job dJ jaL costL arrL)).

  Theorem only_one_pi_job_correspondence : PropSPropRel src_only_one_pi_job tgt_only_one_pi_job.
  Proof.
    unfold src_only_one_pi_job, tgt_only_one_pi_job.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (fpre_reflexive_rel Job pR pL Hp); imp (hap_transitive_rel Job
      pR pL Hp); M_jp; imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR
      arrL Harr jpR jpL Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL
      Hs); intros jrR jrL Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X
      sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply
      ar_forall_identity_correspondence; intro j; imp (arrives_in_correspondence_certificate Job arrR
      arrL j Harr); imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL
      Hcost j)); (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))).
    apply ar_forall_nat_correspondence. intros s1R s1L Hs1. imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Hs1) (ar_decide_lt_related _ _ _ _
      Hs1 Ht2))).
    apply ar_forall_identity_correspondence. intro j1. imp (ar_bool_truth_correspondence _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs j1 _ _ Hs1)). imp (ar_bool_truth_correspondence _
      _ (svc_bool_not_related _ _ (Hp j1 j))).
    apply ar_forall_nat_correspondence. intros s2R s2L Hs2. imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Hs2) (ar_decide_lt_related _ _ _ _
      Hs2 Ht2))).
    apply ar_forall_identity_correspondence. intro j2. imp (ar_bool_truth_correspondence _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs j2 _ _ Hs2)). imp (ar_bool_truth_correspondence _
      _ (svc_bool_not_related _ _ (Hp j2 j))).
    exact (isj_eq_identity_correspondence Job j1 j2).
  Qed.

  Definition src_busy_interval_pi_cases : Prop :=
    ltac:(body_of (fun s : S.statement_busy_interval_pi_cases => s Job jaR costR arrR)).
  Definition tgt_busy_interval_pi_cases : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_busy_interval_pi_cases Job dJ jaL costL
      arrL)).

  Theorem busy_interval_pi_cases_correspondence :
    PropSPropRel src_busy_interval_pi_cases tgt_busy_interval_pi_cases.
  Proof.
    unfold src_busy_interval_pi_cases, tgt_busy_interval_pi_cases.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (fpre_reflexive_rel Job pR pL Hp); imp (hap_transitive_rel Job
      pR pL Hp); M_jp; imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR
      arrL Harr jpR jpL Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL
      Hs); intros jrR jrL Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X
      sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply
      ar_forall_identity_correspondence; intro j; imp (arrives_in_correspondence_certificate Job arrR
      arrL j Harr); imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL
      Hcost j)); (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))).
    apply fpre_or_correspondence.
    - exact (sub_nat_eq_correspondence _ _ _ _
        (ex_cumulative_priority_inversion_related Job PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _
          Ht1 Ht2) (sub_nat_rel_canonical O)).
    - exact (ar_bool_truth_correspondence _ _ ((ex_priority_inversion_related Job PR PL X sR sL Hs arrR
      arrL Harr pR pL Hp j _ _ Ht1))).
  Qed.

  Section Tasks.
    Context (Task : eqType).
    Let dT := ar_decidable_eq Task.
    Variable jtR : prosa.model.task.concept.JobTask Job Task.
    Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
    Hypothesis Hjt : forall j : Job,
      Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).


    Definition src_max_np_job_segment_bounded_by_max_np_task_segment : Prop :=
      ltac:(body_of (fun s : S.statement_max_np_job_segment_bounded_by_max_np_task_segment =>
        s Task Job jtR costR arrR)).
    Definition tgt_max_np_job_segment_bounded_by_max_np_task_segment : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_BusyInterval_Pi_max_np_job_segment_bounded_by_max_np_task_segment
        Job dJ Task dT jtL costL arrL)).

    Theorem max_np_job_segment_bounded_by_max_np_task_segment_correspondence :
      PropSPropRel src_max_np_job_segment_bounded_by_max_np_task_segment
        tgt_max_np_job_segment_bounded_by_max_np_task_segment.
    Proof.
      unfold src_max_np_job_segment_bounded_by_max_np_task_segment,
        tgt_max_np_job_segment_bounded_by_max_np_task_segment.
      M_ps. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). M_jlfp. (apply (bpi_forall_tms
        Task); intros mR mL Hm). M_jp.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      imp (ar_and_correspondence _ _ _ _ (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X
        sR sL Hs arrR arrL Harr jpR jpL Hjp) (model_with_bounded_nonpreemptive_segments_correspondence
        Task Job jtR jtL Hjt costR costL Hcost mR mL Hm jpR jpL Hjp arrR arrL Harr)).
      apply sub_nat_le_correspondence; [exact (max_lp_nonpreemptive_segment_correspondence pR pL Hp jpR
        jpL Hjp j _ _ Ht1)|].
      apply bpi_bigmax_related.
      - intro x. exact (ar_bool_and_related _ _ _ _ (svc_bool_not_related _ _ (Hp x j))
          (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost x))).
      - intro x. exact (svc_target_sub_related _ _ _ _
          (sub_imported_eq_trans _ _ _ (Hm _)
            (sub_imported_eq_congr
              (I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment
                Task dT mL) _ _ (Hjt x)))
          (sub_nat_rel_canonical 1)).
      - exact (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _
          (sub_nat_rel_canonical O) Ht1).
    Qed.

    Definition src_preemption_time_exists_case1 : Prop :=
      ltac:(body_of (fun s : S.statement_preemption_time_exists_case1 => s Task Job jtR jaR costR arrR)).
    Definition tgt_preemption_time_exists_case1 : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_preemption_time_exists_case1
        Job dJ Task dT jtL jaL costL arrL)).

    Theorem preemption_time_exists_case1_correspondence :
      PropSPropRel src_preemption_time_exists_case1 tgt_preemption_time_exists_case1.
    Proof.
      unfold src_preemption_time_exists_case1, tgt_preemption_time_exists_case1.
      M_ps. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). M_jlfp. (apply (bpi_forall_tms
        Task); intros mR mL Hm). M_jp.
      apply ar_forall_identity_correspondence. intro j.
      (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_forall_nat_correspondence;
        intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL
        X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)). imp (ar_and_correspondence _ _ _ _
        (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL
        Hjp) (model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt costR costL
        Hcost mR mL Hm jpR jpL Hjp arrR arrL Harr)).
      imp (ar_bool_truth_correspondence _ _ (fpre_is_idle_related Job PR PL X sR sL Hs arrR arrL Harr _
        _ Ht1)).
      (apply ar_exists_nat_correspondence; intros eR eL He; apply ar_and_correspondence; [ exact
        (ar_bool_truth_correspondence _ _ (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL
        Harr jpR jpL Hjp _ _ He)) |]; exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _
        _ (ar_decide_le_related _ _ _ _ Ht1 He) (ar_decide_le_related _ _ _ _ He (svc_target_add_related
        _ _ _ _ Ht1 (max_lp_nonpreemptive_segment_correspondence pR pL Hp jpR jpL Hjp j _ _ Ht1)))))).
    Qed.

    Definition src_preemption_time_exists_case2 : Prop :=
      ltac:(body_of (fun s : S.statement_preemption_time_exists_case2 => s Task Job jtR jaR costR arrR)).
    Definition tgt_preemption_time_exists_case2 : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_preemption_time_exists_case2
        Job dJ Task dT jtL jaL costL arrL)).

    Theorem preemption_time_exists_case2_correspondence :
      PropSPropRel src_preemption_time_exists_case2 tgt_preemption_time_exists_case2.
    Proof.
      unfold src_preemption_time_exists_case2, tgt_preemption_time_exists_case2.
      (M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
        X); intros sR sL Hs); M_jlfp). (apply (bpi_forall_tms Task); intros mR mL Hm). M_jp. (apply
        (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr). imp
        (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr).
      apply ar_forall_identity_correspondence. intro j.
      (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_forall_nat_correspondence;
        intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL
        X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)). imp (ar_and_correspondence _ _ _ _
        (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL
        Hjp) (model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt costR costL
        Hcost mR mL Hm jpR jpL Hjp arrR arrL Harr)).
      apply ar_forall_identity_correspondence. intro jhp. imp (ar_bool_truth_correspondence _ _
        (fpre_scheduled_at_related Job PR PL X sR sL Hs jhp _ _ Ht1)).
      imp (ar_bool_truth_correspondence _ _ (Hp jhp j)).
      (apply ar_exists_nat_correspondence; intros eR eL He; apply ar_and_correspondence; [ exact
        (ar_bool_truth_correspondence _ _ (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL
        Harr jpR jpL Hjp _ _ He)) |]; exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _
        _ (ar_decide_le_related _ _ _ _ Ht1 He) (ar_decide_le_related _ _ _ _ He (svc_target_add_related
        _ _ _ _ Ht1 (max_lp_nonpreemptive_segment_correspondence pR pL Hp jpR jpL Hjp j _ _ Ht1)))))).
    Qed.

    Definition src_continuously_scheduled_between_preemption_points : Prop :=
      ltac:(body_of (fun s : S.statement_continuously_scheduled_between_preemption_points =>
        s Task Job jtR jaR costR arrR)).
    Definition tgt_continuously_scheduled_between_preemption_points : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_BusyInterval_Pi_continuously_scheduled_between_preemption_points
        Job dJ Task dT jtL jaL costL arrL)).

    Theorem continuously_scheduled_between_preemption_points_correspondence :
      PropSPropRel src_continuously_scheduled_between_preemption_points
        tgt_continuously_scheduled_between_preemption_points.
    Proof.
      unfold src_continuously_scheduled_between_preemption_points,
        tgt_continuously_scheduled_between_preemption_points.
      M_ps. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). (apply (bpi_forall_tms Task);
        intros mR mL Hm). M_jp. (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL
        Hs); intros jrR jrL Hjr). imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs
        arrR arrL Harr jrR jrL Hjr).
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      imp (ar_and_correspondence _ _ _ _ (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X
        sR sL Hs arrR arrL Harr jpR jpL Hjp) (model_with_bounded_nonpreemptive_segments_correspondence
        Task Job jtR jtL Hjt costR costL Hcost mR mL Hm jpR jpL Hjp arrR arrL Harr)). imp
        (ex_unit_service_related Job PR PL X).
      apply ar_forall_identity_correspondence. intro jlp. imp (ar_bool_truth_correspondence _ _
        (fpre_scheduled_at_related Job PR PL X sR sL Hs jlp _ _ Ht1)).
      apply ar_forall_nat_correspondence. intros fR fL Hf.
      (apply ar_imp_correspondence; [ apply ar_forall_nat_correspondence; let rR := fresh "rR" in let rL
        := fresh "rL" in let Hr := fresh "Hr" in intros rR rL Hr; apply ar_imp_correspondence; [ exact
        (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _
        ((fpre_service_related Job PR PL X sR sL Hs jlp _ _ Ht1)) Hr) (ar_decide_le_related _ _ _ _ Hr
        (svc_target_add_related _ _ _ _ ((fpre_service_related Job PR PL X sR sL Hs jlp _ _ Ht1))
        ((svc_target_sub_related _ _ _ _ (job_max_nonpreemptive_segment_correspondence Job costR costL
        Hcost jpR jpL Hjp jlp) (sub_nat_rel_canonical 1))))))) |]; apply ar_imp_correspondence; [exact
        (ar_bool_truth_correspondence _ _ (Hjp jlp _ _ Hr))|]; exact (sub_nat_le_correspondence _ _ _ _
        (svc_target_add_related _ _ _ _ ((fpre_service_related Job PR PL X sR sL Hs jlp _ _ Ht1)) Hf)
        Hr) |]).
      imp (sub_nat_le_correspondence _ _ _ _ Hf ((svc_target_sub_related _ _ _ _
        (job_max_nonpreemptive_segment_correspondence Job costR costL Hcost jpR jpL Hjp jlp)
        (sub_nat_rel_canonical 1)))).
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _
        Ht1 Ht) (ar_decide_lt_related _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht1 Hf)))).
      exact (ar_bool_truth_correspondence _ _ (fpre_scheduled_at_related Job PR PL X sR sL Hs jlp _ _ Ht)).
    Qed.

    Definition src_first_preemption_time : Prop :=
      ltac:(body_of (fun s : S.statement_first_preemption_time => s Task Job jtR jaR costR arrR)).
    Definition tgt_first_preemption_time : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_first_preemption_time
        Job dJ Task dT jtL jaL costL arrL)).

    Theorem first_preemption_time_correspondence :
      PropSPropRel src_first_preemption_time tgt_first_preemption_time.
    Proof.
      unfold src_first_preemption_time, tgt_first_preemption_time.
      M_va. M_ps. imp (isj_psr_uniprocessor_related Job PR PL X). (apply (fpre_forall_sched Job PR PL
        X); intros sR sL Hs). (apply (bpi_forall_tms Task); intros mR mL Hm). M_jp. imp
        (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL
        Hjp). (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL
        Hjr). imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR
        jrL Hjr).
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      imp (ar_and_correspondence _ _ _ _ (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X
        sR sL Hs arrR arrL Harr jpR jpL Hjp) (model_with_bounded_nonpreemptive_segments_correspondence
        Task Job jtR jtL Hjt costR costL Hcost mR mL Hm jpR jpL Hjp arrR arrL Harr)). imp
        (ex_unit_service_related Job PR PL X).
      apply ar_forall_identity_correspondence. intro jlp. imp (ar_bool_truth_correspondence _ _
        (fpre_scheduled_at_related Job PR PL X sR sL Hs jlp _ _ Ht1)).
      apply ar_forall_nat_correspondence. intros fR fL Hf.
      imp (ar_bool_truth_correspondence _ _ (Hjp jlp _ _ (svc_target_add_related _ _ _ _
        ((fpre_service_related Job PR PL X sR sL Hs jlp _ _ Ht1)) Hf))).
      (apply ar_imp_correspondence; [ apply ar_forall_nat_correspondence; let rR := fresh "rR" in let rL
        := fresh "rL" in let Hr := fresh "Hr" in intros rR rL Hr; apply ar_imp_correspondence; [ exact
        (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _
        ((fpre_service_related Job PR PL X sR sL Hs jlp _ _ Ht1)) Hr) (ar_decide_le_related _ _ _ _ Hr
        (svc_target_add_related _ _ _ _ ((fpre_service_related Job PR PL X sR sL Hs jlp _ _ Ht1))
        ((svc_target_sub_related _ _ _ _ (job_max_nonpreemptive_segment_correspondence Job costR costL
        Hcost jpR jpL Hjp jlp) (sub_nat_rel_canonical 1))))))) |]; apply ar_imp_correspondence; [exact
        (ar_bool_truth_correspondence _ _ (Hjp jlp _ _ Hr))|]; exact (sub_nat_le_correspondence _ _ _ _
        (svc_target_add_related _ _ _ _ ((fpre_service_related Job PR PL X sR sL Hs jlp _ _ Ht1)) Hf)
        Hr) |]).
      imp (sub_nat_le_correspondence _ _ _ _ Hf ((svc_target_sub_related _ _ _ _
        (job_max_nonpreemptive_segment_correspondence Job costR costL Hcost jpR jpL Hjp jlp)
        (sub_nat_rel_canonical 1)))).
      imp (isj_psr_ideal_progress_related Job PR PL X).
      exact (ar_bool_truth_correspondence _ _
        (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp _ _
          (svc_target_add_related _ _ _ _ Ht1 Hf))).
    Qed.

    Definition src_preemption_time_exists_case3 : Prop :=
      ltac:(body_of (fun s : S.statement_preemption_time_exists_case3 => s Task Job jtR jaR costR arrR)).
    Definition tgt_preemption_time_exists_case3 : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_preemption_time_exists_case3
        Job dJ Task dT jtL jaL costL arrL)).

    Theorem preemption_time_exists_case3_correspondence :
      PropSPropRel src_preemption_time_exists_case3 tgt_preemption_time_exists_case3.
    Proof.
      unfold src_preemption_time_exists_case3, tgt_preemption_time_exists_case3.
      (M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
        X); intros sR sL Hs); M_jlfp). imp (hap_transitive_rel Job pR pL Hp). (apply (bpi_forall_tms
        Task); intros mR mL Hm). M_jp. imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL
        X sR sL Hs arrR arrL Harr jpR jpL Hjp). (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost
        PR PL X sR sL Hs); intros jrR jrL Hjr). (imp (ex_work_bearing_related Job jaR jaL Hja costR
        costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel
        Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp
        (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR
        jpL Hjp pR pL Hp); apply ar_forall_identity_correspondence; intro j; imp
        (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp (ar_bool_truth_correspondence
        _ _ (ex_job_cost_positive_related Job costR costL Hcost j)); (apply
        ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_forall_nat_correspondence; intros t2R
        t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
        arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2))). imp (ar_and_correspondence _ _ _ _
        (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL
        Hjp) (model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt costR costL
        Hcost mR mL Hm jpR jpL Hjp arrR arrL Harr)). imp (ex_unit_service_related Job PR PL X).
      apply ar_forall_identity_correspondence. intro jlp. imp (ar_bool_truth_correspondence _ _
        (fpre_scheduled_at_related Job PR PL X sR sL Hs jlp _ _ Ht1)). imp (ar_bool_truth_correspondence
        _ _ (svc_bool_not_related _ _ (Hp jlp j))).
      imp (isj_psr_ideal_progress_related Job PR PL X). (apply ar_exists_nat_correspondence; intros eR
        eL He; apply ar_and_correspondence; [ exact (ar_bool_truth_correspondence _ _
        (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp _ _ He)) |]; exact
        (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1
        He) (ar_decide_le_related _ _ _ _ He (svc_target_add_related _ _ _ _ Ht1
        (max_lp_nonpreemptive_segment_correspondence pR pL Hp jpR jpL Hjp j _ _ Ht1)))))).
    Qed.

    Definition src_preemption_time_exists : Prop :=
      ltac:(body_of (fun s : S.statement_preemption_time_exists => s Task Job jtR jaR costR arrR)).
    Definition tgt_preemption_time_exists : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_preemption_time_exists
        Job dJ Task dT jtL jaL costL arrL)).

    Theorem preemption_time_exists_correspondence :
      PropSPropRel src_preemption_time_exists tgt_preemption_time_exists.
    Proof.
      unfold src_preemption_time_exists, tgt_preemption_time_exists.
      (M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
        X); intros sR sL Hs); M_jlfp). imp (hap_transitive_rel Job pR pL Hp). (apply (bpi_forall_tms
        Task); intros mR mL Hm). M_jp. imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL
        X sR sL Hs arrR arrL Harr jpR jpL Hjp). (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost
        PR PL X sR sL Hs); intros jrR jrL Hjr). (imp (ex_work_bearing_related Job jaR jaL Hja costR
        costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel
        Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp
        (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR
        jpL Hjp pR pL Hp); apply ar_forall_identity_correspondence; intro j; imp
        (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp (ar_bool_truth_correspondence
        _ _ (ex_job_cost_positive_related Job costR costL Hcost j)); (apply
        ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_forall_nat_correspondence; intros t2R
        t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
        arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2))). imp (ar_and_correspondence _ _ _ _
        (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL
        Hjp) (model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt costR costL
        Hcost mR mL Hm jpR jpL Hjp arrR arrL Harr)). imp (ex_unit_service_related Job PR PL X). imp
        (isj_psr_ideal_progress_related Job PR PL X).
      (apply ar_exists_nat_correspondence; intros eR eL He; apply ar_and_correspondence; [ exact
        (ar_bool_truth_correspondence _ _ (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL
        Harr jpR jpL Hjp _ _ He)) |]; exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _
        _ (ar_decide_le_related _ _ _ _ Ht1 He) (ar_decide_le_related _ _ _ _ He (svc_target_add_related
        _ _ _ _ Ht1 (max_lp_nonpreemptive_segment_correspondence pR pL Hp jpR jpL Hjp j _ _ Ht1)))))).
    Qed.
  End Tasks.

  Definition src_hp_job_not_scheduled_before_quiet_time : Prop :=
    ltac:(body_of (fun s : S.statement_hp_job_not_scheduled_before_quiet_time => s Job jaR costR arrR)).
  Definition tgt_hp_job_not_scheduled_before_quiet_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_hp_job_not_scheduled_before_quiet_time
      Job dJ jaL costL arrL)).

  Theorem hp_job_not_scheduled_before_quiet_time_correspondence :
    PropSPropRel src_hp_job_not_scheduled_before_quiet_time tgt_hp_job_not_scheduled_before_quiet_time.
  Proof.
    unfold src_hp_job_not_scheduled_before_quiet_time, tgt_hp_job_not_scheduled_before_quiet_time.
    M_ps. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). M_jlfp. (apply (fpre_forall_jr Job
      jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr). imp (fpre_valid_schedule_rel
      Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr).
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro jhp.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ex_quiet_time_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j
      _ _ (pp_succ_related _ _ Ht)).
    imp (ar_bool_truth_correspondence _ _ (fpre_scheduled_at_related Job PR PL X sR sL Hs jhp _ _
      (pp_succ_related _ _ Ht))).
    imp (ar_bool_truth_correspondence _ _ (Hp jhp j)).
    exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs jhp _ _ Ht))).
  Qed.

  Definition src_no_intermediate_preemption_point : Prop :=
    ltac:(body_of (fun s : S.statement_no_intermediate_preemption_point => s Job costR)).
  Definition tgt_no_intermediate_preemption_point : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_no_intermediate_preemption_point
      Job dJ costL)).

  Theorem no_intermediate_preemption_point_correspondence :
    PropSPropRel src_no_intermediate_preemption_point tgt_no_intermediate_preemption_point.
  Proof.
    unfold src_no_intermediate_preemption_point, tgt_no_intermediate_preemption_point.
    M_ps. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). M_jp.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_identity_correspondence. intro jlp.
    apply ar_forall_nat_correspondence. intros fR fL Hf.
    (apply ar_imp_correspondence; [ apply ar_forall_nat_correspondence; let rR := fresh "rR" in let rL
      := fresh "rL" in let Hr := fresh "Hr" in intros rR rL Hr; apply ar_imp_correspondence; [ exact
      (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _
      ((fpre_service_related Job PR PL X sR sL Hs jlp _ _ Ht1)) Hr) (ar_decide_le_related _ _ _ _ Hr
      (svc_target_add_related _ _ _ _ ((fpre_service_related Job PR PL X sR sL Hs jlp _ _ Ht1))
      ((svc_target_sub_related _ _ _ _ (job_max_nonpreemptive_segment_correspondence Job costR costL
      Hcost jpR jpL Hjp jlp) (sub_nat_rel_canonical 1))))))) |]; apply ar_imp_correspondence; [exact
      (ar_bool_truth_correspondence _ _ (Hjp jlp _ _ Hr))|]; exact (sub_nat_le_correspondence _ _ _ _
      (svc_target_add_related _ _ _ _ ((fpre_service_related Job PR PL X sR sL Hs jlp _ _ Ht1)) Hf) Hr)
      |]).
    imp (sub_nat_le_correspondence _ _ _ _ Hf ((svc_target_sub_related _ _ _ _
      (job_max_nonpreemptive_segment_correspondence Job costR costL Hcost jpR jpL Hjp jlp)
      (sub_nat_rel_canonical 1)))).
    apply ar_forall_nat_correspondence. intros rR rL Hr.
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _
      ((fpre_service_related Job PR PL X sR sL Hs jlp _ _ Ht1)) Hr) (ar_decide_lt_related _ _ _ _ Hr
      (svc_target_add_related _ _ _ _ ((fpre_service_related Job PR PL X sR sL Hs jlp _ _ Ht1)) Hf)))).
    exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hjp jlp _ _ Hr))).
  Qed.

  Definition src_preemption_time_le_max_len_of_np_segment : Prop :=
    ltac:(body_of (fun s : S.statement_preemption_time_le_max_len_of_np_segment => s Job jaR costR arrR)).
  Definition tgt_preemption_time_le_max_len_of_np_segment : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Pi_preemption_time_le_max_len_of_np_segment
      Job dJ jaL costL arrL)).

  Theorem preemption_time_le_max_len_of_np_segment_correspondence :
    PropSPropRel src_preemption_time_le_max_len_of_np_segment tgt_preemption_time_le_max_len_of_np_segment.
  Proof.
    unfold src_preemption_time_le_max_len_of_np_segment, tgt_preemption_time_le_max_len_of_np_segment.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (hap_transitive_rel Job pR pL Hp); M_jp; imp
      (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL
      Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL
      Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
      Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply ar_forall_identity_correspondence; intro
      j; imp (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp
      (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j)); (apply
      ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_forall_nat_correspondence; intros t2R
      t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
      arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))).
    apply ar_forall_identity_correspondence. intro jlp. imp (ar_bool_truth_correspondence _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs jlp _ _ Ht1)). imp (ar_bool_truth_correspondence _
      _ (svc_bool_not_related _ _ (Hp jlp j))).
    apply ar_forall_nat_correspondence. intros fR fL Hf.
    imp (ar_bool_truth_correspondence _ _ (Hjp jlp _ _ (svc_target_add_related _ _ _ _
      ((fpre_service_related Job PR PL X sR sL Hs jlp _ _ Ht1)) Hf))).
    imp (sub_nat_le_correspondence _ _ _ _ Hf ((svc_target_sub_related _ _ _ _
      (job_max_nonpreemptive_segment_correspondence Job costR costL Hcost jpR jpL Hjp jlp)
      (sub_nat_rel_canonical 1)))).
    exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_le_related _ _ _ _ Ht1 (svc_target_add_related _ _ _ _ Ht1 Hf))
      (ar_decide_le_related _ _ _ _ (svc_target_add_related _ _ _ _ Ht1 Hf)
        (svc_target_add_related _ _ _ _ Ht1
          (max_lp_nonpreemptive_segment_correspondence pR pL Hp jpR jpL Hjp j _ _ Ht1))))).
  Qed.

  Definition src_no_priority_inversion_after_preemption_point : Prop :=
    ltac:(body_of (fun s : S.statement_no_priority_inversion_after_preemption_point => s Job jaR costR arrR)).
  Definition tgt_no_priority_inversion_after_preemption_point : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_Pi_no_priority_inversion_after_preemption_point
      Job dJ jaL costL arrL)).

  Theorem no_priority_inversion_after_preemption_point_correspondence :
    PropSPropRel src_no_priority_inversion_after_preemption_point
      tgt_no_priority_inversion_after_preemption_point.
  Proof.
    unfold src_no_priority_inversion_after_preemption_point, tgt_no_priority_inversion_after_preemption_point.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (hap_transitive_rel Job pR pL Hp); M_jp; imp
      (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL
      Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL
      Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
      Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply ar_forall_identity_correspondence; intro
      j; imp (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp
      (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j)); (apply
      ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_forall_nat_correspondence; intros t2R
      t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
      arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))).
    apply ar_forall_nat_correspondence. intros pR' pL' Hpp. imp (ar_bool_truth_correspondence _ _
      (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp _ _ Hpp)).
    imp (sub_nat_le_correspondence _ _ _ _ Ht1 Hpp).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Hpp
      Ht) (ar_decide_lt_related _ _ _ _ Ht Ht2))).
    exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ ((ex_priority_inversion_related
      Job PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht)))).
  Qed.

  Definition src_priority_inversion_occurs_only_till_preemption_point : Prop :=
    ltac:(body_of (fun s : S.statement_priority_inversion_occurs_only_till_preemption_point =>
      s Job jaR costR arrR)).
  Definition tgt_priority_inversion_occurs_only_till_preemption_point : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_Pi_priority_inversion_occurs_only_till_preemption_point
      Job dJ jaL costL arrL)).

  Theorem priority_inversion_occurs_only_till_preemption_point_correspondence :
    PropSPropRel src_priority_inversion_occurs_only_till_preemption_point
      tgt_priority_inversion_occurs_only_till_preemption_point.
  Proof.
    unfold src_priority_inversion_occurs_only_till_preemption_point,
      tgt_priority_inversion_occurs_only_till_preemption_point.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (hap_transitive_rel Job pR pL Hp); M_jp; imp
      (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL
      Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL
      Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
      Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs
      arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply ar_forall_identity_correspondence; intro
      j; imp (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp
      (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j)); (apply
      ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_forall_nat_correspondence; intros t2R
      t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
      arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))).
    apply ar_forall_nat_correspondence. intros pR' pL' Hpp. imp (ar_bool_truth_correspondence _ _
      (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp _ _ Hpp)).
    imp (sub_nat_le_correspondence _ _ _ _ Ht1 Hpp).
    exact (sub_nat_le_correspondence _ _ _ _
      (ex_cumulative_priority_inversion_related Job PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _
        Ht1 Ht2)
      (ex_cumulative_priority_inversion_related Job PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _
        Ht1 Hpp)).
  Qed.
End BusyIntervalPi.
