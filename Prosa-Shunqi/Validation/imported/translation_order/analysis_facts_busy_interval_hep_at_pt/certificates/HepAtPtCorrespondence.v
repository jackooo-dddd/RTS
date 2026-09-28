From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import HepAtPtSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes model.schedule.work_conserving model.job.properties
  analysis.definitions.work_bearing_readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedHepAtPt ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers.

Module I := ImportedHepAtPt.
Module S := HepAtPtSemanticSource.HepAtPtSemanticSource.

(** Statement correspondence for [analysis/facts/busy_interval/hep_at_pt.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (job type, arrival and cost classes, arrival
    sequence); target side: the imported Lean theorem types.  Inputs:
    [job_arrival] by [ArJobArrivalRel], [job_cost] by the accepted
    [SvcJobCostRel], arrival sequences by [ArArrivalSequenceRel].  Inputs
    quantified inside a statement are covered in both directions by the
    accepted conversions: processor models ([isj_cover_pstate]), schedules
    through the processor-model relation ([fpre_forall_sched]), JLFP policies
    ([fpre_forall_jlfp]), [JobPreemptable] instances ([fpre_forall_jp]), the
    readiness instance on the statement's schedule pair ([fpre_forall_jr]),
    jobs (identity) and instants.  The busy-interval prefix, quiet times,
    work conservation, work-bearing readiness and unit service are the
    accepted busy-interval-existence helpers; schedule validity, preemption
    times, preemption-model validity and the JLFP-at-preemption-point policy
    are the accepted preemption-facts helpers; priority transitivity is
    related by unfolding, and [t.-1] by the accepted subtraction relation
    ([subn1]).  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma hap_pred_related (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL ->
  SubNatRel nR.-1 (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
    nL (sub_nat_to_imported 1)).
Proof.
  intro Hn. have H := svc_target_sub_related nR nL 1 (sub_nat_to_imported 1) Hn (sub_nat_rel_canonical 1).
  rewrite subn1 in H. exact H.
Qed.

Section HepAtPt.
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

  Lemma hap_transitive_rel pR pL (Hp : FpreJLFPRel Job pR pL) :
    PropSPropRel (@prosa.model.priority.definitions.transitive_job_priorities Job pR)
      (I.Prosa_Model_Priority_Definitions_transitive_job_priorities Job dJ pL).
  Proof.
    unfold prosa.model.priority.definitions.transitive_job_priorities.
    cbn [I.Prosa_Model_Priority_Definitions_transitive_job_priorities].
    apply ar_forall_identity_correspondence. intro y.
    apply ar_forall_identity_correspondence. intro x.
    apply ar_forall_identity_correspondence. intro z.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp x y))|].
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp y z))|].
    exact (ar_bool_truth_correspondence _ _ (Hp x z)).
  Qed.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].
  Local Ltac M_va := imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
  Local Ltac M_ps := apply (isj_cover_pstate Job); intros PR PL X.
  Local Ltac M_jlfp := apply fpre_forall_jlfp; intros pR pL Hp.
  Local Ltac M_jp := apply fpre_forall_jp; intros jpR jpL Hjp.

  Definition src_instant_t_is_not_idle : Prop :=
    ltac:(body_of (fun s : S.statement_instant_t_is_not_idle => s Job jaR costR arrR)).
  Definition tgt_instant_t_is_not_idle : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_HepAtPt_instant_t_is_not_idle
      Job dJ jaL costL arrL)).

  Theorem instant_t_is_not_idle_correspondence :
    PropSPropRel src_instant_t_is_not_idle tgt_instant_t_is_not_idle.
  Proof.
    unfold src_instant_t_is_not_idle, tgt_instant_t_is_not_idle.
    M_va. M_ps. (apply (fpre_forall_sched Job PR PL X); intros sR sL Hs). M_jlfp. imp
      (fpre_reflexive_rel Job pR pL Hp). (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL
      X sR sL Hs); intros jrR jrL Hjr). imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost
      PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr). imp (fpre_valid_schedule_rel Job jaR jaL
      costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr). imp (ex_work_conserving_related Job jaR
      jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr).
    apply ar_forall_identity_correspondence. intro j. imp (arrives_in_correspondence_certificate Job
      arrR arrL j Harr). imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR
      costL Hcost j)). (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)). (apply
      ar_forall_nat_correspondence; intros tR tL Ht; imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _
      Ht Ht2)))).
    exact (pi_not_correspondence _ _ (ar_bool_truth_correspondence _ _
      (fpre_is_idle_related Job PR PL X sR sL Hs arrR arrL Harr _ _ Ht))).
  Qed.

  Definition src_scheduled_at_preemption_time_implies_higher_or_equal_priority_lt : Prop :=
    ltac:(body_of (fun s : S.statement_scheduled_at_preemption_time_implies_higher_or_equal_priority_lt =>
      s Job jaR costR arrR)).
  Definition tgt_scheduled_at_preemption_time_implies_higher_or_equal_priority_lt : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_HepAtPt_scheduled_at_preemption_time_implies_higher_or_equal_priority_lt
      Job dJ jaL costL arrL)).

  Theorem scheduled_at_preemption_time_implies_higher_or_equal_priority_lt_correspondence :
    PropSPropRel src_scheduled_at_preemption_time_implies_higher_or_equal_priority_lt
      tgt_scheduled_at_preemption_time_implies_higher_or_equal_priority_lt.
  Proof.
    unfold src_scheduled_at_preemption_time_implies_higher_or_equal_priority_lt,
      tgt_scheduled_at_preemption_time_implies_higher_or_equal_priority_lt.
    (M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL X);
      intros sR sL Hs); M_jlfp; imp (hap_transitive_rel pR pL Hp); M_jp; (apply (fpre_forall_jr Job jaR
      jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr); imp (ex_work_bearing_related Job
      jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr)). imp
      (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR
      jpL Hjp pR pL Hp).
    apply ar_forall_identity_correspondence. intro j. (apply ar_forall_nat_correspondence; intros t1R
      t1L Ht1; apply ar_forall_nat_correspondence; intros t2R t2L Ht2; imp
      (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
      pR pL Hp j _ _ _ _ Ht1 Ht2)). (apply ar_forall_nat_correspondence; intros tR tL Ht; imp
      (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1
      Ht) (ar_decide_lt_related _ _ _ _ Ht Ht2)))). imp (ar_bool_truth_correspondence _ _
      (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp _ _ Ht)).
    imp (sub_nat_lt_correspondence _ _ _ _ Ht (hap_pred_related _ _ Ht2)).
    (apply ar_forall_identity_correspondence; intro jhp; imp (ar_bool_truth_correspondence _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs jhp _ _ Ht))).
    exact (ar_bool_truth_correspondence _ _ (Hp jhp j)).
  Qed.

  Definition src_scheduled_at_preemption_time_implies_higher_or_equal_priority_eq : Prop :=
    ltac:(body_of (fun s : S.statement_scheduled_at_preemption_time_implies_higher_or_equal_priority_eq =>
      s Job jaR costR arrR)).
  Definition tgt_scheduled_at_preemption_time_implies_higher_or_equal_priority_eq : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_HepAtPt_scheduled_at_preemption_time_implies_higher_or_equal_priority_eq
      Job dJ jaL costL arrL)).

  Theorem scheduled_at_preemption_time_implies_higher_or_equal_priority_eq_correspondence :
    PropSPropRel src_scheduled_at_preemption_time_implies_higher_or_equal_priority_eq
      tgt_scheduled_at_preemption_time_implies_higher_or_equal_priority_eq.
  Proof.
    unfold src_scheduled_at_preemption_time_implies_higher_or_equal_priority_eq,
      tgt_scheduled_at_preemption_time_implies_higher_or_equal_priority_eq.
    (M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL X);
      intros sR sL Hs); M_jlfp; imp (hap_transitive_rel pR pL Hp); M_jp; (apply (fpre_forall_jr Job jaR
      jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr); imp (ex_work_bearing_related Job
      jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr)). imp
      (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr). imp
      (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR
      jpL Hjp pR pL Hp).
    apply ar_forall_identity_correspondence. intro j. imp (arrives_in_correspondence_certificate Job
      arrR arrL j Harr). imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR
      costL Hcost j)). (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)). (apply
      ar_forall_nat_correspondence; intros tR tL Ht; imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _
      Ht Ht2)))). imp (ar_bool_truth_correspondence _ _ (fpre_preemption_time_related Job PR PL X sR sL
      Hs arrR arrL Harr jpR jpL Hjp _ _ Ht)).
    imp (sub_nat_eq_correspondence _ _ _ _ Ht (hap_pred_related _ _ Ht2)).
    (apply ar_forall_identity_correspondence; intro jhp; imp (ar_bool_truth_correspondence _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs jhp _ _ Ht))).
    exact (ar_bool_truth_correspondence _ _ (Hp jhp j)).
  Qed.

  Definition src_scheduled_at_preemption_time_implies_higher_or_equal_priority : Prop :=
    ltac:(body_of (fun s : S.statement_scheduled_at_preemption_time_implies_higher_or_equal_priority =>
      s Job jaR costR arrR)).
  Definition tgt_scheduled_at_preemption_time_implies_higher_or_equal_priority : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_HepAtPt_scheduled_at_preemption_time_implies_higher_or_equal_priority
      Job dJ jaL costL arrL)).

  Theorem scheduled_at_preemption_time_implies_higher_or_equal_priority_correspondence :
    PropSPropRel src_scheduled_at_preemption_time_implies_higher_or_equal_priority
      tgt_scheduled_at_preemption_time_implies_higher_or_equal_priority.
  Proof.
    unfold src_scheduled_at_preemption_time_implies_higher_or_equal_priority,
      tgt_scheduled_at_preemption_time_implies_higher_or_equal_priority.
    (M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL X);
      intros sR sL Hs); M_jlfp; imp (hap_transitive_rel pR pL Hp); M_jp; (apply (fpre_forall_jr Job jaR
      jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr); imp (ex_work_bearing_related Job
      jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr)). imp
      (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr). imp
      (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR
      jpL Hjp pR pL Hp).
    apply ar_forall_identity_correspondence. intro j. imp (arrives_in_correspondence_certificate Job
      arrR arrL j Harr). imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR
      costL Hcost j)). (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)). (apply
      ar_forall_nat_correspondence; intros tR tL Ht; imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _
      Ht Ht2)))). imp (ar_bool_truth_correspondence _ _ (fpre_preemption_time_related Job PR PL X sR sL
      Hs arrR arrL Harr jpR jpL Hjp _ _ Ht)).
    (apply ar_forall_identity_correspondence; intro jhp; imp (ar_bool_truth_correspondence _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs jhp _ _ Ht))).
    exact (ar_bool_truth_correspondence _ _ (Hp jhp j)).
  Qed.

  Definition src_scheduled_at_preemption_time_implies_arrived_between_within_busy_interval : Prop :=
    ltac:(body_of (fun s :
      S.statement_scheduled_at_preemption_time_implies_arrived_between_within_busy_interval =>
      s Job jaR costR arrR)).
  Definition tgt_scheduled_at_preemption_time_implies_arrived_between_within_busy_interval : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_HepAtPt_scheduled_at_preemption_time_implies_arrived_between_within_busy_interval
      Job dJ jaL costL arrL)).

  Theorem scheduled_at_preemption_time_implies_arrived_between_within_busy_interval_correspondence :
    PropSPropRel src_scheduled_at_preemption_time_implies_arrived_between_within_busy_interval
      tgt_scheduled_at_preemption_time_implies_arrived_between_within_busy_interval.
  Proof.
    unfold src_scheduled_at_preemption_time_implies_arrived_between_within_busy_interval,
      tgt_scheduled_at_preemption_time_implies_arrived_between_within_busy_interval.
    (M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL X);
      intros sR sL Hs); M_jlfp; imp (hap_transitive_rel pR pL Hp); M_jp; (apply (fpre_forall_jr Job jaR
      jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr); imp (ex_work_bearing_related Job
      jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr)). imp
      (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr). imp
      (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR
      jpL Hjp pR pL Hp).
    apply ar_forall_identity_correspondence. intro j. imp (arrives_in_correspondence_certificate Job
      arrR arrL j Harr). imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR
      costL Hcost j)). (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)). (apply
      ar_forall_nat_correspondence; intros tR tL Ht; imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _
      Ht Ht2)))). imp (ar_bool_truth_correspondence _ _ (fpre_preemption_time_related Job PR PL X sR sL
      Hs arrR arrL Harr jpR jpL Hjp _ _ Ht)).
    (apply ar_forall_identity_correspondence; intro jhp; imp (ar_bool_truth_correspondence _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs jhp _ _ Ht))).
    exact (ar_bool_truth_correspondence _ _
      (arrived_between_correspondence_certificate Job jaR jaL jhp Hja _ _ _ _ Ht1 Ht2)).
  Qed.

  Definition src_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point : Prop :=
    ltac:(body_of (fun s : S.statement_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point =>
      s Job jaR costR arrR)).
  Definition tgt_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_HepAtPt_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
      Job dJ jaL costL arrL)).

  Theorem not_quiet_implies_exists_scheduled_hp_job_at_preemption_point_correspondence :
    PropSPropRel src_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
      tgt_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point.
  Proof.
    unfold src_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point,
      tgt_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point.
    (M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL X);
      intros sR sL Hs); M_jlfp; imp (fpre_reflexive_rel Job pR pL Hp); imp (hap_transitive_rel pR pL
      Hp)). M_jp. (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR
      jrL Hjr). (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR
      arrL Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR
      sL Hs arrR arrL Harr jrR jrL Hjr); imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X
      sR sL Hs arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X
      sR sL Hs arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply
      ar_forall_identity_correspondence; intro j; imp (arrives_in_correspondence_certificate Job arrR
      arrL j Harr); imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL
      Hcost j)); (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2))). (apply
      ar_forall_nat_correspondence; intros tR tL Ht; imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _
      Ht Ht2)))). imp (ar_bool_truth_correspondence _ _ (fpre_preemption_time_related Job PR PL X sR sL
      Hs arrR arrL Harr jpR jpL Hjp _ _ Ht)).
    (apply ex_exists_identity; intro j_hp; apply ar_and_correspondence; [ exact
      (ar_bool_truth_correspondence _ _ (arrived_between_correspondence_certificate Job jaR jaL j_hp Hja
      _ _ _ _ Ht1 Ht2)) |]; apply ar_and_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp
      j_hp j))|]; exact (ar_bool_truth_correspondence _ _ (fpre_scheduled_at_related Job PR PL X sR sL
      Hs j_hp _ _ Ht))).
  Qed.

  Definition src_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point : Prop :=
    ltac:(body_of (fun s : S.statement_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point =>
      s Job jaR costR arrR)).
  Definition tgt_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_HepAtPt_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point
      Job dJ jaL costL arrL)).

  Theorem not_quiet_implies_exists_scheduled_hp_job_after_preemption_point_correspondence :
    PropSPropRel src_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point
      tgt_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point.
  Proof.
    unfold src_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point,
      tgt_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point.
    (M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL X);
      intros sR sL Hs); M_jlfp; imp (fpre_reflexive_rel Job pR pL Hp); imp (hap_transitive_rel pR pL
      Hp)). M_jp. imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL
      Harr jpR jpL Hjp). (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs);
      intros jrR jrL Hjr). (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL
      Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR
      PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp (ex_work_conserving_related Job jaR jaL costR costL
      PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR costL
      PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply
      ar_forall_identity_correspondence; intro j; imp (arrives_in_correspondence_certificate Job arrR
      arrL j Harr); imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL
      Hcost j)); (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2))).
    apply ar_forall_nat_correspondence. intros tpR tpL Htp.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL
      Harr jpR jpL Hjp _ _ Htp)).
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_le_related _ _ _ _ Ht1 Htp) (ar_decide_lt_related _ _ _ _ Htp Ht2))).
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_le_related _ _ _ _ Htp Ht) (ar_decide_lt_related _ _ _ _ Ht Ht2))).
    (apply ex_exists_identity; intro j_hp; apply ar_and_correspondence; [ exact
      (ar_bool_truth_correspondence _ _ (arrived_between_correspondence_certificate Job jaR jaL j_hp Hja
      _ _ _ _ Ht1 (pp_succ_related _ _ Ht))) |]; apply ar_and_correspondence; [exact
      (ar_bool_truth_correspondence _ _ (Hp j_hp j))|]; exact (ar_bool_truth_correspondence _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs j_hp _ _ Ht))).
  Qed.

  Definition src_not_quiet_implies_exists_scheduled_hp_job : Prop :=
    ltac:(body_of (fun s : S.statement_not_quiet_implies_exists_scheduled_hp_job => s Job jaR costR arrR)).
  Definition tgt_not_quiet_implies_exists_scheduled_hp_job : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_HepAtPt_not_quiet_implies_exists_scheduled_hp_job
      Job dJ jaL costL arrL)).

  Theorem not_quiet_implies_exists_scheduled_hp_job_correspondence :
    PropSPropRel src_not_quiet_implies_exists_scheduled_hp_job tgt_not_quiet_implies_exists_scheduled_hp_job.
  Proof.
    unfold src_not_quiet_implies_exists_scheduled_hp_job, tgt_not_quiet_implies_exists_scheduled_hp_job.
    (M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL X);
      intros sR sL Hs); M_jlfp; imp (fpre_reflexive_rel Job pR pL Hp); imp (hap_transitive_rel pR pL
      Hp)). M_jp. imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL
      Harr jpR jpL Hjp). (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs);
      intros jrR jrL Hjr). (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL
      Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR
      PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp (ex_work_conserving_related Job jaR jaL costR costL
      PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR costL
      PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply
      ar_forall_identity_correspondence; intro j; imp (arrives_in_correspondence_certificate Job arrR
      arrL j Harr); imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL
      Hcost j)); (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2))).
    apply ar_forall_nat_correspondence. intros KR KL HK.
    have HtK := svc_target_add_related _ _ _ _ Ht1 HK.
    apply ar_imp_correspondence.
    { apply ar_exists_nat_correspondence. intros pR' pL' Hpr.
      apply ar_and_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp _ _ Hpr))|].
      exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
        (ar_decide_le_related _ _ _ _ Ht1 Hpr) (ar_decide_le_related _ _ _ _ Hpr HtK))). }
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_le_related _ _ _ _ HtK Ht) (ar_decide_lt_related _ _ _ _ Ht Ht2))).
    (apply ex_exists_identity; intro j_hp; apply ar_and_correspondence; [ exact
      (ar_bool_truth_correspondence _ _ (arrived_between_correspondence_certificate Job jaR jaL j_hp Hja
      _ _ _ _ Ht1 (pp_succ_related _ _ Ht))) |]; apply ar_and_correspondence; [exact
      (ar_bool_truth_correspondence _ _ (Hp j_hp j))|]; exact (ar_bool_truth_correspondence _ _
      (fpre_scheduled_at_related Job PR PL X sR sL Hs j_hp _ _ Ht))).
  Qed.
End HepAtPt.
