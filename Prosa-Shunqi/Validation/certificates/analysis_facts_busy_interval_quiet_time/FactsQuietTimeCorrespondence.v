From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsQuietTimeSemanticSource.
From prosa Require Import analysis.definitions.carry_in.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsQuietTime ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  CarryInCorrespondence.

Module I := ImportedFactsQuietTime.
Module S := FactsQuietTimeSemanticSource.FactsQuietTimeSemanticSource.
Module B := BusyIntervalClassicalSemanticSource.BusyIntervalClassicalSemanticSource.

(** Statement correspondences for [analysis/facts/busy_interval/quiet_time.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (job type, job arrival / cost, JLFP policy,
    processor state, schedule, arrival sequence); target side: the imported
    Lean theorem types at related inputs ([ArJobArrivalRel],
    [SvcJobCostRel], the policy pointwise on Booleans, the accepted two-sided
    [SvcProcessorStateRel]/[SvcScheduleRel], [ArArrivalSequenceRel]).  Later
    binders are covered in both directions (jobs as identity carriers, Nats).
    Quiet time, busy-interval prefix and busy interval replay the accepted
    busy-interval proofs; [no_carry_in] is closed by the accepted
    [CarryInCorrespondence].  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fqt_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma fqt_not_correspondence (P : Prop) (PL : SProp) :
  PropSPropRel P PL -> PropSPropRel (~ P) (I.Not PL).
Proof.
  intro HP. unfold I.Not. apply ar_imp_correspondence; [exact HP|].
  exact fqt_false_correspondence.
Qed.

Section Facts.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hp : forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let COMPLETED := pp_completed_by_related Job costR costL Hcost PStateR PStateL R schedR schedL Hsched.

  Lemma fqt_quiet_time_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    PropSPropRel (@B.quiet_time Job jaR costR PStateR arrR schedR pR j tR)
      (I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time
        Job dJ jaL costL PStateL arrL schedL pL j tL).
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

  Lemma fqt_window_related t1R t1L tR tL t2R t2L :
    SubNatRel t1R t1L -> SubNatRel tR tL -> SubNatRel t2R t2L ->
    PropSPropRel (is_true (ltn t1R tR && ltn tR t2R))
      (Lean.eq (I.Bool_and (ar_target_decide_lt t1L tL) (ar_target_decide_lt tL t2L)) I.Bool_true).
  Proof.
    intros H1 Ht H2.
    exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_lt_related _ _ _ _ H1 Ht) (ar_decide_lt_related _ _ _ _ Ht H2))).
  Qed.

  Lemma fqt_busy_interval_prefix_related (j : Job) t1R t1L t2R t2L :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    PropSPropRel (@B.busy_interval_prefix Job jaR costR PStateR arrR schedR pR j t1R t2R)
      (I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix
        Job dJ jaL costL PStateL arrL schedL pL j t1L t2L).
  Proof.
    intros H1 H2. unfold B.busy_interval_prefix.
    cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix].
    apply ar_and_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ H1 H2)|].
    apply ar_and_correspondence; [exact (fqt_quiet_time_related j _ _ H1)|].
    apply ar_and_correspondence.
    - apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (fqt_window_related _ _ _ _ _ _ H1 Ht H2)|].
      exact (fqt_not_correspondence _ _ (fqt_quiet_time_related j _ _ Ht)).
    - exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
        (ar_decide_le_related _ _ _ _ H1 (Hja j)) (ar_decide_lt_related _ _ _ _ (Hja j) H2))).
  Qed.

  Lemma fqt_busy_interval_related (j : Job) t1R t1L t2R t2L :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    PropSPropRel (@B.busy_interval Job jaR costR PStateR arrR schedR pR j t1R t2R)
      (I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval
        Job dJ jaL costL PStateL arrL schedL pL j t1L t2L).
  Proof.
    intros H1 H2. unfold B.busy_interval.
    cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval].
    apply ar_and_correspondence; [exact (fqt_busy_interval_prefix_related j _ _ _ _ H1 H2)|].
    exact (fqt_quiet_time_related j _ _ H2).
  Qed.

  Definition src_zero_is_quiet_time : Prop :=
    ltac:(body_of (fun s : S.statement_zero_is_quiet_time => s Job jaR costR pR PStateR schedR arrR)).
  Definition tgt_zero_is_quiet_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_QuietTime_zero_is_quiet_time
      Job dJ jaL costL pL PStateL schedL arrL)).
  Theorem zero_is_quiet_time_correspondence : PropSPropRel src_zero_is_quiet_time tgt_zero_is_quiet_time.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    exact (fqt_quiet_time_related j _ _ (sub_nat_rel_canonical O)).
  Qed.

  Definition src_no_carry_in_implies_quiet_time : Prop :=
    ltac:(body_of (fun s : S.statement_no_carry_in_implies_quiet_time => s Job jaR costR pR PStateR schedR arrR)).
  Definition tgt_no_carry_in_implies_quiet_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_QuietTime_no_carry_in_implies_quiet_time
      Job dJ jaL costL pL PStateL schedL arrL)).
  Theorem no_carry_in_implies_quiet_time_correspondence :
    PropSPropRel src_no_carry_in_implies_quiet_time tgt_no_carry_in_implies_quiet_time.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (no_carry_in_correspondence Job jaR jaL Hja costR costL Hcost PStateR PStateL R
        arrR arrL Harr schedR schedL Hsched tR tL Ht)|].
    exact (fqt_quiet_time_related j _ _ Ht).
  Qed.

  Definition src_busy_interval_prefix_no_quiet_time : Prop :=
    ltac:(body_of (fun s : S.statement_busy_interval_prefix_no_quiet_time => s Job jaR costR pR PStateR schedR arrR)).
  Definition tgt_busy_interval_prefix_no_quiet_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_QuietTime_busy_interval_prefix_no_quiet_time
      Job dJ jaL costL pL PStateL schedL arrL)).
  Theorem busy_interval_prefix_no_quiet_time_correspondence :
    PropSPropRel src_busy_interval_prefix_no_quiet_time tgt_busy_interval_prefix_no_quiet_time.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply ar_imp_correspondence; [exact (fqt_busy_interval_prefix_related j _ _ _ _ H1 H2)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (fqt_window_related _ _ _ _ _ _ H1 Ht H2)|].
    exact (fqt_not_correspondence _ _ (fqt_quiet_time_related j _ _ Ht)).
  Qed.

  Definition src_busy_interval_no_quiet_time : Prop :=
    ltac:(body_of (fun s : S.statement_busy_interval_no_quiet_time => s Job jaR costR pR PStateR schedR arrR)).
  Definition tgt_busy_interval_no_quiet_time : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_QuietTime_busy_interval_no_quiet_time
      Job dJ jaL costL pL PStateL schedL arrL)).
  Theorem busy_interval_no_quiet_time_correspondence :
    PropSPropRel src_busy_interval_no_quiet_time tgt_busy_interval_no_quiet_time.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply ar_imp_correspondence; [exact (fqt_busy_interval_related j _ _ _ _ H1 H2)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (fqt_window_related _ _ _ _ _ _ H1 Ht H2)|].
    exact (fqt_not_correspondence _ _ (fqt_quiet_time_related j _ _ Ht)).
  Qed.
End Facts.
