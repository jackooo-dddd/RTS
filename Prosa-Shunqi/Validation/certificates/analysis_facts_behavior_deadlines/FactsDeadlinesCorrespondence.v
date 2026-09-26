From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsDeadlinesSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsDeadlines ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedFactsDeadlines.
Module S := FactsDeadlinesSemanticSource.FactsDeadlinesSemanticSource.

(** Statement correspondences for [analysis/facts/behavior/deadlines.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.
    Inputs: [job_cost] by [SvcJobCostRel], [JobDeadline] pointwise by
    [SubNatRel], processor states and schedules by the accepted two-sided
    [SvcProcessorStateRel]/[SvcScheduleRel].  Service, [completed_by],
    [scheduled_at] and [job_meets_deadline] are replayed from the accepted
    completion/schedulability certificates.  No source or target theorem is
    used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fdl_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [HPQ HQP]. exact (I.Iff_intro PL QL
      (fun p => prop_to_sprop _ _ HQ (HPQ (sprop_to_prop _ _ HP p)))
      (fun q => prop_to_sprop _ _ HP (HQP (sprop_to_prop _ _ HQ q)))).
  - intro H. apply strictly_inhabits. split.
    + intro p. apply (sprop_to_prop _ _ HQ).
      exact (I.Iff_mp PL QL H (prop_to_sprop _ _ HP p)).
    + intro q. apply (sprop_to_prop _ _ HP).
      exact (I.Iff_mpr PL QL H (prop_to_sprop _ _ HQ q)).
Qed.

Section Deadlines.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable dlR : prosa.behavior.job.JobDeadline Job.
  Variable dlL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
  Hypothesis Hdl : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
      (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Section Sched.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Lemma fdl_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.scheduled_at.
      cbn [I.Prosa_Behavior_Service_scheduled_at].
      exact (svc_scheduled_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
    Qed.

    Lemma fdl_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.service_at.
      cbn [I.Prosa_Behavior_Service_service_at].
      exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
    Qed.

    Lemma fdl_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.service.
      cbn [I.Prosa_Behavior_Service_service].
      have Hsum := svc_interval_sum_related O tR Lean.Nat_zero tL
        (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
        (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j t)
        (sub_nat_rel_canonical O) Ht (fun xR xL Hx => fdl_service_at_related j xR xL Hx).
      change (SubNatRel
        (@prosa.behavior.service.service_during Job PStateR schedR j O tR)
        (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
          Job dJ PStateL schedL j Lean.Nat_zero tL)) in Hsum.
      exact Hsum.
    Qed.

    Lemma fdl_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR schedR costR j tR)
        (I.Prosa_Behavior_Service_completed_by Job dJ PStateL schedL costL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.completed_by.
      cbn [I.Prosa_Behavior_Service_completed_by].
      exact (svc_decide_le_related _ _ _ _ (Hcost j) (fdl_service_related j tR tL Ht)).
    Qed.

    Lemma fdl_job_meets_deadline_related (j : Job) :
      SvcBoolRel (@prosa.behavior.service.job_meets_deadline Job PStateR schedR costR dlR j)
        (I.Prosa_Behavior_Service_job_meets_deadline Job dJ PStateL schedL costL dlL j).
    Proof.
      unfold prosa.behavior.service.job_meets_deadline.
      cbn [I.Prosa_Behavior_Service_job_meets_deadline].
      exact (fdl_completed_by_related j _ _ (Hdl j)).
    Qed.

    Lemma fdl_completed_jobs_dont_execute_related :
      PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PStateR schedR costR)
        (I.Prosa_Behavior_Ready_completed_jobs_dont_execute Job dJ PStateL schedL costL).
    Proof.
      unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (fdl_scheduled_at_related j tR tL Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _ (fdl_service_related j tR tL Ht) (Hcost j)).
    Qed.

    Definition src_incomplete_implies_later_deadline : Prop :=
      ltac:(body_of (fun s : S.statement_incomplete_implies_later_deadline =>
        s Job costR dlR PStateR schedR)).
    Definition tgt_incomplete_implies_later_deadline : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Deadlines_incomplete_implies_later_deadline
        Job dJ costL dlL PStateL schedL)).

    Theorem incomplete_implies_later_deadline_correspondence :
      PropSPropRel src_incomplete_implies_later_deadline tgt_incomplete_implies_later_deadline.
    Proof.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (fdl_job_meets_deadline_related j))|].
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _
          (svc_bool_not_related _ _ (fdl_completed_by_related j tR tL Ht)))|].
      exact (sub_nat_lt_correspondence _ _ _ _ Ht (Hdl j)).
    Qed.

    Definition src_incomplete_implies_scheduled_later : Prop :=
      ltac:(body_of (fun s : S.statement_incomplete_implies_scheduled_later =>
        s Job costR dlR PStateR schedR)).
    Definition tgt_incomplete_implies_scheduled_later : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Deadlines_incomplete_implies_scheduled_later
        Job dJ costL dlL PStateL schedL)).

    Theorem incomplete_implies_scheduled_later_correspondence :
      PropSPropRel src_incomplete_implies_scheduled_later tgt_incomplete_implies_scheduled_later.
    Proof.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (fdl_job_meets_deadline_related j))|].
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _
          (svc_bool_not_related _ _ (fdl_completed_by_related j tR tL Ht)))|].
      apply ar_exists_nat_correspondence. intros uR uL Hu.
      apply ar_and_correspondence.
      - exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
          (ar_decide_le_related _ _ _ _ Ht Hu) (ar_decide_lt_related _ _ _ _ Hu (Hdl j)))).
      - exact (svc_bool_truth_correspondence _ _ (fdl_scheduled_at_related j uR uL Hu)).
    Qed.

    Definition src_scheduled_at_implies_later_deadline : Prop :=
      ltac:(body_of (fun s : S.statement_scheduled_at_implies_later_deadline =>
        s Job costR dlR PStateR schedR)).
    Definition tgt_scheduled_at_implies_later_deadline : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Deadlines_scheduled_at_implies_later_deadline
        Job dJ costL dlL PStateL schedL)).

    Theorem scheduled_at_implies_later_deadline_correspondence :
      PropSPropRel src_scheduled_at_implies_later_deadline tgt_scheduled_at_implies_later_deadline.
    Proof.
      apply ar_imp_correspondence; [exact fdl_completed_jobs_dont_execute_related|].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (fdl_job_meets_deadline_related j))|].
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (fdl_scheduled_at_related j tR tL Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _ Ht (Hdl j)).
    Qed.
  End Sched.

  Variable schedR schedR' : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL schedL' : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Hypothesis Hsched' : SvcScheduleRel Job PStateR PStateL R schedR' schedL'.

  Definition src_service_invariant_implies_deadline_met : Prop :=
    ltac:(body_of (fun s : S.statement_service_invariant_implies_deadline_met =>
      s Job costR dlR PStateR schedR schedR')).
  Definition tgt_service_invariant_implies_deadline_met : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Deadlines_service_invariant_implies_deadline_met
      Job dJ costL dlL PStateL schedL schedL')).

  Theorem service_invariant_implies_deadline_met_correspondence :
    PropSPropRel src_service_invariant_implies_deadline_met tgt_service_invariant_implies_deadline_met.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence.
    - exact (sub_nat_eq_correspondence _ _ _ _
        (fdl_service_related schedR schedL Hsched j _ _ (Hdl j))
        (fdl_service_related schedR' schedL' Hsched' j _ _ (Hdl j))).
    - apply fdl_iff_correspondence.
      + exact (svc_bool_truth_correspondence _ _ (fdl_job_meets_deadline_related schedR schedL Hsched j)).
      + exact (svc_bool_truth_correspondence _ _ (fdl_job_meets_deadline_related schedR' schedL' Hsched' j)).
  Qed.
End Deadlines.
