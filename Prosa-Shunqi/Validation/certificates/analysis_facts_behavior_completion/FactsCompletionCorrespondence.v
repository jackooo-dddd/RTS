From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import FactsCompletionSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsCompletion ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedFactsCompletion.
Module S := FactsCompletionSemanticSource.FactsCompletionSemanticSource.

(** Statement correspondences for [analysis/facts/behavior/completion.v].

    Source side: the extracted statement [S.statement_X] specialised at its
    leading inputs (job type, job cost / arrival / readiness classes,
    processor state, schedule, job, as they occur); target side: the type of
    the imported Lean theorem at related inputs ([SvcJobCostRel],
    [SvcJobArrivalRel], two-sided [SvcProcessorStateRel] and [SvcScheduleRel],
    readiness pointwise over related schedules).  Later binders are covered in
    both directions: Nats, jobs (identity), processor states (through the
    state conversion of [SvcProcessorStateRel]), job-arrival classes
    (accepted import/export totals), arrival sequences, and schedules
    (functionally, through the state conversion with its roundtrips).  All
    operations are the accepted Service / ArrivalSequence proofs
    re-instantiated at this artifact; no source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators (proved) *)

Lemma fc_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Lemma fc_iff_correspondence (P Q : Prop) (PL QL : SProp) :
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

Lemma fc_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma fc_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma fc_bool_eq_correspondence (bR cR : bool) (bL cL : I.Bool) :
  SvcBoolRel bR bL -> SvcBoolRel cR cL -> PropSPropRel (bR = cR) (Lean.eq bL cL).
Proof.
  intros Hb Hc. apply prop_sprop_rel_intro.
  - intro E. destruct E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hb) Hc).
  - intro E. apply strictly_inhabits.
    have EL := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hb (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hc))).
    destruct bR, cR; cbn in EL; solve [reflexivity | discriminate EL].
Qed.

Lemma fc_succ_related (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> SubNatRel nR.+1 (svc_target_add nL svc_target_one).
Proof.
  intro Hn. have H := svc_target_add_related nR nL 1 svc_target_one Hn (sub_nat_rel_canonical 1).
  rewrite addn1 in H. exact H.
Qed.

Section Completion.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let cover_state :=
    fc_forall_cover_sprop _ _ (svc_ps_state_rel Job PStateR PStateL R)
      (svc_ps_state_to_target Job PStateR PStateL R) (svc_ps_state_to_source Job PStateR PStateL R)
      (svc_ps_state_rel_canonical Job PStateR PStateL R) (svc_ps_state_rel_surjective Job PStateR PStateL R).

  Let cover_job_arrival :=
    fc_forall_cover_sprop _ _ (SvcJobArrivalRel Job)
      (svc_import_job_arrival Job) (svc_export_job_arrival Job)
      (svc_job_arrival_import Job) (svc_job_arrival_export Job).

  (** *** Schedule-level operations *)

  Section Sched.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Lemma fc_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.scheduled_at.
      cbn [I.Prosa_Behavior_Service_scheduled_at].
      exact (svc_scheduled_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
    Qed.

    Lemma fc_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.service_at.
      cbn [I.Prosa_Behavior_Service_service_at].
      exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
    Qed.

    Lemma fc_service_during_related (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
        (I.Prosa_Behavior_Service_service_during Job dJ PStateL schedL j t1L t2L).
    Proof.
      intros Ht1 Ht2.
      have Hsum := svc_interval_sum_related t1R t2R t1L t2L
        (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
        (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j t)
        Ht1 Ht2 (fun tR tL Ht => fc_service_at_related j tR tL Ht).
      change (SubNatRel
        (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
        (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
          Job dJ PStateL schedL j t1L t2L)) in Hsum.
      exact Hsum.
    Qed.

    Lemma fc_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.service.
      cbn [I.Prosa_Behavior_Service_service].
      exact (fc_service_during_related j O tR Lean.Nat_zero tL (sub_nat_rel_canonical O) Ht).
    Qed.

    Lemma fc_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR schedR costR j tR)
        (I.Prosa_Behavior_Service_completed_by Job dJ PStateL schedL costL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.completed_by.
      cbn [I.Prosa_Behavior_Service_completed_by].
      exact (svc_decide_le_related _ _ _ _ (Hcost j) (fc_service_related j tR tL Ht)).
    Qed.

    Lemma fc_remaining_cost_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.remaining_cost Job PStateR schedR costR j tR)
        (I.Prosa_Behavior_Service_remaining_cost Job dJ PStateL schedL costL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.remaining_cost.
      cbn [I.Prosa_Behavior_Service_remaining_cost].
      exact (svc_target_sub_related _ _ _ _ (Hcost j) (fc_service_related j tR tL Ht)).
    Qed.

    Lemma fc_completed_jobs_dont_execute_related :
      PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PStateR schedR costR)
        (I.Prosa_Behavior_Ready_completed_jobs_dont_execute Job dJ PStateL schedL costL).
    Proof.
      unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fc_scheduled_at_related j tR tL Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _ (fc_service_related j tR tL Ht) (Hcost j)).
    Qed.

    Section Arrival.
      Variable jaR : prosa.behavior.job.JobArrival Job.
      Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
      Hypothesis Hja : SvcJobArrivalRel Job jaR jaL.

      Lemma fc_has_arrived_related (j : Job) (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        SvcBoolRel (@prosa.behavior.arrival_sequence.has_arrived Job jaR j tR)
          (I.Prosa_Behavior_Arrival_sequence_has_arrived Job dJ jaL j tL).
      Proof.
        intro Ht. unfold prosa.behavior.arrival_sequence.has_arrived.
        cbn [I.Prosa_Behavior_Arrival_sequence_has_arrived].
        exact (svc_decide_le_related _ _ _ _ (Hja j) Ht).
      Qed.

      Lemma fc_jobs_must_arrive_related :
        PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PStateR schedR)
          (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job dJ jaL PStateL schedL).
      Proof.
        unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
        cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fc_scheduled_at_related j tR tL Ht))|].
        exact (svc_bool_truth_correspondence _ _ (fc_has_arrived_related j tR tL Ht)).
      Qed.

      Lemma fc_pending_related (j : Job) (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        SvcBoolRel (@prosa.behavior.service.pending Job PStateR schedR costR jaR j tR)
          (I.Prosa_Behavior_Service_pending Job dJ PStateL schedL costL jaL j tL).
      Proof.
        intro Ht. unfold prosa.behavior.service.pending.
        cbn [I.Prosa_Behavior_Service_pending].
        exact (svc_bool_and_related _ _ _ _ (fc_has_arrived_related j tR tL Ht)
          (svc_bool_not_related _ _ (fc_completed_by_related j tR tL Ht))).
      Qed.

      Lemma fc_pending_earlier_and_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        SvcBoolRel (@prosa.behavior.service.pending_earlier_and_at Job PStateR schedR costR jaR j tR)
          (I.Prosa_Behavior_Service_pending_earlier_and_at Job dJ PStateL schedL costL jaL j tL).
      Proof.
        intro Ht. unfold prosa.behavior.service.pending_earlier_and_at,
          prosa.behavior.arrival_sequence.arrived_before.
        cbn [I.Prosa_Behavior_Service_pending_earlier_and_at I.Prosa_Behavior_Arrival_sequence_arrived_before].
        exact (svc_bool_and_related _ _ _ _ (svc_decide_lt_related _ _ _ _ (Hja j) Ht)
          (svc_bool_not_related _ _ (fc_completed_by_related j tR tL Ht))).
      Qed.
    End Arrival.

    (** **** Statements with a fixed schedule and job *)

    Section Job.
      Variable j : Job.

      Definition src_completion_monotonic : Prop :=
        ltac:(body_of (fun s : S.statement_completion_monotonic => s Job costR PStateR schedR j)).
      Definition tgt_completion_monotonic : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_completion_monotonic
          Job dJ costL PStateL schedL j)).
      Theorem completion_monotonic_correspondence :
        PropSPropRel src_completion_monotonic tgt_completion_monotonic.
      Proof.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_forall_nat_correspondence. intros uR uL Hu.
        apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Hu)|].
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fc_completed_by_related j _ _ Ht))|].
        exact (svc_bool_truth_correspondence _ _ (fc_completed_by_related j _ _ Hu)).
      Qed.

      Definition src_incompletion_monotonic : Prop :=
        ltac:(body_of (fun s : S.statement_incompletion_monotonic => s Job costR PStateR schedR j)).
      Definition tgt_incompletion_monotonic : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_incompletion_monotonic
          Job dJ costL PStateL schedL j)).
      Theorem incompletion_monotonic_correspondence :
        PropSPropRel src_incompletion_monotonic tgt_incompletion_monotonic.
      Proof.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_forall_nat_correspondence. intros uR uL Hu.
        apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Hu)|].
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fc_completed_by_related j _ _ Hu)))|].
        exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fc_completed_by_related j _ _ Ht))).
      Qed.

      Definition src_less_service_than_cost_is_incomplete : Prop :=
        ltac:(body_of (fun s : S.statement_less_service_than_cost_is_incomplete => s Job costR PStateR schedR j)).
      Definition tgt_less_service_than_cost_is_incomplete : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_less_service_than_cost_is_incomplete
          Job dJ costL PStateL schedL j)).
      Theorem less_service_than_cost_is_incomplete_correspondence :
        PropSPropRel src_less_service_than_cost_is_incomplete tgt_less_service_than_cost_is_incomplete.
      Proof.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply fc_iff_correspondence.
        - exact (sub_nat_lt_correspondence _ _ _ _ (fc_service_related j _ _ Ht) (Hcost j)).
        - exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fc_completed_by_related j _ _ Ht))).
      Qed.

      Definition src_incomplete_is_positive_remaining_cost : Prop :=
        ltac:(body_of (fun s : S.statement_incomplete_is_positive_remaining_cost => s Job costR PStateR schedR j)).
      Definition tgt_incomplete_is_positive_remaining_cost : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_incomplete_is_positive_remaining_cost
          Job dJ costL PStateL schedL j)).
      Theorem incomplete_is_positive_remaining_cost_correspondence :
        PropSPropRel src_incomplete_is_positive_remaining_cost tgt_incomplete_is_positive_remaining_cost.
      Proof.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply fc_iff_correspondence.
        - exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fc_completed_by_related j _ _ Ht))).
        - exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (fc_remaining_cost_related j _ _ Ht)).
      Qed.

      Definition src_incomplete_implies_positive_cost : Prop :=
        ltac:(body_of (fun s : S.statement_incomplete_implies_positive_cost => s Job costR PStateR schedR j)).
      Definition tgt_incomplete_implies_positive_cost : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_incomplete_implies_positive_cost
          Job dJ costL PStateL schedL j)).
      Theorem incomplete_implies_positive_cost_correspondence :
        PropSPropRel src_incomplete_implies_positive_cost tgt_incomplete_implies_positive_cost.
      Proof.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fc_completed_by_related j _ _ Ht)))|].
        unfold prosa.model.job.properties.job_cost_positive.
        cbn [I.Prosa_Model_Job_Properties_job_cost_positive].
        exact (svc_bool_truth_correspondence _ _
          (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))).
      Qed.

      Definition src_scheduled_implies_positive_cost : Prop :=
        ltac:(body_of (fun s : S.statement_scheduled_implies_positive_cost => s Job costR PStateR schedR j)).
      Definition tgt_scheduled_implies_positive_cost : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_scheduled_implies_positive_cost
          Job dJ costL PStateL schedL j)).
      Theorem scheduled_implies_positive_cost_correspondence :
        PropSPropRel src_scheduled_implies_positive_cost tgt_scheduled_implies_positive_cost.
      Proof.
        apply ar_imp_correspondence; [exact fc_completed_jobs_dont_execute_related|].
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fc_scheduled_at_related j _ _ Ht))|].
        exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j)).
      Qed.

      Definition src_service_lt_cost : Prop :=
        ltac:(body_of (fun s : S.statement_service_lt_cost => s Job costR PStateR schedR j)).
      Definition tgt_service_lt_cost : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_service_lt_cost
          Job dJ costL PStateL schedL j)).
      Theorem service_lt_cost_correspondence : PropSPropRel src_service_lt_cost tgt_service_lt_cost.
      Proof.
        apply ar_imp_correspondence; [exact fc_completed_jobs_dont_execute_related|].
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fc_scheduled_at_related j _ _ Ht))|].
        exact (sub_nat_lt_correspondence _ _ _ _ (fc_service_related j _ _ Ht) (Hcost j)).
      Qed.

      Definition src_serviced_implies_positive_remaining_cost : Prop :=
        ltac:(body_of (fun s : S.statement_serviced_implies_positive_remaining_cost => s Job costR PStateR schedR j)).
      Definition tgt_serviced_implies_positive_remaining_cost : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_serviced_implies_positive_remaining_cost
          Job dJ costL PStateL schedL j)).
      Theorem serviced_implies_positive_remaining_cost_correspondence :
        PropSPropRel src_serviced_implies_positive_remaining_cost tgt_serviced_implies_positive_remaining_cost.
      Proof.
        apply ar_imp_correspondence; [exact fc_completed_jobs_dont_execute_related|].
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence;
          [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (fc_service_at_related j _ _ Ht))|].
        exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (fc_remaining_cost_related j _ _ Ht)).
      Qed.

      Definition fc_ideal_progress_rel :
        PropSPropRel (@prosa.model.processor.platform_properties.ideal_progress_proc_model Job PStateR)
          (I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job dJ PStateL).
      Proof.
        unfold prosa.model.processor.platform_properties.ideal_progress_proc_model.
        cbn [I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model].
        apply ar_forall_identity_correspondence. intro j'.
        apply cover_state. intros sR sL Hs.
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (svc_scheduled_in_related Job PStateR PStateL R j' sR sL Hs))|].
        exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O)
          (svc_service_in_related Job PStateR PStateL R j' sR sL Hs)).
      Defined.

      Definition src_scheduled_implies_positive_remaining_cost : Prop :=
        ltac:(body_of (fun s : S.statement_scheduled_implies_positive_remaining_cost => s Job costR PStateR schedR j)).
      Definition tgt_scheduled_implies_positive_remaining_cost : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_scheduled_implies_positive_remaining_cost
          Job dJ costL PStateL schedL j)).
      Theorem scheduled_implies_positive_remaining_cost_correspondence :
        PropSPropRel src_scheduled_implies_positive_remaining_cost tgt_scheduled_implies_positive_remaining_cost.
      Proof.
        apply ar_imp_correspondence; [exact fc_completed_jobs_dont_execute_related|].
        apply ar_imp_correspondence; [exact fc_ideal_progress_rel|].
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fc_scheduled_at_related j _ _ Ht))|].
        exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (fc_remaining_cost_related j _ _ Ht)).
      Qed.

      Definition src_scheduled_implies_not_completed : Prop :=
        ltac:(body_of (fun s : S.statement_scheduled_implies_not_completed => s Job costR PStateR schedR j)).
      Definition tgt_scheduled_implies_not_completed : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_scheduled_implies_not_completed
          Job dJ costL PStateL schedL j)).
      Theorem scheduled_implies_not_completed_correspondence :
        PropSPropRel src_scheduled_implies_not_completed tgt_scheduled_implies_not_completed.
      Proof.
        apply ar_imp_correspondence; [exact fc_completed_jobs_dont_execute_related|].
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fc_scheduled_at_related j _ _ Ht))|].
        exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fc_completed_by_related j _ _ Ht))).
      Qed.

      Definition src_not_scheduled_remains_incomplete : Prop :=
        ltac:(body_of (fun s : S.statement_not_scheduled_remains_incomplete => s Job costR PStateR schedR j)).
      Definition tgt_not_scheduled_remains_incomplete : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_not_scheduled_remains_incomplete
          Job dJ costL PStateL schedL j)).
      Theorem not_scheduled_remains_incomplete_correspondence :
        PropSPropRel src_not_scheduled_remains_incomplete tgt_not_scheduled_remains_incomplete.
      Proof.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fc_completed_by_related j _ _ Ht)))|].
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fc_scheduled_at_related j _ _ Ht)))|].
        exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _
          (fc_completed_by_related j _ _ (fc_succ_related _ _ Ht)))).
      Qed.

      Definition src_completed_implies_not_scheduled : Prop :=
        ltac:(body_of (fun s : S.statement_completed_implies_not_scheduled => s Job costR PStateR schedR j)).
      Definition tgt_completed_implies_not_scheduled : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_completed_implies_not_scheduled
          Job dJ costL PStateL schedL j)).
      Theorem completed_implies_not_scheduled_correspondence :
        PropSPropRel src_completed_implies_not_scheduled tgt_completed_implies_not_scheduled.
      Proof.
        apply ar_imp_correspondence; [exact fc_completed_jobs_dont_execute_related|].
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fc_completed_by_related j _ _ Ht))|].
        exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fc_scheduled_at_related j _ _ Ht))).
      Qed.

      Section WithArrival.
        Variable jaR : prosa.behavior.job.JobArrival Job.
        Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
        Hypothesis Hja : SvcJobArrivalRel Job jaR jaL.

        Definition src_completed_on_arrival_implies_zero_cost : Prop :=
          ltac:(body_of (fun s : S.statement_completed_on_arrival_implies_zero_cost =>
            s Job costR jaR PStateR schedR j)).
        Definition tgt_completed_on_arrival_implies_zero_cost : SProp :=
          ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_completed_on_arrival_implies_zero_cost
            Job dJ costL jaL PStateL schedL j)).
        Theorem completed_on_arrival_implies_zero_cost_correspondence :
          PropSPropRel src_completed_on_arrival_implies_zero_cost tgt_completed_on_arrival_implies_zero_cost.
        Proof.
          apply ar_imp_correspondence; [exact (fc_jobs_must_arrive_related jaR jaL Hja)|].
          apply ar_imp_correspondence;
            [exact (svc_bool_truth_correspondence _ _ (fc_completed_by_related j _ _ (Hja j)))|].
          exact (sub_nat_eq_correspondence _ _ _ _ (Hcost j) (sub_nat_rel_canonical O)).
        Qed.

        Definition src_not_pending_earlier_and_at_0 : Prop :=
          ltac:(body_of (fun s : S.statement_not_pending_earlier_and_at_0 => s Job costR jaR PStateR schedR j)).
        Definition tgt_not_pending_earlier_and_at_0 : SProp :=
          ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_not_pending_earlier_and_at_0
            Job dJ costL jaL PStateL schedL j)).
        Theorem not_pending_earlier_and_at_0_correspondence :
          PropSPropRel src_not_pending_earlier_and_at_0 tgt_not_pending_earlier_and_at_0.
        Proof.
          exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _
            (fc_pending_earlier_and_at_related jaR jaL Hja j _ _ (sub_nat_rel_canonical O)))).
        Qed.

        Definition src_completed_implies_scheduled_before : Prop :=
          ltac:(body_of (fun s : S.statement_completed_implies_scheduled_before =>
            s Job costR jaR PStateR schedR j)).
        Definition tgt_completed_implies_scheduled_before : SProp :=
          ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_completed_implies_scheduled_before
            Job dJ costL jaL PStateL schedL j)).
        Theorem completed_implies_scheduled_before_correspondence :
          PropSPropRel src_completed_implies_scheduled_before tgt_completed_implies_scheduled_before.
        Proof.
          apply ar_imp_correspondence;
            [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))|].
          apply ar_imp_correspondence; [exact (fc_jobs_must_arrive_related jaR jaL Hja)|].
          apply ar_forall_nat_correspondence. intros tR tL Ht.
          apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fc_completed_by_related j _ _ Ht))|].
          apply ar_exists_nat_correspondence. intros uR uL Hu.
          apply ar_and_correspondence.
          - exact (svc_bool_truth_correspondence _ _ (svc_bool_and_related _ _ _ _
              (svc_decide_le_related _ _ _ _ (Hja j) Hu) (svc_decide_lt_related _ _ _ _ Hu Ht))).
          - exact (svc_bool_truth_correspondence _ _ (fc_scheduled_at_related j _ _ Hu)).
        Qed.

        Definition src_job_pending_at_arrival : Prop :=
          ltac:(body_of (fun s : S.statement_job_pending_at_arrival => s Job costR jaR PStateR schedR j)).
        Definition tgt_job_pending_at_arrival : SProp :=
          ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_job_pending_at_arrival
            Job dJ costL jaL PStateL schedL j)).
        Theorem job_pending_at_arrival_correspondence :
          PropSPropRel src_job_pending_at_arrival tgt_job_pending_at_arrival.
        Proof.
          apply ar_imp_correspondence;
            [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))|].
          apply ar_imp_correspondence; [exact (fc_jobs_must_arrive_related jaR jaL Hja)|].
          exact (svc_bool_truth_correspondence _ _ (fc_pending_related jaR jaL Hja j _ _ (Hja j))).
        Qed.

        Definition src_has_arrived_scheduled : Prop :=
          ltac:(body_of (fun s : S.statement_has_arrived_scheduled => s Job PStateR schedR j jaR)).
        Definition tgt_has_arrived_scheduled : SProp :=
          ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_has_arrived_scheduled
            Job dJ PStateL schedL j jaL)).
        Theorem has_arrived_scheduled_correspondence :
          PropSPropRel src_has_arrived_scheduled tgt_has_arrived_scheduled.
        Proof.
          apply ar_imp_correspondence; [exact (fc_jobs_must_arrive_related jaR jaL Hja)|].
          apply ar_forall_nat_correspondence. intros tR tL Ht.
          apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fc_scheduled_at_related j _ _ Ht))|].
          exact (svc_bool_truth_correspondence _ _ (fc_has_arrived_related jaR jaL Hja j _ _ Ht)).
        Qed.
      End WithArrival.
    End Job.

    (** **** Statements quantifying over the job after hypotheses *)

    Definition fc_unit_service_rel :
      PropSPropRel (@prosa.model.processor.platform_properties.unit_service_proc_model Job PStateR)
        (I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job dJ PStateL).
    Proof.
      unfold prosa.model.processor.platform_properties.unit_service_proc_model.
      cbn [I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model].
      apply ar_forall_identity_correspondence. intro j'.
      apply cover_state. intros sR sL Hs.
      exact (sub_nat_le_correspondence _ _ _ _ (svc_service_in_related Job PStateR PStateL R j' sR sL Hs)
        (sub_nat_rel_canonical 1)).
    Defined.

    Definition src_service_at_most_cost : Prop :=
      ltac:(body_of (fun s : S.statement_service_at_most_cost => s Job costR PStateR schedR)).
    Definition tgt_service_at_most_cost : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_service_at_most_cost
        Job dJ costL PStateL schedL)).
    Theorem service_at_most_cost_correspondence : PropSPropRel src_service_at_most_cost tgt_service_at_most_cost.
    Proof.
      apply ar_imp_correspondence; [exact fc_completed_jobs_dont_execute_related|].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact fc_unit_service_rel|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      exact (sub_nat_le_correspondence _ _ _ _ (fc_service_related j _ _ Ht) (Hcost j)).
    Qed.

    Definition src_service_cost_invariant : Prop :=
      ltac:(body_of (fun s : S.statement_service_cost_invariant => s Job costR PStateR schedR)).
    Definition tgt_service_cost_invariant : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_service_cost_invariant
        Job dJ costL PStateL schedL)).
    Theorem service_cost_invariant_correspondence : PropSPropRel src_service_cost_invariant tgt_service_cost_invariant.
    Proof.
      apply ar_imp_correspondence; [exact fc_completed_jobs_dont_execute_related|].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact fc_unit_service_rel|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      exact (sub_nat_eq_correspondence _ _ _ _
        (svc_target_add_related _ _ _ _ (fc_service_related j _ _ Ht) (fc_remaining_cost_related j _ _ Ht))
        (Hcost j)).
    Qed.

    Definition src_cumulative_service_le_job_cost : Prop :=
      ltac:(body_of (fun s : S.statement_cumulative_service_le_job_cost => s Job costR PStateR schedR)).
    Definition tgt_cumulative_service_le_job_cost : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_cumulative_service_le_job_cost
        Job dJ costL PStateL schedL)).
    Theorem cumulative_service_le_job_cost_correspondence :
      PropSPropRel src_cumulative_service_le_job_cost tgt_cumulative_service_le_job_cost.
    Proof.
      apply ar_imp_correspondence; [exact fc_completed_jobs_dont_execute_related|].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact fc_unit_service_rel|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_nat_correspondence. intros uR uL Hu.
      exact (sub_nat_le_correspondence _ _ _ _ (fc_service_during_related j _ _ _ _ Ht Hu) (Hcost j)).
    Qed.

    Definition src_job_doesnt_complete_before_remaining_cost : Prop :=
      ltac:(body_of (fun s : S.statement_job_doesnt_complete_before_remaining_cost => s Job costR PStateR schedR)).
    Definition tgt_job_doesnt_complete_before_remaining_cost : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_job_doesnt_complete_before_remaining_cost
        Job dJ costL PStateL schedL)).
    Theorem job_doesnt_complete_before_remaining_cost_correspondence :
      PropSPropRel src_job_doesnt_complete_before_remaining_cost tgt_job_doesnt_complete_before_remaining_cost.
    Proof.
      apply ar_imp_correspondence; [exact fc_completed_jobs_dont_execute_related|].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact fc_unit_service_rel|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fc_completed_by_related j _ _ Ht)))|].
      exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fc_completed_by_related j _ _
        (svc_target_sub_related _ _ _ _
          (svc_target_add_related _ _ _ _ Ht (fc_remaining_cost_related j _ _ Ht))
          (sub_nat_rel_canonical 1))))).
    Qed.

    Definition src_scheduled_implies_pending : Prop :=
      ltac:(body_of (fun s : S.statement_scheduled_implies_pending => s Job costR PStateR schedR)).
    Definition tgt_scheduled_implies_pending : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_scheduled_implies_pending
        Job dJ costL PStateL schedL)).
    Theorem scheduled_implies_pending_correspondence :
      PropSPropRel src_scheduled_implies_pending tgt_scheduled_implies_pending.
    Proof.
      apply ar_imp_correspondence; [exact fc_completed_jobs_dont_execute_related|].
      apply ar_forall_identity_correspondence. intro j.
      apply cover_job_arrival. intros jaR jaL Hja.
      apply ar_imp_correspondence; [exact (fc_jobs_must_arrive_related jaR jaL Hja)|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fc_scheduled_at_related j _ _ Ht))|].
      exact (svc_bool_truth_correspondence _ _ (fc_pending_related jaR jaL Hja j _ _ Ht)).
    Qed.

    (** **** Readiness *)

    Section Ready.
      Variable jaR : prosa.behavior.job.JobArrival Job.
      Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
      Hypothesis Hja : SvcJobArrivalRel Job jaR jaL.
      Variable readyR : @prosa.behavior.ready.JobReady Job PStateR costR jaR.
      Variable readyL : I.Prosa_Behavior_Ready_JobReady Job dJ PStateL costL jaL.
      Hypothesis Hready : forall (j : Job) (tR : nat) (tL : Lean.Nat), SubNatRel tR tL ->
        SvcBoolRel (@prosa.behavior.ready.job_ready Job PStateR costR jaR readyR schedR j tR)
          (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PStateL costL jaL readyL schedL j tL).

      Lemma fc_jobs_must_be_ready_related :
        PropSPropRel (@prosa.behavior.ready.jobs_must_be_ready_to_execute Job jaR PStateR schedR costR readyR)
          (I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute Job dJ jaL PStateL schedL costL readyL).
      Proof.
        unfold prosa.behavior.ready.jobs_must_be_ready_to_execute.
        cbn [I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fc_scheduled_at_related j _ _ Ht))|].
        exact (svc_bool_truth_correspondence _ _ (Hready j tR tL Ht)).
      Qed.

      Definition src_ready_implies_incomplete : Prop :=
        ltac:(body_of (fun s : S.statement_ready_implies_incomplete => s Job PStateR schedR costR jaR readyR)).
      Definition tgt_ready_implies_incomplete : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_ready_implies_incomplete
          Job dJ PStateL schedL costL jaL readyL)).
      Theorem ready_implies_incomplete_correspondence :
        PropSPropRel src_ready_implies_incomplete tgt_ready_implies_incomplete.
      Proof.
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (Hready j tR tL Ht))|].
        exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fc_completed_by_related j _ _ Ht))).
      Qed.

      Definition src_completed_jobs_are_not_ready : Prop :=
        ltac:(body_of (fun s : S.statement_completed_jobs_are_not_ready => s Job PStateR schedR costR jaR readyR)).
      Definition tgt_completed_jobs_are_not_ready : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_completed_jobs_are_not_ready
          Job dJ PStateL schedL costL jaL readyL)).
      Theorem completed_jobs_are_not_ready_correspondence :
        PropSPropRel src_completed_jobs_are_not_ready tgt_completed_jobs_are_not_ready.
      Proof.
        apply ar_imp_correspondence; [exact fc_jobs_must_be_ready_related|].
        exact fc_completed_jobs_dont_execute_related.
      Qed.

      Definition fc_arrival_sequence_to_source
          (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ) :
          prosa.behavior.arrival_sequence.arrival_sequence Job :=
        fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

      Lemma fc_arrival_sequence_to_source_rel arrL :
        ArArrivalSequenceRel Job (fc_arrival_sequence_to_source arrL) arrL.
      Proof.
        intros tR tL Ht. unfold ArListRel, fc_arrival_sequence_to_source.
        refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
        exact (sub_imported_eq_congr arrL _ _ Ht).
      Qed.

      Definition src_valid_schedule_implies_completed_jobs_dont_execute : Prop :=
        ltac:(body_of (fun s : S.statement_valid_schedule_implies_completed_jobs_dont_execute =>
          s Job PStateR schedR costR jaR readyR)).
      Definition tgt_valid_schedule_implies_completed_jobs_dont_execute : SProp :=
        ltac:(type_of_term
          (@I.Prosa_Analysis_Facts_Behavior_Completion_valid_schedule_implies_completed_jobs_dont_execute
            Job dJ PStateL schedL costL jaL readyL)).
      Theorem valid_schedule_implies_completed_jobs_dont_execute_correspondence :
        PropSPropRel src_valid_schedule_implies_completed_jobs_dont_execute
          tgt_valid_schedule_implies_completed_jobs_dont_execute.
      Proof.
        apply (fc_forall_cover_sprop _ _ (ArArrivalSequenceRel Job)
          (ar_arrival_sequence_to_imported Job) fc_arrival_sequence_to_source
          (ar_arrival_sequence_canonical Job) fc_arrival_sequence_to_source_rel).
        intros arrR arrL Harr.
        apply ar_imp_correspondence; [|exact fc_completed_jobs_dont_execute_related].
        unfold prosa.behavior.ready.valid_schedule, prosa.behavior.ready.jobs_come_from_arrival_sequence.
        cbn [I.Prosa_Behavior_Ready_valid_schedule I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence].
        apply ar_and_correspondence; [|exact fc_jobs_must_be_ready_related].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fc_scheduled_at_related j _ _ Ht))|].
        exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      Qed.
    End Ready.

    Definition src_ideal_progress_completed_jobs : Prop :=
      ltac:(body_of (fun s : S.statement_ideal_progress_completed_jobs => s Job PStateR schedR costR)).
    Definition tgt_ideal_progress_completed_jobs : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_ideal_progress_completed_jobs
        Job dJ PStateL schedL costL)).
    Theorem ideal_progress_completed_jobs_correspondence :
      PropSPropRel src_ideal_progress_completed_jobs tgt_ideal_progress_completed_jobs.
    Proof.
      apply ar_imp_correspondence; [exact fc_ideal_progress_rel|].
      apply ar_imp_correspondence; [|exact fc_completed_jobs_dont_execute_related].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      exact (sub_nat_le_correspondence _ _ _ _ (fc_service_related j _ _ Ht) (Hcost j)).
    Qed.
  End Sched.

  (** *** State-level statements *)

  Definition src_scheduled_implies_serviced (j : Job) : Prop :=
    ltac:(body_of (fun s : S.statement_scheduled_implies_serviced => s Job PStateR j)).
  Definition tgt_scheduled_implies_serviced (j : Job) : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_scheduled_implies_serviced
      Job dJ PStateL j)).
  Theorem scheduled_implies_serviced_correspondence (j : Job) :
    PropSPropRel (src_scheduled_implies_serviced j) (tgt_scheduled_implies_serviced j).
  Proof.
    unfold src_scheduled_implies_serviced, tgt_scheduled_implies_serviced.
    apply ar_imp_correspondence.
    { unfold prosa.model.processor.platform_properties.ideal_progress_proc_model.
      cbn [I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model].
      apply ar_forall_identity_correspondence. intro j'.
      apply cover_state. intros sR sL Hs.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (svc_scheduled_in_related Job PStateR PStateL R j' sR sL Hs))|].
      exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O)
        (svc_service_in_related Job PStateR PStateL R j' sR sL Hs)). }
    apply cover_state. intros sR sL Hs.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (svc_scheduled_in_related Job PStateR PStateL R j sR sL Hs))|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O)
      (svc_service_in_related Job PStateR PStateL R j sR sL Hs)).
  Qed.

  Definition src_unit_service (j : Job) : Prop :=
    ltac:(body_of (fun s : S.statement_unit_service => s Job PStateR j)).
  Definition tgt_unit_service (j : Job) : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_unit_service Job dJ PStateL j)).
  Theorem unit_service_correspondence (j : Job) :
    PropSPropRel (src_unit_service j) (tgt_unit_service j).
  Proof.
    unfold src_unit_service, tgt_unit_service.
    apply ar_imp_correspondence.
    { unfold prosa.model.processor.platform_properties.unit_service_proc_model.
      cbn [I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model].
      apply ar_forall_identity_correspondence. intro j'.
      apply cover_state. intros sR sL Hs.
      exact (sub_nat_le_correspondence _ _ _ _ (svc_service_in_related Job PStateR PStateL R j' sR sL Hs)
        (sub_nat_rel_canonical 1)). }
    apply cover_state. intros sR sL Hs.
    exact (sub_nat_le_correspondence _ _ _ _ (svc_service_in_related Job PStateR PStateL R j sR sL Hs)
      (sub_nat_rel_canonical 1)).
  Qed.

  (** *** Two schedules with an identical prefix *)

  Definition FcScheduleFunRel (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      Lean.eq (svc_ps_state_to_target Job PStateR PStateL R (schedR tR)) (schedL tL).

  Lemma fc_schedule_fun_to_svc schedR schedL :
    FcScheduleFunRel schedR schedL -> SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Proof.
    intros Hf tR tL Ht.
    exact (fc_lean_transport (fun sL => svc_ps_state_rel Job PStateR PStateL R (schedR tR) sL)
      _ _ (Hf tR tL Ht) (svc_ps_state_rel_canonical Job PStateR PStateL R (schedR tR))).
  Qed.

  Definition fc_schedule_to_target (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
      I.Prosa_Behavior_Schedule_schedule Job dJ PStateL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq tL)).

  Definition fc_schedule_to_source (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) :
      @prosa.behavior.schedule.schedule Job PStateR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)).

  Lemma fc_schedule_to_target_rel schedR : FcScheduleFunRel schedR (fc_schedule_to_target schedR).
  Proof.
    intros tR tL Ht. unfold fc_schedule_to_target.
    rewrite (fc_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma fc_schedule_to_source_rel schedL : FcScheduleFunRel (fc_schedule_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. unfold fc_schedule_to_source.
    exact (sub_imported_eq_trans _ _ _
      (svc_ps_state_target_roundtrip Job PStateR PStateL R _)
      (sub_imported_eq_congr schedL _ _ Ht)).
  Qed.

  Let cover_schedule :=
    fc_forall_cover_sprop _ _ FcScheduleFunRel fc_schedule_to_target fc_schedule_to_source
      fc_schedule_to_target_rel fc_schedule_to_source_rel.

  Lemma fc_identical_prefix_correspondence schedR schedR' schedL schedL'
      (Hf : FcScheduleFunRel schedR schedL) (Hf' : FcScheduleFunRel schedR' schedL')
      (hR : nat) (hL : Lean.Nat) (Hh : SubNatRel hR hL) :
    PropSPropRel (@prosa.analysis.definitions.schedule_prefix.identical_prefix
        Job PStateR schedR schedR' hR)
      (I.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix
        Job dJ PStateL schedL schedL' hL).
  Proof.
    unfold prosa.analysis.definitions.schedule_prefix.identical_prefix.
    cbn [I.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Ht Hh)|].
    apply prop_sprop_rel_intro.
    - intro E.
      exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ (Hf tR tL Ht))
        (sub_imported_eq_trans _ _ _
          (coq_eq_to_imported_eq _ _ (f_equal (svc_ps_state_to_target Job PStateR PStateL R) E))
          (Hf' tR tL Ht))).
    - intro EL. apply strictly_inhabits.
      have ET := imported_eq_to_coq_eq _ _
        (sub_imported_eq_trans _ _ _ (Hf tR tL Ht)
          (sub_imported_eq_trans _ _ _ EL (sub_imported_eq_sym _ _ (Hf' tR tL Ht)))).
      have ES := f_equal (svc_ps_state_to_source Job PStateR PStateL R) ET.
      rewrite !(svc_ps_state_source_roundtrip Job PStateR PStateL R) in ES.
      exact ES.
  Qed.

  Definition src_identical_prefix_completed_by : Prop :=
    ltac:(body_of (fun s : S.statement_identical_prefix_completed_by => s Job PStateR costR)).
  Definition tgt_identical_prefix_completed_by : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_identical_prefix_completed_by
      Job dJ PStateL costL)).
  Theorem identical_prefix_completed_by_correspondence :
    PropSPropRel src_identical_prefix_completed_by tgt_identical_prefix_completed_by.
  Proof.
    apply cover_schedule. intros s1R s1L H1.
    apply cover_schedule. intros s2R s2L H2.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_imp_correspondence; [exact (fc_identical_prefix_correspondence _ _ _ _ H1 H2 hR hL Hh)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Hh)|].
    exact (fc_bool_eq_correspondence _ _ _ _
      (fc_completed_by_related s1R s1L (fc_schedule_fun_to_svc _ _ H1) j tR tL Ht)
      (fc_completed_by_related s2R s2L (fc_schedule_fun_to_svc _ _ H2) j tR tL Ht)).
  Qed.

  Section PendingPrefix.
    Variable jaR : prosa.behavior.job.JobArrival Job.
    Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
    Hypothesis Hja : SvcJobArrivalRel Job jaR jaL.

    Definition src_identical_prefix_pending : Prop :=
      ltac:(body_of (fun s : S.statement_identical_prefix_pending => s Job PStateR costR jaR)).
    Definition tgt_identical_prefix_pending : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Completion_identical_prefix_pending
        Job dJ PStateL costL jaL)).
    Theorem identical_prefix_pending_correspondence :
      PropSPropRel src_identical_prefix_pending tgt_identical_prefix_pending.
    Proof.
      apply cover_schedule. intros s1R s1L H1.
      apply cover_schedule. intros s2R s2L H2.
      apply ar_forall_nat_correspondence. intros hR hL Hh.
      apply ar_imp_correspondence; [exact (fc_identical_prefix_correspondence _ _ _ _ H1 H2 hR hL Hh)|].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Hh)|].
      exact (fc_bool_eq_correspondence _ _ _ _
        (fc_pending_related s1R s1L (fc_schedule_fun_to_svc _ _ H1) jaR jaL Hja j tR tL Ht)
        (fc_pending_related s2R s2L (fc_schedule_fun_to_svc _ _ H2) jaR jaL Hja j tR tL Ht)).
    Qed.
  End PendingPrefix.
End Completion.
