From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsEdfWcSemanticSource.
From prosa Require Import model.processor.ideal model.schedule.edf model.readiness.basic
  model.schedule.work_conserving analysis.definitions.schedule_prefix analysis.transform.swap.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsEdfWc ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  IdealUniSchedulerCorrespondence EdfDefinitionsHelpers EdfTransCorrespondence FactsEdfOptCorrespondence.

Module I := ImportedFactsEdfWc.
Module S := FactsEdfWcSemanticSource.FactsEdfWcSemanticSource.
Module ET := EdfTransSemanticSource.EdfTransSemanticSource.
Module SC := SchedulabilitySemanticSource.SchedulabilitySemanticSource.

(** Definition and statement correspondences for [analysis/facts/transform/edf_wc.v].

    Source side: the extracted byte-identical definition block and the
    extracted statements [S.statement_X] specialised at their leading inputs
    (the instances and the arrival sequence); target side: the compiled Lean
    definition and the imported Lean theorem types.  The processor model is
    fixed to the ideal uniprocessor on both sides, with the accepted relations
    and covers of the edf-opt certificate (states by the constructor-preserving
    Option map, schedules pointwise); [job_cost] by [SvcJobCostRel],
    [job_deadline] pointwise by [SubNatRel], [job_arrival] by
    [ArJobArrivalRel], arrival sequences by [ArArrivalSequenceRel]; the
    transformation definitions and [swapped] by the accepted edf-trans
    definition certificates; the readiness model is the source's local basic
    instance on both sides, related through the accepted [pending] relation;
    work conservation and backlog are related here by unfolding.  No source or
    target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Section EdfWc.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.
  Let SchedR := @prosa.behavior.schedule.schedule Job PSR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.

  Variable jcR : prosa.behavior.job.JobCost Job.
  Variable jcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hjc : SvcJobCostRel Job jcR jcL.
  Variable dlR : prosa.behavior.job.JobDeadline Job.
  Variable dlL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
  Hypothesis Hdl : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
      (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let RMR := @prosa.model.readiness.basic.basic_ready_instance Job PSR jaR jcR.
  Let RML := I.Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job dJ PSL jaL jcL.

  (** *** Observations on related schedules *)

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : IdScheduleRel Job sR sL.

    Lemma few_sched_at (j : Job) (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
      PropSPropRel (is_true (@prosa.behavior.service.scheduled_at Job PSR sR j tR))
        (Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL sL j tL) I.Bool_true).
    Proof. exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job sR sL Hs j tR tL Ht)). Qed.

    Lemma few_backlogged_related (j : Job) (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
      SvcBoolRel (@prosa.behavior.ready.backlogged Job PSR jcR jaR RMR sR j tR)
        (I.Prosa_Behavior_Ready_backlogged_inst4 Job dJ PSL jcL jaL RML sL j tL).
    Proof.
      unfold prosa.behavior.ready.backlogged.
      cbn [I.Prosa_Behavior_Ready_backlogged_inst4].
      exact (svc_bool_and_related _ _ _ _
        (pa_pending_related Job jcR jcL Hjc jaR jaL Hja sR sL Hs j tR tL Ht)
        (svc_bool_not_related _ _ (iu_scheduled_at_related Job sR sL Hs j tR tL Ht))).
    Qed.

    Lemma few_wc_rel :
      PropSPropRel (@prosa.model.schedule.work_conserving.work_conserving Job jaR jcR PSR RMR arrR sR)
        (I.Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job dJ jaL jcL PSL RML arrL sL).
    Proof.
      unfold prosa.model.schedule.work_conserving.work_conserving.
      cbn [I.Prosa_Model_Schedule_WorkConserving_work_conserving_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (few_backlogged_related j tR tL Ht))|].
      apply pa_exists_identity_correspondence. intro j'.
      exact (few_sched_at j' tR tL Ht).
    Qed.
  End Sched.

  (** [exists j_other, scheduled_at s j_other t] on related schedules. *)
  Lemma few_exists_sched (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL) (tR : nat) (tL : Lean.Nat)
      (Ht : SubNatRel tR tL) :
    PropSPropRel (exists j_other : Job, is_true (@prosa.behavior.service.scheduled_at Job PSR sR j_other tR))
      (I.Exists Job (fun j_other =>
        Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL sL j_other tL) I.Bool_true)).
  Proof.
    apply pa_exists_identity_correspondence. intro j'.
    exact (few_sched_at _ _ Hs j' tR tL Ht).
  Qed.

  Lemma few_swapped (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
    IdScheduleRel Job (@prosa.analysis.transform.swap.swapped Job PSR sR t1R t2R)
      (I.Prosa_Analysis_Transform_Swap_swapped_inst4 Job dJ PSL sL t1L t2L).
  Proof. exact (fet_swapped_related Job sR sL t1R t2R t1L t2L Hs H1 H2). Qed.

  (** ** Definition correspondence *)

  Theorem scheduled_behavior_premises_correspondence (sR : SchedR) (sL : SchedL) :
    IdScheduleRel Job sR sL ->
    PropSPropRel (@S.scheduled_behavior_premises Job jcR dlR jaR arrR sR)
      (I.Prosa_Analysis_Facts_Transform_EdfWc_scheduled_behavior_premises Job dJ jcL dlL jaL arrL sL).
  Proof.
    intro Hs.
    unfold S.scheduled_behavior_premises.
    cbn [I.Prosa_Analysis_Facts_Transform_EdfWc_scheduled_behavior_premises].
    apply ar_and_correspondence; [exact (feo_must_rel Job jaR jaL Hja _ _ Hs)|].
    apply ar_and_correspondence; [exact (feo_cde_rel Job jcR jcL Hjc _ _ Hs)|].
    apply ar_and_correspondence; [exact (feo_jcf_rel Job _ _ Hs arrR arrL Harr)|].
    exact (feo_dm_rel Job jcR jcL Hjc dlR dlL Hdl _ _ Hs).
  Qed.

  (** ** Statement correspondences *)

  Definition src_non_idle_swap_maintains_work_conservation_t1 : Prop :=
    ltac:(body_of (fun s : S.statement_non_idle_swap_maintains_work_conservation_t1 => s Job jcR jaR arrR)).
  Definition tgt_non_idle_swap_maintains_work_conservation_t1 : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfWc_non_idle_swap_maintains_work_conservation_t1 Job dJ jcL jaL arrL)).

  Theorem non_idle_swap_maintains_work_conservation_t1_correspondence :
    PropSPropRel src_non_idle_swap_maintains_work_conservation_t1 tgt_non_idle_swap_maintains_work_conservation_t1.
  Proof.
    unfold src_non_idle_swap_maintains_work_conservation_t1, tgt_non_idle_swap_maintains_work_conservation_t1.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (few_sched_at _ _ Hs j2 _ _ Ht2)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (few_wc_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ Ht Ht1)|].
    exact (few_exists_sched _ _ (few_swapped _ _ Hs _ _ _ _ Ht1 Ht2) _ _ Ht).
  Qed.

  Definition src_non_idle_swap_maintains_work_conservation_t2 : Prop :=
    ltac:(body_of (fun s : S.statement_non_idle_swap_maintains_work_conservation_t2 => s Job jcR jaR arrR)).
  Definition tgt_non_idle_swap_maintains_work_conservation_t2 : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfWc_non_idle_swap_maintains_work_conservation_t2 Job dJ jcL jaL arrL)).

  Theorem non_idle_swap_maintains_work_conservation_t2_correspondence :
    PropSPropRel src_non_idle_swap_maintains_work_conservation_t2 tgt_non_idle_swap_maintains_work_conservation_t2.
  Proof.
    unfold src_non_idle_swap_maintains_work_conservation_t2, tgt_non_idle_swap_maintains_work_conservation_t2.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_imp_correspondence; [exact (few_sched_at _ _ Hs j1 _ _ Ht1)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (few_wc_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ Ht Ht2)|].
    exact (few_exists_sched _ _ (few_swapped _ _ Hs _ _ _ _ Ht1 Ht2) _ _ Ht).
  Qed.

  (** The common shape of the [LEQ_t1] and [GT_t2] statements. *)
  Lemma few_outer (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) (Ht1 : SubNatRel t1R t1L) (Ht2 : SubNatRel t2R t2L)
      (CR : nat -> Prop) (CL : Lean.Nat -> SProp)
      (HC : forall tR tL, SubNatRel tR tL -> PropSPropRel (CR tR) (CL tL)) :
    PropSPropRel
      (forall j1 j2 : Job, @prosa.behavior.service.scheduled_at Job PSR sR j1 t1R ->
        @prosa.behavior.service.scheduled_at Job PSR sR j2 t2R ->
        forall (j : Job) (t : nat), prosa.behavior.arrival_sequence.arrives_in arrR j ->
        @prosa.behavior.ready.backlogged Job PSR jcR jaR RMR
          (@prosa.analysis.transform.swap.swapped Job PSR sR t1R t2R) j t ->
        @prosa.model.schedule.work_conserving.work_conserving Job jaR jcR PSR RMR arrR sR -> CR t ->
        exists j_other : Job, @prosa.behavior.service.scheduled_at Job PSR
          (@prosa.analysis.transform.swap.swapped Job PSR sR t1R t2R) j_other t)
      (forall j1 j2 : Job,
        Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL sL j1 t1L) I.Bool_true ->
        Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL sL j2 t2L) I.Bool_true ->
        forall (j : Job) (t : Lean.Nat), I.Prosa_Behavior_Arrival_sequence_arrives_in Job dJ arrL j ->
        Lean.eq (I.Prosa_Behavior_Ready_backlogged_inst4 Job dJ PSL jcL jaL RML
          (I.Prosa_Analysis_Transform_Swap_swapped_inst4 Job dJ PSL sL t1L t2L) j t) I.Bool_true ->
        I.Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job dJ jaL jcL PSL RML arrL sL -> CL t ->
        I.Exists Job (fun j_other => Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL
          (I.Prosa_Analysis_Transform_Swap_swapped_inst4 Job dJ PSL sL t1L t2L) j_other t) I.Bool_true)).
  Proof.
    have Hw := few_swapped _ _ Hs _ _ _ _ Ht1 Ht2.
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (few_sched_at _ _ Hs j1 _ _ Ht1)|].
    apply ar_imp_correspondence; [exact (few_sched_at _ _ Hs j2 _ _ Ht2)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (few_backlogged_related _ _ Hw j _ _ Ht))|].
    apply ar_imp_correspondence; [exact (few_wc_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (HC _ _ Ht)|].
    exact (few_exists_sched _ _ Hw _ _ Ht).
  Qed.

  Definition src_non_idle_swap_maintains_work_conservation_LEQ_t1 : Prop :=
    ltac:(body_of (fun s : S.statement_non_idle_swap_maintains_work_conservation_LEQ_t1 => s Job jcR jaR arrR)).
  Definition tgt_non_idle_swap_maintains_work_conservation_LEQ_t1 : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfWc_non_idle_swap_maintains_work_conservation_LEQ_t1 Job dJ jcL jaL arrL)).

  Theorem non_idle_swap_maintains_work_conservation_LEQ_t1_correspondence :
    PropSPropRel src_non_idle_swap_maintains_work_conservation_LEQ_t1
      tgt_non_idle_swap_maintains_work_conservation_LEQ_t1.
  Proof.
    unfold src_non_idle_swap_maintains_work_conservation_LEQ_t1, tgt_non_idle_swap_maintains_work_conservation_LEQ_t1.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht1 Ht2)|].
    exact (few_outer _ _ Hs _ _ _ _ Ht1 Ht2 _ _ (fun tR tL Ht => sub_nat_le_correspondence _ _ _ _ Ht Ht1)).
  Qed.

  Definition src_non_idle_swap_maintains_work_conservation_GT_t2 : Prop :=
    ltac:(body_of (fun s : S.statement_non_idle_swap_maintains_work_conservation_GT_t2 => s Job jcR jaR arrR)).
  Definition tgt_non_idle_swap_maintains_work_conservation_GT_t2 : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfWc_non_idle_swap_maintains_work_conservation_GT_t2 Job dJ jcL jaL arrL)).

  Theorem non_idle_swap_maintains_work_conservation_GT_t2_correspondence :
    PropSPropRel src_non_idle_swap_maintains_work_conservation_GT_t2
      tgt_non_idle_swap_maintains_work_conservation_GT_t2.
  Proof.
    unfold src_non_idle_swap_maintains_work_conservation_GT_t2, tgt_non_idle_swap_maintains_work_conservation_GT_t2.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht1 Ht2)|].
    exact (few_outer _ _ Hs _ _ _ _ Ht1 Ht2 _ _ (fun tR tL Ht => sub_nat_lt_correspondence _ _ _ _ Ht2 Ht)).
  Qed.

  Definition src_non_idle_swap_maintains_work_conservation_BET_t1_t2 : Prop :=
    ltac:(body_of (fun s : S.statement_non_idle_swap_maintains_work_conservation_BET_t1_t2 => s Job jcR jaR arrR)).
  Definition tgt_non_idle_swap_maintains_work_conservation_BET_t1_t2 : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfWc_non_idle_swap_maintains_work_conservation_BET_t1_t2 Job dJ jcL jaL arrL)).

  Theorem non_idle_swap_maintains_work_conservation_BET_t1_t2_correspondence :
    PropSPropRel src_non_idle_swap_maintains_work_conservation_BET_t1_t2
      tgt_non_idle_swap_maintains_work_conservation_BET_t1_t2.
  Proof.
    unfold src_non_idle_swap_maintains_work_conservation_BET_t1_t2,
      tgt_non_idle_swap_maintains_work_conservation_BET_t1_t2.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (feo_cde_rel Job jcR jcL Hjc _ _ Hs)|].
    apply ar_imp_correspondence; [exact (feo_jcf_rel Job _ _ Hs arrR arrL Harr)|].
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ (Hja j2) Ht1)|].
    apply ar_imp_correspondence; [exact (few_sched_at _ _ Hs j1 _ _ Ht1)|].
    apply ar_imp_correspondence; [exact (few_sched_at _ _ Hs j2 _ _ Ht2)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (few_wc_rel _ _ Hs)|].
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _
        (svc_bool_and_related _ _ _ _ (svc_decide_lt_related _ _ _ _ Ht1 Ht)
          (svc_decide_le_related _ _ _ _ Ht Ht2)))|].
    exact (few_exists_sched _ _ (few_swapped _ _ Hs _ _ _ _ Ht1 Ht2) _ _ Ht).
  Qed.

  Definition src_fsc_swap_maintains_work_conservation : Prop :=
    ltac:(body_of (fun s : S.statement_fsc_swap_maintains_work_conservation => s Job jcR dlR jaR arrR)).
  Definition tgt_fsc_swap_maintains_work_conservation : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfWc_fsc_swap_maintains_work_conservation Job dJ jcL dlL jaL arrL)).

  Theorem fsc_swap_maintains_work_conservation_correspondence :
    PropSPropRel src_fsc_swap_maintains_work_conservation tgt_fsc_swap_maintains_work_conservation.
  Proof.
    unfold src_fsc_swap_maintains_work_conservation, tgt_fsc_swap_maintains_work_conservation.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (feo_must_rel Job jaR jaL Hja _ _ Hs)|].
    apply ar_imp_correspondence; [exact (feo_cde_rel Job jcR jcL Hjc _ _ Hs)|].
    apply ar_imp_correspondence; [exact (feo_jcf_rel Job _ _ Hs arrR arrL Harr)|].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_imp_correspondence; [exact (few_sched_at _ _ Hs j1 _ _ Ht1)|].
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Ht1 (Hdl j1))|].
    apply ar_imp_correspondence; [exact (few_wc_rel _ _ Hs)|].
    exact (few_wc_rel _ _ (few_swapped _ _ Hs _ _ _ _ Ht1
      (feo_fsc Job dlR dlL Hdl jaR jaL Hja _ _ Hs _ _ Ht1 j1))).
  Qed.

  Definition src_mea_maintains_work_conservation : Prop :=
    ltac:(body_of (fun s : S.statement_mea_maintains_work_conservation => s Job jcR dlR jaR arrR)).
  Definition tgt_mea_maintains_work_conservation : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfWc_mea_maintains_work_conservation Job dJ jcL dlL jaL arrL)).

  Theorem mea_maintains_work_conservation_correspondence :
    PropSPropRel src_mea_maintains_work_conservation tgt_mea_maintains_work_conservation.
  Proof.
    unfold src_mea_maintains_work_conservation, tgt_mea_maintains_work_conservation.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (feo_jcf_rel Job _ _ Hs arrR arrL Harr)|].
    apply ar_imp_correspondence; [exact (feo_must_rel Job jaR jaL Hja _ _ Hs)|].
    apply ar_imp_correspondence; [exact (feo_cde_rel Job jcR jcL Hjc _ _ Hs)|].
    apply ar_imp_correspondence; [exact (feo_dm_rel Job jcR jcL Hjc dlR dlL Hdl _ _ Hs)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (few_wc_rel _ _ Hs)|].
    exact (few_wc_rel _ _ (feo_mea Job dlR dlL Hdl jaR jaL Hja _ _ Hs _ _ Ht)).
  Qed.

  Definition src_edf_transform_prefix_maintains_work_conservation : Prop :=
    ltac:(body_of (fun s : S.statement_edf_transform_prefix_maintains_work_conservation => s Job jcR dlR jaR arrR)).
  Definition tgt_edf_transform_prefix_maintains_work_conservation : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfWc_edf_transform_prefix_maintains_work_conservation
        Job dJ jcL dlL jaL arrL)).

  Theorem edf_transform_prefix_maintains_work_conservation_correspondence :
    PropSPropRel src_edf_transform_prefix_maintains_work_conservation
      tgt_edf_transform_prefix_maintains_work_conservation.
  Proof.
    unfold src_edf_transform_prefix_maintains_work_conservation,
      tgt_edf_transform_prefix_maintains_work_conservation.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    have Hp := feo_prefix Job dlR dlL Hdl jaR jaL Hja _ _ Hs _ _ Hh.
    apply ar_imp_correspondence;
      [exact (ar_and_correspondence _ _ _ _ (scheduled_behavior_premises_correspondence _ _ Hs) (few_wc_rel _ _ Hs))|].
    exact (ar_and_correspondence _ _ _ _ (scheduled_behavior_premises_correspondence _ _ Hp) (few_wc_rel _ _ Hp)).
  Qed.

  Definition src_sched_satisfies_behavior_premises : Prop :=
    ltac:(body_of (fun s : S.statement_sched_satisfies_behavior_premises => s Job jcR dlR jaR arrR)).
  Definition tgt_sched_satisfies_behavior_premises : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfWc_sched_satisfies_behavior_premises Job dJ jcL dlL jaL arrL)).

  Theorem sched_satisfies_behavior_premises_correspondence :
    PropSPropRel src_sched_satisfies_behavior_premises tgt_sched_satisfies_behavior_premises.
  Proof.
    unfold src_sched_satisfies_behavior_premises, tgt_sched_satisfies_behavior_premises.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (feo_valid_rel Job jcR jcL Hjc jaR jaL Hja _ _ Hs arrR arrL Harr)|].
    apply ar_imp_correspondence; [exact (feo_dm_rel Job jcR jcL Hjc dlR dlL Hdl _ _ Hs)|].
    exact (scheduled_behavior_premises_correspondence _ _ Hs).
  Qed.

  Definition src_edf_transform_maintains_work_conservation : Prop :=
    ltac:(body_of (fun s : S.statement_edf_transform_maintains_work_conservation => s Job jcR dlR jaR arrR)).
  Definition tgt_edf_transform_maintains_work_conservation : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfWc_edf_transform_maintains_work_conservation Job dJ jcL dlL jaL arrL)).

  Theorem edf_transform_maintains_work_conservation_correspondence :
    PropSPropRel src_edf_transform_maintains_work_conservation tgt_edf_transform_maintains_work_conservation.
  Proof.
    unfold src_edf_transform_maintains_work_conservation, tgt_edf_transform_maintains_work_conservation.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (feo_valid_rel Job jcR jcL Hjc jaR jaL Hja _ _ Hs arrR arrL Harr)|].
    apply ar_imp_correspondence; [exact (feo_dm_rel Job jcR jcL Hjc dlR dlL Hdl _ _ Hs)|].
    apply ar_imp_correspondence; [exact (few_wc_rel _ _ Hs)|].
    exact (few_wc_rel _ _ (feo_transform Job dlR dlL Hdl jaR jaL Hja _ _ Hs)).
  Qed.
End EdfWc.
