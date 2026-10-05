From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsNonpreemptiveJobSemanticSource.
From prosa Require Import model.schedule.nonpreemptive model.preemption.fully_nonpreemptive.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsNonpreemptiveJob ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence.

Module I := ImportedFactsNonpreemptiveJob.
Module S := FactsNonpreemptiveJobSemanticSource.FactsNonpreemptiveJobSemanticSource.

(** Statement correspondences for [analysis/facts/preemption/job/nonpreemptive.v].

    Source side: the extracted statements [S.statement_X] (elaborated with
    the source's section-local fully nonpreemptive instance) specialised at
    their leading inputs; target side: the imported Lean theorem types, which
    pass the accepted Lean [fully_nonpreemptive_job_model] explicitly.  The
    source instance (compiled from the pinned [fully_nonpreemptive.v]) is
    related to the Lean definition as a [PpJobPreemptableRel].  Inputs:
    [job_cost] by [SvcJobCostRel], processor states by the accepted
    two-sided [SvcProcessorStateRel], schedules by [SvcScheduleRel] (as a
    leading input) or covered in both directions functionally through the
    state conversion with its roundtrips (when quantified), arrival
    sequences by [ArArrivalSequenceRel].  Preemption validity, segment
    lengths and [preempted_at] are closed by the accepted
    [PreemptionParameterCorrespondence].  No source or target theorem is
    used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fnpj_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Lemma fnpj_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma fnpj_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Section Nonpreemptive.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Lemma fnpj_fully_nonpreemptive_related :
    PpJobPreemptableRel Job
      (@prosa.model.preemption.fully_nonpreemptive.fully_nonpreemptive_job_model Job costR)
      (I.Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job dJ costL).
  Proof.
    intros j nR nL Hn.
    exact (pp_bool_or_related _ _ _ _
      (pp_nat_eqb_related _ _ _ _ Hn (sub_nat_rel_canonical O))
      (pp_nat_eqb_related _ _ _ _ Hn (Hcost j))).
  Qed.

  Definition src_job_max_nps_is_job_cost : Prop :=
    ltac:(body_of (fun s : S.statement_job_max_nps_is_job_cost => s Job costR)).
  Definition tgt_job_max_nps_is_job_cost : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_Job_Nonpreemptive_job_max_nps_is_job_cost
      Job dJ costL)).
  Theorem job_max_nps_is_job_cost_correspondence :
    PropSPropRel src_job_max_nps_is_job_cost tgt_job_max_nps_is_job_cost.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    exact (sub_nat_eq_correspondence _ _ _ _
      (job_max_nonpreemptive_segment_correspondence Job costR costL Hcost _ _
        fnpj_fully_nonpreemptive_related j) (Hcost j)).
  Qed.

  Definition src_job_last_nps_is_job_cost : Prop :=
    ltac:(body_of (fun s : S.statement_job_last_nps_is_job_cost => s Job costR)).
  Definition tgt_job_last_nps_is_job_cost : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_Job_Nonpreemptive_job_last_nps_is_job_cost
      Job dJ costL)).
  Theorem job_last_nps_is_job_cost_correspondence :
    PropSPropRel src_job_last_nps_is_job_cost tgt_job_last_nps_is_job_cost.
  Proof.
    apply ar_forall_identity_correspondence. intro j.
    exact (sub_nat_eq_correspondence _ _ _ _
      (job_last_nonpreemptive_segment_correspondence Job costR costL Hcost _ _
        fnpj_fully_nonpreemptive_related j) (Hcost j)).
  Qed.

  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let cover_state :=
    fnpj_forall_cover_sprop _ _ (svc_ps_state_rel Job PStateR PStateL R)
      (svc_ps_state_to_target Job PStateR PStateL R) (svc_ps_state_to_source Job PStateR PStateL R)
      (svc_ps_state_rel_canonical Job PStateR PStateL R) (svc_ps_state_rel_surjective Job PStateR PStateL R).

  Lemma fnpj_unit_service_related :
    PropSPropRel (@prosa.model.processor.platform_properties.unit_service_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.unit_service_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model].
    apply ar_forall_identity_correspondence. intro j'.
    apply cover_state. intros sR sL Hs.
    exact (sub_nat_le_correspondence _ _ _ _ (svc_service_in_related Job PStateR PStateL R j' sR sL Hs)
      (sub_nat_rel_canonical 1)).
  Qed.

  (** Schedule-level observations for any related schedule pair. *)

  Section Sched.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Let SCHED := pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched.
    Let COMPLETED := pp_completed_by_related Job costR costL Hcost PStateR PStateL R schedR schedL Hsched.
    Let SERVICE := pp_service_related Job PStateR PStateL R schedR schedL Hsched.

    Lemma fnpj_nonpreemptive_schedule_related :
      PropSPropRel (@prosa.model.schedule.nonpreemptive.nonpreemptive_schedule Job costR PStateR schedR)
        (I.Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule Job dJ costL PStateL schedL).
    Proof.
      unfold prosa.model.schedule.nonpreemptive.nonpreemptive_schedule.
      cbn [I.Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_nat_correspondence. intros uR uL Hu.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Hu)|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (SCHED j _ _ Ht))|].
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (COMPLETED j _ _ Hu)))|].
      exact (ar_bool_truth_correspondence _ _ (SCHED j _ _ Hu)).
    Qed.

    Lemma fnpj_completed_jobs_dont_execute_related :
      PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PStateR schedR costR)
        (I.Prosa_Behavior_Ready_completed_jobs_dont_execute Job dJ PStateL schedL costL).
    Proof.
      unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (SCHED j _ _ Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _ (SERVICE j _ _ Ht) (Hcost j)).
    Qed.

    Definition src_no_preemptions_equiv_nonpreemptive : Prop :=
      ltac:(body_of (fun s : S.statement_no_preemptions_equiv_nonpreemptive => s Job costR PStateR schedR)).
    Definition tgt_no_preemptions_equiv_nonpreemptive : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_Job_Nonpreemptive_no_preemptions_equiv_nonpreemptive
        Job dJ costL PStateL schedL)).
    Theorem no_preemptions_equiv_nonpreemptive_correspondence :
      PropSPropRel src_no_preemptions_equiv_nonpreemptive tgt_no_preemptions_equiv_nonpreemptive.
    Proof.
      apply pp_iff_correspondence.
      - apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
          (preempted_at_correspondence Job costR costL Hcost PStateR PStateL R schedR schedL Hsched j _ _ Ht))).
      - exact fnpj_nonpreemptive_schedule_related.
    Qed.
  End Sched.

  (** Schedules quantified inside a statement are covered functionally. *)

  Definition FnpjScheduleFunRel (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      Lean.eq (svc_ps_state_to_target Job PStateR PStateL R (schedR tR)) (schedL tL).

  Lemma fnpj_schedule_fun_to_svc schedR schedL :
    FnpjScheduleFunRel schedR schedL -> SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Proof.
    intros Hf tR tL Ht.
    exact (fnpj_lean_transport (fun sL => svc_ps_state_rel Job PStateR PStateL R (schedR tR) sL)
      _ _ (Hf tR tL Ht) (svc_ps_state_rel_canonical Job PStateR PStateL R (schedR tR))).
  Qed.

  Definition fnpj_schedule_to_target (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
      I.Prosa_Behavior_Schedule_schedule Job dJ PStateL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq tL)).

  Definition fnpj_schedule_to_source (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) :
      @prosa.behavior.schedule.schedule Job PStateR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)).

  Lemma fnpj_schedule_to_target_rel schedR : FnpjScheduleFunRel schedR (fnpj_schedule_to_target schedR).
  Proof.
    intros tR tL Ht. unfold fnpj_schedule_to_target.
    rewrite (fnpj_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma fnpj_schedule_to_source_rel schedL : FnpjScheduleFunRel (fnpj_schedule_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. unfold fnpj_schedule_to_source.
    exact (sub_imported_eq_trans _ _ _
      (svc_ps_state_target_roundtrip Job PStateR PStateL R _)
      (sub_imported_eq_congr schedL _ _ Ht)).
  Qed.

  Let cover_schedule :=
    fnpj_forall_cover_sprop _ _ FnpjScheduleFunRel fnpj_schedule_to_target fnpj_schedule_to_source
      fnpj_schedule_to_target_rel fnpj_schedule_to_source_rel.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Definition src_valid_fully_nonpreemptive_model : Prop :=
    ltac:(body_of (fun s : S.statement_valid_fully_nonpreemptive_model => s Job costR arrR PStateR)).
  Definition tgt_valid_fully_nonpreemptive_model : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Preemption_Job_Nonpreemptive_valid_fully_nonpreemptive_model
      Job dJ costL arrL PStateL)).
  Theorem valid_fully_nonpreemptive_model_correspondence :
    PropSPropRel src_valid_fully_nonpreemptive_model tgt_valid_fully_nonpreemptive_model.
  Proof.
    apply ar_imp_correspondence; [exact fnpj_unit_service_related|].
    apply cover_schedule. intros schedR schedL Hf.
    have Hsched := fnpj_schedule_fun_to_svc _ _ Hf.
    apply ar_imp_correspondence; [exact (fnpj_nonpreemptive_schedule_related schedR schedL Hsched)|].
    apply ar_imp_correspondence; [exact (fnpj_completed_jobs_dont_execute_related schedR schedL Hsched)|].
    exact (valid_preemption_model_correspondence Job costR costL Hcost _ _ fnpj_fully_nonpreemptive_related
      PStateR PStateL R schedR schedL Hsched arrR arrL Harr).
  Qed.
End Nonpreemptive.
