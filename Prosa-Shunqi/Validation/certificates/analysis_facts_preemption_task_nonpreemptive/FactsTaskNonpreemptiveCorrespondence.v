From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsTaskNonpreemptiveSemanticSource.
From prosa Require Import model.schedule.nonpreemptive model.preemption.fully_nonpreemptive.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsTaskNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskPreemptionParametersCorrespondence TaskPreemptionFullyNonpreemptiveCorrespondence.

Module I := ImportedFactsTaskNonpreemptive.
Module S := FactsTaskNonpreemptiveSemanticSource.FactsTaskNonpreemptiveSemanticSource.
Module T := TaskPreemptionFullyNonpreemptiveSemanticSource.TaskPreemptionFullyNonpreemptiveSemanticSource.

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma ftnp_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Section Fnp.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Lemma ftnp_fully_nonpreemptive_job_related :
    PpJobPreemptableRel Job
      (@prosa.model.preemption.fully_nonpreemptive.fully_nonpreemptive_job_model Job costR)
      (I.Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job dJ costL).
  Proof.
    intros j nR nL Hn.
    exact (pp_bool_or_related _ _ _ _
      (pp_nat_eqb_related _ _ _ _ Hn (sub_nat_rel_canonical O))
      (pp_nat_eqb_related _ _ _ _ Hn (Hcost j))).
  Qed.
End Fnp.


(** Statement correspondences for [analysis/facts/preemption/task/nonpreemptive.v]:
    the extracted statements (elaborated with the source's section-local
    fully nonpreemptive job/task instances) against the imported Lean theorem
    types (which pass the accepted Lean definitions explicitly).  The job
    instance is a [PpJobPreemptableRel] proved above, the task instance the
    accepted [fully_nonpreemptive_task_model_correspondence]; the
    bounded-segment predicates are closed by the accepted
    [TaskPreemptionParametersCorrespondence], processor-state and schedule
    hypotheses as in the accepted job-nonpreemptive certificate.  No source
    or target theorem is used. *)

Lemma ftnp_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Lemma ftnp_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Section TaskNonpreemptive.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let FNPJ := ftnp_fully_nonpreemptive_job_related Job costR costL Hcost.
  Let FNPT := fully_nonpreemptive_task_model_correspondence Task tcR tcL Htc.

  Lemma ftnp_task_cost_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (ftnp_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)).
  Qed.

  Lemma ftnp_valid_job_costs_related :
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
  Proof.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    unfold prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_valid_job_cost].
    exact (ar_bool_truth_correspondence _ _
      (svc_decide_le_related _ _ _ _ (Hcost j) (ftnp_task_cost_of_job_related j))).
  Qed.

  Definition src_fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions : Prop :=
    ltac:(body_of (fun s : S.statement_fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions =>
      s Task tcR Job jtR costR arrR)).
  Definition tgt_fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_Task_Nonpreemptive_fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions
        Task dT tcL Job dJ jtL costL arrL)).
  Theorem fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions_correspondence :
    PropSPropRel src_fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions
      tgt_fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions.
  Proof.
    apply ar_imp_correspondence; [exact ftnp_valid_job_costs_related|].
    exact (model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt
      costR costL Hcost _ _ FNPT _ _ FNPJ arrR arrL Harr).
  Qed.

  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let cover_state :=
    ftnp_forall_cover_sprop _ _ (svc_ps_state_rel Job PStateR PStateL R)
      (svc_ps_state_to_target Job PStateR PStateL R) (svc_ps_state_to_source Job PStateR PStateL R)
      (svc_ps_state_rel_canonical Job PStateR PStateL R) (svc_ps_state_rel_surjective Job PStateR PStateL R).

  Lemma ftnp_unit_service_related :
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

  Definition FtnpScheduleFunRel (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      Lean.eq (svc_ps_state_to_target Job PStateR PStateL R (schedR tR)) (schedL tL).

  Lemma ftnp_schedule_fun_to_svc schedR schedL :
    FtnpScheduleFunRel schedR schedL -> SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Proof.
    intros Hf tR tL Ht.
    exact (ftnp_lean_transport (fun sL => svc_ps_state_rel Job PStateR PStateL R (schedR tR) sL)
      _ _ (Hf tR tL Ht) (svc_ps_state_rel_canonical Job PStateR PStateL R (schedR tR))).
  Qed.

  Definition ftnp_schedule_to_target (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
      I.Prosa_Behavior_Schedule_schedule Job dJ PStateL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq tL)).

  Definition ftnp_schedule_to_source (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) :
      @prosa.behavior.schedule.schedule Job PStateR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)).

  Lemma ftnp_schedule_to_target_rel schedR : FtnpScheduleFunRel schedR (ftnp_schedule_to_target schedR).
  Proof.
    intros tR tL Ht. unfold ftnp_schedule_to_target.
    rewrite (ftnp_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma ftnp_schedule_to_source_rel schedL : FtnpScheduleFunRel (ftnp_schedule_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. unfold ftnp_schedule_to_source.
    exact (sub_imported_eq_trans _ _ _
      (svc_ps_state_target_roundtrip Job PStateR PStateL R _)
      (sub_imported_eq_congr schedL _ _ Ht)).
  Qed.

  Let cover_schedule :=
    ftnp_forall_cover_sprop _ _ FtnpScheduleFunRel ftnp_schedule_to_target ftnp_schedule_to_source
      ftnp_schedule_to_target_rel ftnp_schedule_to_source_rel.

  Section Sched.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Let SCHED := pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched.
    Let COMPLETED := pp_completed_by_related Job costR costL Hcost PStateR PStateL R schedR schedL Hsched.
    Let SERVICE := pp_service_related Job PStateR PStateL R schedR schedL Hsched.

    Lemma ftnp_nonpreemptive_schedule_related :
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

    Lemma ftnp_completed_jobs_dont_execute_related :
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
  End Sched.

  Definition src_fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions : Prop :=
    ltac:(body_of (fun s : S.statement_fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions =>
      s Task tcR Job jtR costR arrR PStateR)).
  Definition tgt_fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Preemption_Task_Nonpreemptive_fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions
        Task dT tcL Job dJ jtL costL arrL PStateL)).
  Theorem fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions_correspondence :
    PropSPropRel src_fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions
      tgt_fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions.
  Proof.
    apply ar_imp_correspondence; [exact ftnp_unit_service_related|].
    apply cover_schedule. intros schedR schedL Hf.
    have Hsched := ftnp_schedule_fun_to_svc _ _ Hf.
    apply ar_imp_correspondence; [exact (ftnp_nonpreemptive_schedule_related schedR schedL Hsched)|].
    apply ar_imp_correspondence; [exact (ftnp_completed_jobs_dont_execute_related schedR schedL Hsched)|].
    apply ar_imp_correspondence; [exact ftnp_valid_job_costs_related|].
    exact (valid_model_with_bounded_nonpreemptive_segments_correspondence Task Job jtR jtL Hjt
      costR costL Hcost _ _ FNPT _ _ FNPJ arrR arrL Harr PStateR PStateL R schedR schedL Hsched).
  Qed.
End TaskNonpreemptive.
