From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import FactsEdfAthepBoundSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsEdfAthepBound ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence
  WorkloadBoundedCorrespondence EdfAthepBoundCorrespondence.

Module I := ImportedFactsEdfAthepBound.
Module S := FactsEdfAthepBoundSemanticSource.FactsEdfAthepBoundSemanticSource.

(** Statement correspondences for [analysis/facts/workload/edf_athep_bound.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types, [task_cost],
    [task_deadline], a leading [MaxArrivals] instance, [job_task],
    [job_arrival], [job_cost], a leading processor state, a leading arrival
    sequence, and for the monotonicity statement the leading task set);
    target side: the imported Lean theorem types at related inputs
    ([SubNatRel] on [task_cost]/[task_deadline], the accepted
    [CvMaxArrivalsRel], [Lean.eq] on [job_task], [ArJobArrivalRel],
    [SvcJobCostRel], the accepted two-sided [SvcProcessorStateRel],
    [ArArrivalSequenceRel], [ArListRel]).  Binders quantified inside the
    statements are covered in both directions: task sets through the list
    conversion, schedules through the processor-state conversion, Nats;
    tasks and jobs are identity carriers.  The EDF policy over the
    absolute-deadline instance is related pointwise on Booleans by unfolding
    both instances; workloads, arrivals, the request-bound function, the
    athep bound definition and the workload-bound predicate are closed by the
    accepted certificates re-instantiated at this artifact.  No source or
    target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma feab_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Lemma feab_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma feab_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma feab_decide_eq_related (T : eqType) (x y : T) :
  ArBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (ar_decidable_eq T x y)).
Proof.
  unfold ar_decidable_eq, ArBoolRel.
  destruct (@eqP T x y); cbn; exact (@Lean.eq_refl _ _).
Qed.

Lemma feab_monotone_related (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  (forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL)) ->
  PropSPropRel (@prosa.util.rel.monotone nat leq fR)
    (I.Prosa_Util_Rel_monotone Lean.Nat (fun x y => ar_target_decide_le x y) fL).
Proof.
  intro Hf. unfold prosa.util.rel.monotone.
  cbn [I.Prosa_Util_Rel_monotone].
  apply ar_forall_nat_correspondence. intros xR xL Hx.
  apply ar_forall_nat_correspondence. intros yR yL Hy.
  apply ar_imp_correspondence;
    [exact (ar_bool_truth_correspondence _ _ (ar_decide_le_related _ _ _ _ Hx Hy))|].
  exact (ar_bool_truth_correspondence _ _ (ar_decide_le_related _ _ _ _ (Hf _ _ Hx) (Hf _ _ Hy))).
Qed.

Section Facts.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable tdR : prosa.model.task.concept.TaskDeadline Task.
  Variable tdL : I.Prosa_Model_Task_Concept_TaskDeadline Task dT.
  Hypothesis Htd : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR tsk)
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL tsk).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  (** *** The EDF policy over the absolute-deadline instance *)

  Let dlR := @prosa.model.task.absolute_deadline.job_deadline_from_task_deadline Job Task tdR jaR jtR.
  Let dlL := I.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline
    Job Task dJ dT tdL jaL jtL.
  Let edfR := @prosa.model.priority.edf.EDF Job dlR.
  Let edfL := I.Prosa_Model_Priority_Edf_EDF Job dJ dlL.

  Lemma feab_task_deadline_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (feab_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_deadline Task tdR (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL v)) _ _ (Hjt j) (Htd _)).
  Qed.

  Lemma feab_job_deadline_related (j : Job) :
    SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
      (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).
  Proof.
    unfold dlR, dlL, prosa.model.task.absolute_deadline.job_deadline_from_task_deadline.
    cbn [I.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline
      I.Prosa_Behavior_Job_JobDeadline_job_deadline].
    exact (svc_target_add_related _ _ _ _ (Hja j) (feab_task_deadline_of_job_related j)).
  Qed.

  Lemma feab_edf_related (x y : Job) :
    ArBoolRel (edfR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ edfL x y).
  Proof.
    unfold edfR, edfL, prosa.model.priority.edf.EDF.
    cbn [I.Prosa_Model_Priority_Edf_EDF I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job].
    exact (svc_decide_le_related _ _ _ _ (feab_job_deadline_related x) (feab_job_deadline_related y)).
  Qed.

  Lemma feab_job_task_eq_related (jo : Job) (tsk : Task) :
    ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR jo == tsk)
      (I.Decidable_decide
        (Lean.eq (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL jo) tsk)
        (dT (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL jo) tsk)).
  Proof.
    refine (feab_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR jo == tsk)
        (I.Decidable_decide (Lean.eq v tsk) (dT v tsk))) _ _ (Hjt jo) _).
    exact (feab_decide_eq_related Task _ tsk).
  Qed.

  Lemma feab_edf_from_related (j : Job) (tsk_o : Task) :
    ArPredRel (fun jo => edfR jo j && (@prosa.model.task.concept.job_task Job Task jtR jo == tsk_o))
      (fun jo => I.Bool_and (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ edfL jo j)
        (I.Decidable_decide
          (Lean.eq (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL jo) tsk_o)
          (dT (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL jo) tsk_o))).
  Proof.
    intro jo.
    exact (ar_bool_and_related _ _ _ _ (feab_edf_related jo j) (feab_job_task_eq_related jo tsk_o)).
  Qed.

  (** *** Task-concept and job predicates *)

  Lemma feab_job_of_task_related (tsk : Task) (j : Job) :
    ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof.
    unfold prosa.model.task.concept.job_of_task.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    exact (feab_job_task_eq_related j tsk).
  Qed.

  Lemma feab_job_cost_positive_related (j : Job) :
    PropSPropRel (is_true (@prosa.model.job.properties.job_cost_positive Job costR j))
      (Lean.eq (I.Prosa_Model_Job_Properties_job_cost_positive Job dJ costL j) I.Bool_true).
  Proof.
    unfold prosa.model.job.properties.job_cost_positive.
    cbn [I.Prosa_Model_Job_Properties_job_cost_positive].
    exact (ar_bool_truth_correspondence _ _
      (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))).
  Qed.

  Lemma feab_task_cost_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (feab_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)).
  Qed.

  Lemma feab_valid_job_costs_related :
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
      (svc_decide_le_related _ _ _ _ (Hcost j) (feab_task_cost_of_job_related j))).
  Qed.

  Lemma feab_all_jobs_from_taskset_related tsR tsL (Hts : ArListRel tsR tsL) :
    PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
      (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
  Proof.
    unfold prosa.model.task.concept.all_jobs_from_taskset.
    cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    rewrite -(imported_eq_to_coq_eq _ _ (Hjt j)).
    exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task _ _ _ Hts)).
  Qed.

  Let VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.

  (** *** Covers *)

  Lemma feab_list_to_target_rel (xs : seq Task) : ArListRel xs (ar_list_to_imported xs).
  Proof. exact (@Lean.eq_refl _ _). Qed.

  Lemma feab_list_to_source_rel (xs : I.List Task) : ArListRel (ar_list_to_rocq xs) xs.
  Proof. exact (ar_list_target_roundtrip xs). Qed.

  Let cover_ts :=
    feab_forall_cover_sprop _ _ (@ArListRel Task)
      ar_list_to_imported ar_list_to_rocq feab_list_to_target_rel feab_list_to_source_rel.

  (** *** Statements over a leading arrival sequence *)

  Let EDF_FROM_WL j tsk_o t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :=
    workload_of_jobs_correspondence Job costR costL Hcost _ _ (feab_edf_from_related j tsk_o) _ _
      (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2).

  Definition src_total_workload_shorten_range : Prop :=
    ltac:(body_of (fun s : S.statement_total_workload_shorten_range => s Task tdR Job jtR jaR costR arrR)).
  Definition tgt_total_workload_shorten_range : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Workload_EdfAthepBound_total_workload_shorten_range
      Task dT tdL Job dJ jtL jaL costL arrL)).
  Theorem total_workload_shorten_range_correspondence :
    PropSPropRel src_total_workload_shorten_range tgt_total_workload_shorten_range.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply cover_ts. intros tsR tsL Hts.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (feab_job_of_task_related tsk j))|].
    apply ar_imp_correspondence; [exact (feab_job_cost_positive_related j)|].
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    apply ar_imp_correspondence;
      [exact (sub_nat_lt_correspondence _ _ _ _ (svc_target_add_related _ _ _ _ Ht1 Hd) Ht2)|].
    apply ar_forall_identity_correspondence. intro tsk_o.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task _ _ _ Hts))|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (wl_ne_observation Task tsk_o tsk))|].
    have HL := svc_target_sub_related _ _ _ _
      (svc_target_add_related _ _ _ _
        (svc_target_add_related _ _ _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1)
          (sub_nat_rel_canonical (S O)))
        (Htd tsk))
      (Htd tsk_o).
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ HL Hd)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (EDF_FROM_WL j tsk_o _ _ Ht1 _ _ (svc_target_add_related _ _ _ _ Ht1 Hd))
      (EDF_FROM_WL j tsk_o _ _ Ht1 _ _ (svc_target_add_related _ _ _ _ Ht1 HL))).
  Qed.

  Section MA.
    Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
    Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
    Hypothesis Hma : CvMaxArrivalsRel Task maR maL.

    Let RESPS tsR tsL Hts :=
      taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts
        maR maL Hma.
    Let BOUND tsR tsL Hts tsk :=
      bound_on_athep_workload_correspondence Task tcR tcL Htc tdR tdL Htd maR maL Hma tsR tsL Hts tsk.

    Definition src_sum_of_workloads_is_at_most_bound_on_total_hep_workload : Prop :=
      ltac:(body_of (fun s : S.statement_sum_of_workloads_is_at_most_bound_on_total_hep_workload =>
        s Task tcR tdR maR Job jtR jaR costR arrR)).
    Definition tgt_sum_of_workloads_is_at_most_bound_on_total_hep_workload : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_Workload_EdfAthepBound_sum_of_workloads_is_at_most_bound_on_total_hep_workload
          Task dT tcL tdL maL Job dJ jtL jaL costL arrL)).
    Theorem sum_of_workloads_is_at_most_bound_on_total_hep_workload_correspondence :
      PropSPropRel src_sum_of_workloads_is_at_most_bound_on_total_hep_workload
        tgt_sum_of_workloads_is_at_most_bound_on_total_hep_workload.
    Proof.
      apply ar_imp_correspondence; [exact VALID|].
      apply ar_imp_correspondence; [exact feab_valid_job_costs_related|].
      apply cover_ts. intros tsR tsL Hts.
      apply ar_imp_correspondence; [exact (RESPS tsR tsL Hts)|].
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (feab_job_of_task_related tsk j))|].
      apply ar_imp_correspondence; [exact (feab_job_cost_positive_related j)|].
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
      apply ar_forall_nat_correspondence. intros dR dL Hd.
      apply ar_imp_correspondence;
        [exact (sub_nat_lt_correspondence _ _ _ _ (svc_target_add_related _ _ _ _ Ht1 Hd) Ht2)|].
      exact (sub_nat_le_correspondence _ _ _ _
        (rbf_sum_filtered_related Task _ _
          (fun tsk_o => EDF_FROM_WL j tsk_o _ _ Ht1 _ _ (svc_target_add_related _ _ _ _ Ht1 Hd))
          _ _ (fun tsk_o => wl_ne_observation Task tsk_o tsk) _ _ Hts)
        (BOUND tsR tsL Hts tsk _ _ _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1) Hd)).
    Qed.

    Section Sched.
      Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
      Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
      Variable R : SvcProcessorStateRel Job PStateR PStateL.

      Definition feab_sched_to_target (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
          I.Prosa_Behavior_Schedule_schedule Job dJ PStateL :=
        fun tL => svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq tL)).

      Definition feab_sched_to_source (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) :
          @prosa.behavior.schedule.schedule Job PStateR :=
        fun tR => svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)).

      Lemma feab_sched_to_target_rel schedR :
        SvcScheduleRel Job PStateR PStateL R schedR (feab_sched_to_target schedR).
      Proof.
        intros tR tL Ht. unfold feab_sched_to_target.
        rewrite (feab_nat_input _ _ Ht).
        exact (svc_ps_state_rel_canonical Job PStateR PStateL R (schedR tR)).
      Qed.

      Lemma feab_sched_to_source_rel schedL :
        SvcScheduleRel Job PStateR PStateL R (feab_sched_to_source schedL) schedL.
      Proof.
        intros tR tL Ht. unfold feab_sched_to_source.
        exact (feab_lean_transport
          (fun x => svc_ps_state_rel Job PStateR PStateL R
            (svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR))) (schedL x))
          _ _ Ht (svc_ps_state_rel_surjective Job PStateR PStateL R _)).
      Qed.

      Let cover_sched :=
        feab_forall_cover_sprop _ _ (SvcScheduleRel Job PStateR PStateL R)
          feab_sched_to_target feab_sched_to_source feab_sched_to_target_rel feab_sched_to_source_rel.

      Definition src_bound_on_athep_workload_is_valid : Prop :=
        ltac:(body_of (fun s : S.statement_bound_on_athep_workload_is_valid =>
          s Task tcR tdR maR Job jtR jaR costR PStateR arrR)).
      Definition tgt_bound_on_athep_workload_is_valid : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Workload_EdfAthepBound_bound_on_athep_workload_is_valid
          Task dT tcL tdL maL Job dJ jtL jaL costL PStateL arrL)).
      Theorem bound_on_athep_workload_is_valid_correspondence :
        PropSPropRel src_bound_on_athep_workload_is_valid tgt_bound_on_athep_workload_is_valid.
      Proof.
        apply ar_imp_correspondence; [exact VALID|].
        apply ar_imp_correspondence; [exact feab_valid_job_costs_related|].
        apply cover_ts. intros tsR tsL Hts.
        apply ar_imp_correspondence; [exact (feab_all_jobs_from_taskset_related tsR tsL Hts)|].
        apply ar_imp_correspondence; [exact (RESPS tsR tsL Hts)|].
        apply ar_forall_identity_correspondence. intro tsk.
        apply cover_sched. intros schedR schedL Hsched.
        exact (athep_workload_is_bounded_correspondence Task Job costR costL Hcost jaR jaL Hja
          jtR jtL Hjt PStateR PStateL R _ _ feab_edf_related arrR arrL Harr
          schedR schedL Hsched tsk _ _
          (fun aR aL dR dL Ha Hd => BOUND tsR tsL Hts tsk aR dR aL dL Ha Hd)).
      Qed.
    End Sched.
  End MA.
End Facts.

Section Monotone.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable tdR : prosa.model.task.concept.TaskDeadline Task.
  Variable tdL : I.Prosa_Model_Task_Concept_TaskDeadline Task dT.
  Hypothesis Htd : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR tsk)
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL tsk).
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : CvMaxArrivalsRel Task maR maL.
  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.

  Definition src_bound_on_athep_workload_monotone : Prop :=
    ltac:(body_of (fun s : S.statement_bound_on_athep_workload_monotone => s Task tcR tdR maR tsR)).
  Definition tgt_bound_on_athep_workload_monotone : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Workload_EdfAthepBound_bound_on_athep_workload_monotone
      Task dT tcL tdL maL tsL)).
  Theorem bound_on_athep_workload_monotone_correspondence :
    PropSPropRel src_bound_on_athep_workload_monotone tgt_bound_on_athep_workload_monotone.
  Proof.
    apply ar_imp_correspondence;
      [exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hma)|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_nat_correspondence. intros aR aL Ha.
    apply feab_monotone_related. intros dR dL Hd.
    exact (bound_on_athep_workload_correspondence Task tcR tcL Htc tdR tdL Htd maR maL Hma tsR tsL Hts
      tsk aR dR aL dL Ha Hd).
  Qed.
End Monotone.
