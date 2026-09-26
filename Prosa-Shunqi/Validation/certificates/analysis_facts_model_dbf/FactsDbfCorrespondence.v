From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import FactsDbfSemanticSource.
From prosa Require Import model.task.arrivals model.task.absolute_deadline.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsDbf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence
  WorkloadBoundedCorrespondence DemandBoundFunctionCorrespondence.

Module I := ImportedFactsDbf.
Module S := FactsDbfSemanticSource.FactsDbfSemanticSource.

(** Correspondences for [analysis/facts/model/dbf.v].

    Source side: the extracted definition blocks and statements
    [S.statement_X] specialised at their leading inputs (task and job types,
    [task_deadline], [job_task], [job_arrival] and the arrival sequence);
    target side: the compiled Lean definitions and the imported Lean theorem
    types at related inputs ([SubNatRel] on [task_deadline], [Lean.eq] on
    [job_task], [ArJobArrivalRel], [ArArrivalSequenceRel]; the definitions
    also at [SvcJobCostRel]).  Binders quantified inside the statements are
    covered in both directions: the [TaskCost] and [JobCost] instances
    pointwise with two-way totals, [MaxArrivals] instances by the accepted
    curve-family totals, task sets through the list conversion, Nats; tasks
    are identity carriers.  The absolute-deadline instance is related by
    unfolding it on both sides; the deadline-filtered task arrivals,
    workloads, RBFs and DBFs are closed by the accepted arrivals, workload,
    request-bound-function and demand-bound-function certificates
    re-instantiated at this artifact.  No source or target theorem is
    used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fdbf_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Lemma fdbf_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma fdbf_list_eq_correspondence (T : Type) (aR bR : seq T) (aL bL : I.List T) :
  ArListRel aR aL -> ArListRel bR bL -> PropSPropRel (aR = bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Ha)
      (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (f_equal ar_list_to_imported E)) Hb)).
  - intro HL. apply strictly_inhabits.
    have E := f_equal ar_list_to_rocq (imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Ha (sub_imported_eq_trans _ _ _ HL (sub_imported_eq_sym _ _ Hb)))).
    rewrite !ar_list_source_roundtrip in E.
    exact E.
Qed.

Section Dbf.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
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
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let ONE := sub_nat_rel_canonical (S O).

  (** *** The absolute-deadline instance *)

  Let dlR := @prosa.model.task.absolute_deadline.job_deadline_from_task_deadline Job Task tdR jaR jtR.
  Let dlL := I.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline
    Job Task dJ dT tdL jaL jtL.

  Lemma fdbf_task_deadline_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (fdbf_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_deadline Task tdR (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL v)) _ _ (Hjt j) (Htd _)).
  Qed.

  Lemma fdbf_job_deadline_related (j : Job) :
    SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
      (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).
  Proof.
    unfold dlR, dlL, prosa.model.task.absolute_deadline.job_deadline_from_task_deadline.
    cbn [I.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline
      I.Prosa_Behavior_Job_JobDeadline_job_deadline].
    exact (svc_target_add_related _ _ _ _ (Hja j) (fdbf_task_deadline_of_job_related j)).
  Qed.

  Lemma fdbf_job_of_task_related (tsk : Task) (j : Job) :
    ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof. exact (job_of_task_related Job Task jtR jtL Hjt tsk tsk (@Lean.eq_refl _ _) j). Qed.

  (** *** The definitions *)

  Section Defs.
    Variable costR : prosa.behavior.job.JobCost Job.
    Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
    Hypothesis Hcost : SvcJobCostRel Job costR costL.

    Theorem task_demand_within_correspondence (tsk : Task) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@S.task_demand_within Task tdR Job jtR jaR arrR costR tsk t1R t2R)
        (I.Prosa_Analysis_Facts_Model_Dbf_task_demand_within Task dT tdL Job dJ jtL jaL arrL costL tsk t1L t2L).
    Proof.
      intros H1 H2. unfold S.task_demand_within.
      cbn [I.Prosa_Analysis_Facts_Model_Dbf_task_demand_within].
      exact (workload_of_jobs_correspondence Job costR costL Hcost _ _
        (fun j => ar_bool_and_related _ _ _ _
          (svc_decide_le_related _ _ _ _ (fdbf_job_deadline_related j) H2)
          (fdbf_job_of_task_related tsk j)) _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2)).
    Qed.

    Theorem total_demand_within_correspondence (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@S.total_demand_within Task tdR Job jtR jaR arrR costR t1R t2R)
        (I.Prosa_Analysis_Facts_Model_Dbf_total_demand_within Task dT tdL Job dJ jtL jaL arrL costL t1L t2L).
    Proof.
      intros H1 H2. unfold S.total_demand_within.
      cbn [I.Prosa_Analysis_Facts_Model_Dbf_total_demand_within].
      exact (workload_of_jobs_correspondence Job costR costL Hcost _ _
        (fun j => svc_decide_le_related _ _ _ _ (fdbf_job_deadline_related j) H2) _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2)).
    Qed.
  End Defs.

  (** *** Covers and predicates *)

  Definition FdbfTaskCostRel (tcR : prosa.model.task.concept.TaskCost Task)
      (tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT) : SProp :=
    forall tsk : Task, SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).

  Lemma fdbf_task_cost_source_total tcR : FdbfTaskCostRel tcR
    (I.Prosa_Model_Task_Concept_TaskCost_mk Task dT (fun tsk => sub_nat_to_imported (tcR tsk))).
  Proof. intro tsk. exact (sub_nat_rel_canonical _). Qed.

  Lemma fdbf_task_cost_target_total tcL : FdbfTaskCostRel
    ((fun tsk => sub_nat_to_rocq (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk))
      : prosa.model.task.concept.TaskCost Task) tcL.
  Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

  Lemma fdbf_job_cost_source_total costR : SvcJobCostRel Job costR
    (I.Prosa_Behavior_Job_JobCost_mk Job dJ (fun j => sub_nat_to_imported (costR j))).
  Proof. intro j. exact (sub_nat_rel_canonical _). Qed.

  Lemma fdbf_job_cost_target_total costL : SvcJobCostRel Job
    ((fun j => sub_nat_to_rocq (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j))
      : prosa.behavior.job.JobCost Job) costL.
  Proof. intro j. exact (sub_nat_rel_surjective _). Qed.

  Let cover_tc := fdbf_forall_cover_sprop _ _ FdbfTaskCostRel _ _
    fdbf_task_cost_source_total fdbf_task_cost_target_total.
  Let cover_cost := fdbf_forall_cover_sprop _ _ (SvcJobCostRel Job) _ _
    fdbf_job_cost_source_total fdbf_job_cost_target_total.
  Let cover_ma :=
    fdbf_forall_cover_sprop _ _ (CvMaxArrivalsRel Task)
      (fun cR => I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_mk Task dT (fun tsk => cv_import_fun (cR tsk)))
      (fun cL => (fun tsk => cv_export_fun (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT cL tsk))
         : prosa.model.task.arrival.curves.MaxArrivals Task)
      (MaxArrivals_source_total Task) (MaxArrivals_target_total Task).

  Lemma fdbf_list_to_target_rel (xs : seq Task) : ArListRel xs (ar_list_to_imported xs).
  Proof. exact (@Lean.eq_refl _ _). Qed.
  Lemma fdbf_list_to_source_rel (xs : I.List Task) : ArListRel (ar_list_to_rocq xs) xs.
  Proof. exact (ar_list_target_roundtrip xs). Qed.
  Let cover_ts :=
    fdbf_forall_cover_sprop _ _ (@ArListRel Task)
      ar_list_to_imported ar_list_to_rocq fdbf_list_to_target_rel fdbf_list_to_source_rel.

  Lemma fdbf_valid_job_costs_related tcR tcL (Htc : FdbfTaskCostRel tcR tcL)
      costR costL (Hcost : SvcJobCostRel Job costR costL) :
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
      (svc_decide_le_related _ _ _ _ (Hcost j)
        (fdbf_lean_transport
          (fun v => SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
            (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)))).
  Qed.

  Lemma fdbf_all_jobs_from_taskset_related tsR tsL (Hts : ArListRel tsR tsL) :
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
  Let SHIFT tsk dR dL (Hd : SubNatRel dR dL) :=
    svc_target_sub_related _ _ _ _ Hd (svc_target_sub_related _ _ _ _ (Htd tsk) ONE).
  Let RESPS tsR tsL Hts maR maL Hma :=
    taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma.

  (** *** Statements about the deadline-filtered arrivals *)

  Definition src_task_arrivals_with_deadline_within_eq : Prop :=
    ltac:(body_of (fun s : S.statement_task_arrivals_with_deadline_within_eq => s Task tdR Job jtR jaR arrR)).
  Definition tgt_task_arrivals_with_deadline_within_eq : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Dbf_task_arrivals_with_deadline_within_eq
      Task dT tdL Job dJ jtL jaL arrL)).
  Theorem task_arrivals_with_deadline_within_eq_correspondence :
    PropSPropRel src_task_arrivals_with_deadline_within_eq tgt_task_arrivals_with_deadline_within_eq.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    exact (fdbf_list_eq_correspondence Job _ _ _ _
      (task_arrivals_with_deadline_within_correspondence Job Task jtR jtL Hjt arrR arrL Harr dlR dlL
        fdbf_job_deadline_related tsk tsk _ _ _ _ (@Lean.eq_refl _ _) Ht (svc_target_add_related _ _ _ _ Ht Hd))
      (task_arrivals_between_correspondence Job Task jtR jtL Hjt arrR arrL Harr tsk tsk _ _ _ _
        (@Lean.eq_refl _ _) Ht (svc_target_add_related _ _ _ _ Ht (SHIFT tsk _ _ Hd)))).
  Qed.

  Definition src_num_task_arrivals_with_deadline_within_eq : Prop :=
    ltac:(body_of (fun s : S.statement_num_task_arrivals_with_deadline_within_eq => s Task tdR Job jtR jaR arrR)).
  Definition tgt_num_task_arrivals_with_deadline_within_eq : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Dbf_num_task_arrivals_with_deadline_within_eq
      Task dT tdL Job dJ jtL jaL arrL)).
  Theorem num_task_arrivals_with_deadline_within_eq_correspondence :
    PropSPropRel src_num_task_arrivals_with_deadline_within_eq tgt_num_task_arrivals_with_deadline_within_eq.
  Proof.
    apply ar_imp_correspondence; [exact VALID|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    exact (sub_nat_eq_correspondence _ _ _ _
      (number_of_task_arrivals_with_deadline_within_correspondence Job Task jtR jtL Hjt arrR arrL Harr dlR dlL
        fdbf_job_deadline_related tsk tsk _ _ _ _ (@Lean.eq_refl _ _) Ht (svc_target_add_related _ _ _ _ Ht Hd))
      (number_of_task_arrivals_correspondence Job Task jtR jtL Hjt arrR arrL Harr tsk tsk _ _ _ _
        (@Lean.eq_refl _ _) Ht (svc_target_add_related _ _ _ _ Ht (SHIFT tsk _ _ Hd)))).
  Qed.

  (** *** Statements over the cost and arrival-curve instances *)

  Ltac fdbf_prefix :=
    apply ar_imp_correspondence; [exact VALID|];
    apply cover_tc; let tcR := fresh "tcR" in let tcL := fresh "tcL" in let Htc := fresh "Htc" in
      intros tcR tcL Htc;
    apply cover_cost; let costR := fresh "costR" in let costL := fresh "costL" in
      let Hcost := fresh "Hcost" in intros costR costL Hcost;
    apply ar_imp_correspondence; [exact (fdbf_valid_job_costs_related _ _ Htc _ _ Hcost)|];
    apply cover_ts; let tsR := fresh "tsR" in let tsL := fresh "tsL" in let Hts := fresh "Hts" in
      intros tsR tsL Hts;
    apply cover_ma; let maR := fresh "maR" in let maL := fresh "maL" in let Hma := fresh "Hma" in
      intros maR maL Hma;
    apply ar_imp_correspondence; [exact (RESPS _ _ Hts _ _ Hma)|].

  Definition src_task_demand_within_le_task_dbf : Prop :=
    ltac:(body_of (fun s : S.statement_task_demand_within_le_task_dbf => s Task tdR Job jtR jaR arrR)).
  Definition tgt_task_demand_within_le_task_dbf : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Dbf_task_demand_within_le_task_dbf
      Task dT tdL Job dJ jtL jaL arrL)).
  Theorem task_demand_within_le_task_dbf_correspondence :
    PropSPropRel src_task_demand_within_le_task_dbf tgt_task_demand_within_le_task_dbf.
  Proof.
    fdbf_prefix.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    exact (sub_nat_le_correspondence _ _ _ _
      (task_demand_within_correspondence costR costL Hcost tsk _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht Hd))
      (task_demand_bound_function_correspondence Task tcR tcL Htc tdR tdL Htd maR maL Hma tsk _ _ Hd)).
  Qed.

  Definition src_task_demand_within_le_task_rbf_shifted : Prop :=
    ltac:(body_of (fun s : S.statement_task_demand_within_le_task_rbf_shifted => s Task tdR Job jtR jaR arrR)).
  Definition tgt_task_demand_within_le_task_rbf_shifted : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Dbf_task_demand_within_le_task_rbf_shifted
      Task dT tdL Job dJ jtL jaL arrL)).
  Theorem task_demand_within_le_task_rbf_shifted_correspondence :
    PropSPropRel src_task_demand_within_le_task_rbf_shifted tgt_task_demand_within_le_task_rbf_shifted.
  Proof.
    fdbf_prefix.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    exact (sub_nat_le_correspondence _ _ _ _
      (task_demand_within_correspondence costR costL Hcost tsk _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht Hd))
      (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _ (SHIFT tsk _ _ Hd))).
  Qed.

  Definition src_total_demand_within_le_total_dbf : Prop :=
    ltac:(body_of (fun s : S.statement_total_demand_within_le_total_dbf => s Task tdR Job jtR jaR arrR)).
  Definition tgt_total_demand_within_le_total_dbf : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Dbf_total_demand_within_le_total_dbf
      Task dT tdL Job dJ jtL jaL arrL)).
  Theorem total_demand_within_le_total_dbf_correspondence :
    PropSPropRel src_total_demand_within_le_total_dbf tgt_total_demand_within_le_total_dbf.
  Proof.
    fdbf_prefix.
    apply ar_imp_correspondence; [exact (fdbf_all_jobs_from_taskset_related _ _ Hts)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    exact (sub_nat_le_correspondence _ _ _ _
      (total_demand_within_correspondence costR costL Hcost _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht Hd))
      (total_demand_bound_function_correspondence Task tcR tcL Htc tdR tdL Htd maR maL Hma tsR tsL Hts _ _ Hd)).
  Qed.

  Definition src_total_demand_within_le_sum_task_rbf_shifted : Prop :=
    ltac:(body_of (fun s : S.statement_total_demand_within_le_sum_task_rbf_shifted => s Task tdR Job jtR jaR arrR)).
  Definition tgt_total_demand_within_le_sum_task_rbf_shifted : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Dbf_total_demand_within_le_sum_task_rbf_shifted
      Task dT tdL Job dJ jtL jaL arrL)).
  Theorem total_demand_within_le_sum_task_rbf_shifted_correspondence :
    PropSPropRel src_total_demand_within_le_sum_task_rbf_shifted tgt_total_demand_within_le_sum_task_rbf_shifted.
  Proof.
    fdbf_prefix.
    apply ar_imp_correspondence; [exact (fdbf_all_jobs_from_taskset_related _ _ Hts)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    exact (sub_nat_le_correspondence _ _ _ _
      (total_demand_within_correspondence costR costL Hcost _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht Hd))
      (rbf_sum_related Task _ _
        (fun tsk => task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk _ _
          (SHIFT tsk _ _ Hd)) _ _ Hts)).
  Qed.
End Dbf.
