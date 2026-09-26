From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsJobIndexSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsJobIndex ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence.

Module I := ImportedFactsJobIndex.
Module S := FactsJobIndexSemanticSource.FactsJobIndexSemanticSource.

(** Statement correspondences for [analysis/facts/job_index.v].

    Source side: the extracted statement [S.statement_X] specialised at the
    leading input binders ([Task], [Job], [JobTask], [JobArrival], the arrival
    sequence); target side: the type of the imported Lean theorem.  Jobs are
    identity carriers, [job_task] is related by [Lean.eq], the job-arrival
    field and instants by [SubNatRel], Boolean predicates on jobs by
    [ArPredRel] (covered in both directions).  The definition-level relations
    ([task_arrivals_*], [job_index], [prev_job], [index], [size],
    [arrivals_between_P]) are the accepted task-arrivals certificates. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fji_eq_id (T : Type) (x y : T) : PropSPropRel (x = y) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - exact (coq_eq_to_imported_eq x y).
  - intro H. apply strictly_inhabits. exact (imported_eq_to_coq_eq x y H).
Qed.

Lemma fji_not_correspondence (P : Prop) (PL : SProp) :
  PropSPropRel P PL -> PropSPropRel (~ P) (PL -> I.False).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros Hn p. exact (match Hn (sprop_to_prop _ _ HP p) with end).
  - intro Hn. apply strictly_inhabits. intro p.
    exact (match Hn (prop_to_sprop _ _ HP p) return Logic.False with end).
Qed.

Lemma fji_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [Hpq Hqp]. apply I.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ (Hpq (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP (Hqp (sprop_to_prop _ _ HQ q))).
  - intros [Hpq Hqp]. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ (Hpq (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP (Hqp (prop_to_sprop _ _ HQ q))).
Qed.

Lemma fji_exists_id (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) -> PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (H x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (H x) Hx).
Qed.

Lemma fji_mem_truth (T : eqType) (x : T) xsR xsL :
  ArListRel xsR xsL ->
  PropSPropRel (is_true (x \in xsR)) (Lean.eq (ar_target_decide_mem T x xsL) I.Bool_true).
Proof. intro H. exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related T x xsR xsL H)). Qed.

Lemma fji_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, ArPredRel pR pL -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall pR, PR pR) (forall pL, PL pL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL.
    exact (prop_to_sprop _ _ (H (fun x => ar_bool_to_rocq (pL x)) pL
      (fun x => ar_bool_target_roundtrip (pL x))) (HR _)).
  - intro HL. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ (H pR (fun x => ar_bool_to_imported (pR x))
      (fun x => @Lean.eq_refl _ _)) (HL _)).
Qed.

Section JobIndex.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
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

  Let VA := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.
  Let ARR j := arrives_in_correspondence_certificate Job arrR arrL j Harr.
  Let JI j := job_index_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j.
  Let UPTO j := task_arrivals_up_to_job_arrival_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j.
  Let PREV j := prev_job_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j.
  Let JA j := Hja j.
  Let LE := sub_nat_le_correspondence.
  Let LT := sub_nat_lt_correspondence.
  Let EQ := sub_nat_eq_correspondence.

  Lemma fji_task_eq (j1 j2 : Job) :
    PropSPropRel (@prosa.model.task.concept.job_task Job Task jtR j1 = @prosa.model.task.concept.job_task Job Task jtR j2)
      (Lean.eq (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j1)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j2)).
  Proof.
    apply prop_sprop_rel_intro.
    - intro H. refine (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ (Hjt j1)) _).
      refine (sub_imported_eq_trans _ _ _ _ (Hjt j2)).
      exact (coq_eq_to_imported_eq _ _ H).
    - intro H. apply strictly_inhabits.
      exact (imported_eq_to_coq_eq _ _
        (sub_imported_eq_trans _ _ _ (Hjt j1) (sub_imported_eq_trans _ _ _ H (sub_imported_eq_sym _ _ (Hjt j2))))).
  Qed.

  Lemma fji_prev_task_eq (j : Job) :
    PropSPropRel
      (@prosa.model.task.concept.job_task Job Task jtR (@prosa.model.task.arrivals.prev_job Job Task jtR jaR arrR j) =
        @prosa.model.task.concept.job_task Job Task jtR j)
      (Lean.eq (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL
          (I.Prosa_Model_Task_Arrivals_prev_job Job dJ Task dT jtL jaL arrL j))
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    rewrite -(imported_eq_to_coq_eq _ _ (PREV j)).
    exact (fji_task_eq _ j).
  Qed.

  Definition src_case_arrival_lte_implies_equal_job : Prop := ltac:(body_of (fun s : S.statement_case_arrival_lte_implies_equal_job => s Task Job jtR jaR arrR)).
  Definition tgt_case_arrival_lte_implies_equal_job : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_case_arrival_lte_implies_equal_job Task dT Job dJ jtL jaL arrL)).
  Theorem case_arrival_lte_implies_equal_job_correspondence : PropSPropRel src_case_arrival_lte_implies_equal_job tgt_case_arrival_lte_implies_equal_job.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply ar_imp_correspondence; [exact (ARR j1)|].
    apply ar_imp_correspondence; [exact (ARR j2)|].
    apply ar_imp_correspondence; [exact (fji_task_eq j1 j2)|].
    apply ar_imp_correspondence; [exact (EQ _ _ _ _ (JI j1) (JI j2))|].
    apply ar_imp_correspondence; [exact (LE _ _ _ _ (JA j1) (JA j2))|].
    exact (fji_eq_id Job j1 j2).
  Qed.

  Definition src_case_arrival_gt_implies_equal_job : Prop := ltac:(body_of (fun s : S.statement_case_arrival_gt_implies_equal_job => s Task Job jtR jaR arrR)).
  Definition tgt_case_arrival_gt_implies_equal_job : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_case_arrival_gt_implies_equal_job Task dT Job dJ jtL jaL arrL)).
  Theorem case_arrival_gt_implies_equal_job_correspondence : PropSPropRel src_case_arrival_gt_implies_equal_job tgt_case_arrival_gt_implies_equal_job.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply ar_imp_correspondence; [exact (ARR j1)|].
    apply ar_imp_correspondence; [exact (ARR j2)|].
    apply ar_imp_correspondence; [exact (fji_task_eq j1 j2)|].
    apply ar_imp_correspondence; [exact (EQ _ _ _ _ (JI j1) (JI j2))|].
    apply ar_imp_correspondence; [exact (LT _ _ _ _ (JA j2) (JA j1))|].
    exact (fji_eq_id Job j1 j2).
  Qed.

  Definition src_equal_index_implies_equal_jobs : Prop := ltac:(body_of (fun s : S.statement_equal_index_implies_equal_jobs => s Task Job jtR jaR arrR)).
  Definition tgt_equal_index_implies_equal_jobs : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_equal_index_implies_equal_jobs Task dT Job dJ jtL jaL arrL)).
  Theorem equal_index_implies_equal_jobs_correspondence : PropSPropRel src_equal_index_implies_equal_jobs tgt_equal_index_implies_equal_jobs.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply ar_imp_correspondence; [exact (ARR j1)|].
    apply ar_imp_correspondence; [exact (ARR j2)|].
    apply ar_imp_correspondence; [exact (fji_task_eq j1 j2)|].
    apply ar_imp_correspondence; [exact (EQ _ _ _ _ (JI j1) (JI j2))|].
    exact (fji_eq_id Job j1 j2).
  Qed.

  Definition src_diff_jobs_iff_diff_indices : Prop := ltac:(body_of (fun s : S.statement_diff_jobs_iff_diff_indices => s Task Job jtR jaR arrR)).
  Definition tgt_diff_jobs_iff_diff_indices : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_diff_jobs_iff_diff_indices Task dT Job dJ jtL jaL arrL)).
  Theorem diff_jobs_iff_diff_indices_correspondence : PropSPropRel src_diff_jobs_iff_diff_indices tgt_diff_jobs_iff_diff_indices.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply ar_imp_correspondence; [exact (ARR j1)|].
    apply ar_imp_correspondence; [exact (ARR j2)|].
    apply ar_imp_correspondence; [exact (fji_task_eq j1 j2)|].
    apply fji_iff_correspondence.
    - exact (fji_not_correspondence _ _ (fji_eq_id Job j1 j2)).
    - exact (fji_not_correspondence _ _ (EQ _ _ _ _ (JI j1) (JI j2))).
  Qed.

  Definition src_index_as_sum_size_and_index : Prop := ltac:(body_of (fun s : S.statement_index_as_sum_size_and_index => s Task Job jtR jaR arrR)).
  Definition tgt_index_as_sum_size_and_index : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_index_as_sum_size_and_index Task dT Job dJ jtL jaL arrL)).
  Theorem index_as_sum_size_and_index_correspondence : PropSPropRel src_index_as_sum_size_and_index tgt_index_as_sum_size_and_index.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_imp_correspondence; [exact (ARR j1)|].
    exact (EQ _ _ _ _ (JI j1) (sub_add_correspondence _ _ _ _
      (ari_size_related Job _ _ (task_arrivals_before_job_arrival_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j1))
      (ari_index_related Job j1 _ _ (task_arrivals_at_job_arrival_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j1)))).
  Qed.

  Definition src_arrival_lt_implies_job_in_arrivals_between_P : Prop := ltac:(body_of (fun s : S.statement_arrival_lt_implies_job_in_arrivals_between_P => s Job jaR arrR)).
  Definition tgt_arrival_lt_implies_job_in_arrivals_between_P : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_arrival_lt_implies_job_in_arrivals_between_P Job dJ jaL arrL)).
  Theorem arrival_lt_implies_job_in_arrivals_between_P_correspondence : PropSPropRel src_arrival_lt_implies_job_in_arrivals_between_P tgt_arrival_lt_implies_job_in_arrivals_between_P.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply fji_forall_pred => pR pL Hp.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    have BP := arrivals_between_P_correspondence_certificate Job arrR arrL pR pL Harr Hp _ _ _ _ H1 H2.
    apply ar_imp_correspondence; [exact (fji_mem_truth Job j1 _ _ BP)|].
    apply ar_imp_correspondence; [exact (fji_mem_truth Job j2 _ _ BP)|].
    apply ar_imp_correspondence; [exact (LT _ _ _ _ (JA j2) (JA j1))|].
    exact (fji_mem_truth Job j2 _ _
      (arrivals_between_P_correspondence_certificate Job arrR arrL pR pL Harr Hp _ _ _ _ H1 (JA j1))).
  Qed.

  Definition src_index_lte_implies_arrival_lte_P : Prop := ltac:(body_of (fun s : S.statement_index_lte_implies_arrival_lte_P => s Job jaR arrR)).
  Definition tgt_index_lte_implies_arrival_lte_P : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_index_lte_implies_arrival_lte_P Job dJ jaL arrL)).
  Theorem index_lte_implies_arrival_lte_P_correspondence : PropSPropRel src_index_lte_implies_arrival_lte_P tgt_index_lte_implies_arrival_lte_P.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply fji_forall_pred => pR pL Hp.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    have BP := arrivals_between_P_correspondence_certificate Job arrR arrL pR pL Harr Hp _ _ _ _ H1 H2.
    apply ar_imp_correspondence; [exact (fji_mem_truth Job j1 _ _ BP)|].
    apply ar_imp_correspondence; [exact (fji_mem_truth Job j2 _ _ BP)|].
    apply ar_imp_correspondence;
      [exact (LE _ _ _ _ (ari_index_related Job j1 _ _ BP) (ari_index_related Job j2 _ _ BP))|].
    exact (LE _ _ _ _ (JA j1) (JA j2)).
  Qed.

  Definition src_job_index_same_in_task_arrivals : Prop := ltac:(body_of (fun s : S.statement_job_index_same_in_task_arrivals => s Task Job jtR jaR arrR)).
  Definition tgt_job_index_same_in_task_arrivals : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_job_index_same_in_task_arrivals Task dT Job dJ jtL jaL arrL)).
  Theorem job_index_same_in_task_arrivals_correspondence : PropSPropRel src_job_index_same_in_task_arrivals tgt_job_index_same_in_task_arrivals.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply ar_imp_correspondence; [exact (ARR j1)|].
    apply ar_imp_correspondence; [exact (ARR j2)|].
    apply ar_imp_correspondence; [exact (fji_task_eq j1 j2)|].
    apply ar_imp_correspondence; [exact (LE _ _ _ _ (JA j1) (JA j2))|].
    exact (EQ _ _ _ _ (ari_index_related Job j1 _ _ (UPTO j1)) (ari_index_related Job j1 _ _ (UPTO j2))).
  Qed.

  Definition src_index_job_lt_size_task_arrivals_up_to_job : Prop := ltac:(body_of (fun s : S.statement_index_job_lt_size_task_arrivals_up_to_job => s Task Job jtR jaR arrR)).
  Definition tgt_index_job_lt_size_task_arrivals_up_to_job : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_index_job_lt_size_task_arrivals_up_to_job Task dT Job dJ jtL jaL arrL)).
  Theorem index_job_lt_size_task_arrivals_up_to_job_correspondence : PropSPropRel src_index_job_lt_size_task_arrivals_up_to_job tgt_index_job_lt_size_task_arrivals_up_to_job.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_imp_correspondence; [exact (ARR j1)|].
    exact (LT _ _ _ _ (JI j1) (ari_size_related Job _ _ (UPTO j1))).
  Qed.

  Definition src_index_lte_implies_arrival_lte : Prop := ltac:(body_of (fun s : S.statement_index_lte_implies_arrival_lte => s Task Job jtR jaR arrR)).
  Definition tgt_index_lte_implies_arrival_lte : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_index_lte_implies_arrival_lte Task dT Job dJ jtL jaL arrL)).
  Theorem index_lte_implies_arrival_lte_correspondence : PropSPropRel src_index_lte_implies_arrival_lte tgt_index_lte_implies_arrival_lte.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply ar_imp_correspondence; [exact (ARR j1)|].
    apply ar_imp_correspondence; [exact (ARR j2)|].
    apply ar_imp_correspondence; [exact (fji_task_eq j1 j2)|].
    apply ar_imp_correspondence; [exact (LE _ _ _ _ (JI j2) (JI j1))|].
    exact (LE _ _ _ _ (JA j2) (JA j1)).
  Qed.

  Definition src_earlier_arrival_implies_lower_index : Prop := ltac:(body_of (fun s : S.statement_earlier_arrival_implies_lower_index => s Task Job jtR jaR arrR)).
  Definition tgt_earlier_arrival_implies_lower_index : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_earlier_arrival_implies_lower_index Task dT Job dJ jtL jaL arrL)).
  Theorem earlier_arrival_implies_lower_index_correspondence : PropSPropRel src_earlier_arrival_implies_lower_index tgt_earlier_arrival_implies_lower_index.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply ar_imp_correspondence; [exact (ARR j1)|].
    apply ar_imp_correspondence; [exact (ARR j2)|].
    apply ar_imp_correspondence; [exact (fji_task_eq j1 j2)|].
    apply ar_imp_correspondence; [exact (LT _ _ _ _ (JA j1) (JA j2))|].
    exact (LT _ _ _ _ (JI j1) (JI j2)).
  Qed.

  Definition src_job_index_minus_one_lt_size_task_arrivals_up_to : Prop := ltac:(body_of (fun s : S.statement_job_index_minus_one_lt_size_task_arrivals_up_to => s Task Job jtR jaR arrR)).
  Definition tgt_job_index_minus_one_lt_size_task_arrivals_up_to : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_job_index_minus_one_lt_size_task_arrivals_up_to Task dT Job dJ jtL jaL arrL)).
  Theorem job_index_minus_one_lt_size_task_arrivals_up_to_correspondence : PropSPropRel src_job_index_minus_one_lt_size_task_arrivals_up_to tgt_job_index_minus_one_lt_size_task_arrivals_up_to.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_imp_correspondence; [exact (ARR j1)|].
    exact (LT _ _ _ _ (ari_nat_sub_related _ _ 1 _ (JI j1) (@Lean.eq_refl _ _)) (ari_size_related Job _ _ (UPTO j1))).
  Qed.

  Definition src_positive_job_index_implies_positive_size_of_task_arrivals : Prop := ltac:(body_of (fun s : S.statement_positive_job_index_implies_positive_size_of_task_arrivals => s Task Job jtR jaR arrR)).
  Definition tgt_positive_job_index_implies_positive_size_of_task_arrivals : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_positive_job_index_implies_positive_size_of_task_arrivals Task dT Job dJ jtL jaL arrL)).
  Theorem positive_job_index_implies_positive_size_of_task_arrivals_correspondence : PropSPropRel src_positive_job_index_implies_positive_size_of_task_arrivals tgt_positive_job_index_implies_positive_size_of_task_arrivals.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_imp_correspondence; [exact (ARR j1)|].
    exact (LT _ _ _ _ (sub_nat_rel_canonical O) (ari_size_related Job _ _ (UPTO j1))).
  Qed.

  Definition src_prev_job_arr : Prop := ltac:(body_of (fun s : S.statement_prev_job_arr => s Task Job jtR jaR arrR)).
  Definition tgt_prev_job_arr : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_prev_job_arr Task dT Job dJ jtL jaL arrL)).
  Theorem prev_job_arr_correspondence : PropSPropRel src_prev_job_arr tgt_prev_job_arr.
  Proof.
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (ARR j)|].
    rewrite -(imported_eq_to_coq_eq _ _ (PREV j)).
    exact (ARR _).
  Qed.

  Definition src_prev_job_index : Prop := ltac:(body_of (fun s : S.statement_prev_job_index => s Task Job jtR jaR arrR)).
  Definition tgt_prev_job_index : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_prev_job_index Task dT Job dJ jtL jaL arrL)).
  Theorem prev_job_index_correspondence : PropSPropRel src_prev_job_index tgt_prev_job_index.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (ARR j)|].
    apply ar_imp_correspondence; [exact (LT _ _ _ _ (sub_nat_rel_canonical O) (JI j))|].
    rewrite -(imported_eq_to_coq_eq _ _ (PREV j)).
    exact (EQ _ _ _ _ (ari_index_related Job _ _ _ (UPTO j)) (ari_nat_sub_related _ _ 1 _ (JI j) (@Lean.eq_refl _ _))).
  Qed.

  Definition src_prev_job_task : Prop := ltac:(body_of (fun s : S.statement_prev_job_task => s Task Job jtR jaR arrR)).
  Definition tgt_prev_job_task : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_prev_job_task Task dT Job dJ jtL jaL arrL)).
  Theorem prev_job_task_correspondence : PropSPropRel src_prev_job_task tgt_prev_job_task.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (ARR j)|].
    apply ar_imp_correspondence; [exact (LT _ _ _ _ (sub_nat_rel_canonical O) (JI j))|].
    exact (fji_prev_task_eq j).
  Qed.

  Definition src_prev_job_in_task_arrivals_up_to_j : Prop := ltac:(body_of (fun s : S.statement_prev_job_in_task_arrivals_up_to_j => s Task Job jtR jaR arrR)).
  Definition tgt_prev_job_in_task_arrivals_up_to_j : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_prev_job_in_task_arrivals_up_to_j Task dT Job dJ jtL jaL arrL)).
  Theorem prev_job_in_task_arrivals_up_to_j_correspondence : PropSPropRel src_prev_job_in_task_arrivals_up_to_j tgt_prev_job_in_task_arrivals_up_to_j.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (ARR j)|].
    rewrite -(imported_eq_to_coq_eq _ _ (PREV j)).
    exact (fji_mem_truth Job _ _ _ (UPTO j)).
  Qed.

  Definition src_prev_job_arr_lte : Prop := ltac:(body_of (fun s : S.statement_prev_job_arr_lte => s Task Job jtR jaR arrR)).
  Definition tgt_prev_job_arr_lte : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_prev_job_arr_lte Task dT Job dJ jtL jaL arrL)).
  Theorem prev_job_arr_lte_correspondence : PropSPropRel src_prev_job_arr_lte tgt_prev_job_arr_lte.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (ARR j)|].
    apply ar_imp_correspondence; [exact (LT _ _ _ _ (sub_nat_rel_canonical O) (JI j))|].
    rewrite -(imported_eq_to_coq_eq _ _ (PREV j)).
    exact (LE _ _ _ _ (JA _) (JA j)).
  Qed.

  Definition src_prev_job_index_j : Prop := ltac:(body_of (fun s : S.statement_prev_job_index_j => s Task Job jtR jaR arrR)).
  Definition tgt_prev_job_index_j : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_prev_job_index_j Task dT Job dJ jtL jaL arrL)).
  Theorem prev_job_index_j_correspondence : PropSPropRel src_prev_job_index_j tgt_prev_job_index_j.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (ARR j)|].
    apply ar_imp_correspondence; [exact (LT _ _ _ _ (sub_nat_rel_canonical O) (JI j))|].
    apply ar_imp_correspondence; [exact (LT _ _ _ _ (sub_nat_rel_canonical O) (JI j))|].
    rewrite -(imported_eq_to_coq_eq _ _ (PREV j)).
    exact (EQ _ _ _ _ (JI _) (ari_nat_sub_related _ _ 1 _ (JI j) (@Lean.eq_refl _ _))).
  Qed.

  Definition src_no_jobs_between_consecutive_jobs : Prop := ltac:(body_of (fun s : S.statement_no_jobs_between_consecutive_jobs => s Task Job jtR jaR arrR)).
  Definition tgt_no_jobs_between_consecutive_jobs : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_no_jobs_between_consecutive_jobs Task dT Job dJ jtL jaL arrL)).
  Theorem no_jobs_between_consecutive_jobs_correspondence : PropSPropRel src_no_jobs_between_consecutive_jobs tgt_no_jobs_between_consecutive_jobs.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (ARR j)|].
    apply ar_imp_correspondence; [exact (LT _ _ _ _ (sub_nat_rel_canonical O) (JI j))|].
    apply ar_imp_correspondence; [exact (LT _ _ _ _ (sub_nat_rel_canonical O) (JI j))|].
    rewrite -(imported_eq_to_coq_eq _ _ (PREV j)).
    exact (ar_list_eq_correspondence Job _ [::] _ (I.List_nil Job)
      (task_arrivals_between_correspondence Job Task jtR jtL Hjt arrR arrL Harr _ _ _ _ _ _ (Hjt j)
        (ari_succ_related _ _ (JA _)) (JA j))
      (@Lean.eq_refl _ _)).
  Qed.

  Definition src_exists_jobs_before_j : Prop := ltac:(body_of (fun s : S.statement_exists_jobs_before_j => s Task Job jtR jaR arrR)).
  Definition tgt_exists_jobs_before_j : SProp := ltac:(type_of_term (@I.Prosa_Analysis_Facts_JobIndex_exists_jobs_before_j Task dT Job dJ jtL jaL arrL)).
  Theorem exists_jobs_before_j_correspondence : PropSPropRel src_exists_jobs_before_j tgt_exists_jobs_before_j.
  Proof.
    apply ar_imp_correspondence; [exact VA|].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (ARR j)|].
    apply ar_forall_nat_correspondence => kR kL Hk.
    apply ar_imp_correspondence; [exact (LT _ _ _ _ Hk (JI j))|].
    apply fji_exists_id => j'.
    apply ar_and_correspondence; [exact (fji_not_correspondence _ _ (fji_eq_id Job j j'))|].
    apply ar_and_correspondence; [exact (fji_task_eq j' j)|].
    apply ar_and_correspondence; [exact (ARR j')|].
    exact (EQ _ _ _ _ (JI j') Hk).
  Qed.
End JobIndex.
