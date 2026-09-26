From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import FactsArrivalCurvesSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsArrivalCurves ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence CurvesCorrespondence.

Module I := ImportedFactsArrivalCurves.
Module S := FactsArrivalCurvesSemanticSource.FactsArrivalCurvesSemanticSource.

(** Statement correspondences for [analysis/facts/model/arrival_curves.v].

    Source side: the extracted statement [S.statement_X] specialised at its
    leading input binders (task/job types, the arrival-curve class, the
    job-task map, the priority policy, the arrival sequence and task set);
    target side: the type of the imported Lean theorem.  Inputs: arrival
    curves ([CvMaxArrivalsRel], accepted two-way totals), [job_task] by
    [Lean.eq], JLFP/FP policies pointwise on Booleans (two-way totals below),
    arrival sequences and task sets by the accepted relations.  Sums: MathComp
    [\sum_(x <- s) F x] against [List.sum ∘ List.map] (accepted
    [ari_sum_related]); filtered sums through [big_filter]. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Definition FacJLFPRel (Job : eqType)
    (pR : prosa.model.priority.definitions.JLFP_policy Job)
    (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job (ar_decidable_eq Job)) : SProp :=
  forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job (ar_decidable_eq Job) pL x y).

Lemma JLFP_policy_source_total (Job : eqType) pR :
  FacJLFPRel Job pR
    (I.Prosa_Model_Priority_Definitions_JLFP_policy_mk Job (ar_decidable_eq Job)
      (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_job Job pR x y))).
Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

Lemma JLFP_policy_target_total (Job : eqType) pL :
  FacJLFPRel Job
    (fun x y => ar_bool_to_rocq
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job (ar_decidable_eq Job) pL x y)) pL.
Proof. intros x y. exact (ar_bool_target_roundtrip _). Qed.

Definition FacFPRel (Task : eqType)
    (pR : prosa.model.priority.definitions.FP_policy Task)
    (pL : I.Prosa_Model_Priority_Definitions_FP_policy Task (ar_decidable_eq Task)) : SProp :=
  forall x y : Task,
    ArBoolRel (@prosa.model.priority.definitions.hep_task Task pR x y)
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task (ar_decidable_eq Task) pL x y).

Lemma FP_policy_source_total (Task : eqType) pR :
  FacFPRel Task pR
    (I.Prosa_Model_Priority_Definitions_FP_policy_mk Task (ar_decidable_eq Task)
      (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_task Task pR x y))).
Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

Lemma FP_policy_target_total (Task : eqType) pL :
  FacFPRel Task
    (fun x y => ar_bool_to_rocq
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task (ar_decidable_eq Task) pL x y)) pL.
Proof. intros x y. exact (ar_bool_target_roundtrip _). Qed.

Lemma fac_sum_filter_related (T : Type) (PR : T -> bool) (PL : T -> I.Bool)
    (FR : T -> nat) (FL : T -> Lean.Nat) xsR xsL :
  ArPredRel PR PL -> (forall x, SubNatRel (FR x) (FL x)) -> ArListRel xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (ari_list_sum T FL (ar_target_filter PL xsL)).
Proof.
  intros HP HF Hxs. rewrite -big_filter.
  exact (ari_sum_related T FR FL _ _ HF (ar_filter_related T PR PL xsR xsL HP Hxs)).
Qed.

Section ArrivalCurves.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : CvMaxArrivalsRel Task maR maL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma fac_all_jobs_from_taskset_related tsR tsL :
    ArListRel tsR tsL ->
    PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
      (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
  Proof.
    intro Hts.
    unfold prosa.model.task.concept.all_jobs_from_taskset.
    cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    rewrite -(imported_eq_to_coq_eq _ _ (Hjt j)).
    exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task _ _ _ Hts)).
  Qed.

  Section NonPathological.
    Variable tsk : Task.
    Definition src_non_pathological_max_arrivals : Prop :=
      ltac:(body_of (fun s : S.statement_non_pathological_max_arrivals => s Task maR Job jtR tsk arrR)).
    Definition tgt_non_pathological_max_arrivals : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ArrivalCurves_non_pathological_max_arrivals
        Task dT maL Job dJ jtL tsk arrL)).
    Theorem non_pathological_max_arrivals_correspondence :
      PropSPropRel src_non_pathological_max_arrivals tgt_non_pathological_max_arrivals.
    Proof.
      apply ar_imp_correspondence;
        [exact (respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsk _ _ (Hma tsk))|].
      apply ar_forall_identity_correspondence => j.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (job_of_task_related Job Task jtR jtL Hjt tsk tsk (@Lean.eq_refl _ _) j))|].
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O)
        (Hma tsk (S O) _ (sub_nat_rel_canonical (S O)))).
    Qed.
  End NonPathological.

  Section Bounds.
    Variable tsR : seq Task.
    Variable tsL : I.List Task.
    Hypothesis Hts : ArListRel tsR tsL.
    Let RESP := taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma.
    Let WIN (t1R : nat) (t1L : Lean.Nat) (dR : nat) (dL : Lean.Nat)
        (H1 : SubNatRel t1R t1L) (Hd : SubNatRel dR dL) :=
      arrivals_between_correspondence_certificate Job arrR arrL Harr t1R t1L _ _ H1
        (sub_add_correspondence _ _ _ _ H1 Hd).

    Section JLFP.
      Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
      Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
      Hypothesis Hp : FacJLFPRel Job pR pL.
      Definition src_jlfp_hep_arrivals_bounded_by_sum_max_arrivals : Prop :=
        ltac:(body_of (fun s : S.statement_jlfp_hep_arrivals_bounded_by_sum_max_arrivals =>
          s Task maR Job jtR pR arrR tsR)).
      Definition tgt_jlfp_hep_arrivals_bounded_by_sum_max_arrivals : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ArrivalCurves_jlfp_hep_arrivals_bounded_by_sum_max_arrivals
          Task dT maL Job dJ jtL pL arrL tsL)).
      Theorem jlfp_hep_arrivals_bounded_by_sum_max_arrivals_correspondence :
        PropSPropRel src_jlfp_hep_arrivals_bounded_by_sum_max_arrivals
          tgt_jlfp_hep_arrivals_bounded_by_sum_max_arrivals.
      Proof.
        apply ar_imp_correspondence; [exact (fac_all_jobs_from_taskset_related tsR tsL Hts)|].
        apply ar_imp_correspondence; [exact RESP|].
        apply ar_forall_identity_correspondence => j.
        apply ar_forall_nat_correspondence => t1R t1L H1.
        apply ar_forall_nat_correspondence => dR dL Hd.
        exact (sub_nat_le_correspondence _ _ _ _
          (ari_size_related Job _ _ (ar_filter_related Job _ _ _ _ (fun x => Hp x j) (WIN _ _ _ _ H1 Hd)))
          (ari_sum_related Task _ _ _ _ (fun tsk => Hma tsk _ _ Hd) Hts)).
      Qed.
    End JLFP.

    Section FP.
      Variable fR : prosa.model.priority.definitions.FP_policy Task.
      Variable fL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
      Hypothesis Hf : FacFPRel Task fR fL.
      Lemma fac_fp_hep_job_related (x y : Job) :
        ArBoolRel (@prosa.model.priority.definitions.hep_job Job
            (@prosa.model.priority.coercion.FP_to_JLFP Job Task jtR fR) x y)
          (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ
            (I.Prosa_Model_Priority_Coercion_FP_to_JLFP Job dJ Task dT jtL fL) x y).
      Proof.
        change (ArBoolRel (@prosa.model.priority.definitions.hep_task Task fR
            (@prosa.model.task.concept.job_task Job Task jtR x) (@prosa.model.task.concept.job_task Job Task jtR y))
          (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL
            (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL x)
            (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))).
        refine (ari_lean_transport (fun v => ArBoolRel _
          (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL v
            (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))) _ _ (Hjt x) _).
        refine (ari_lean_transport (fun v => ArBoolRel _
          (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL
            (@prosa.model.task.concept.job_task Job Task jtR x) v)) _ _ (Hjt y) _).
        exact (Hf _ _).
      Qed.

      Lemma fac_fp_task_pred (j : Job) :
        ArPredRel (fun tsk => @prosa.model.priority.definitions.hep_task Task fR tsk
              (@prosa.model.task.concept.job_task Job Task jtR j))
            (fun tsk => I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL tsk
              (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
      Proof.
        intro tsk.
        refine (ari_lean_transport (fun v => ArBoolRel _
          (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL tsk v)) _ _ (Hjt j) _).
        exact (Hf _ _).
      Qed.
      Definition src_fp_hep_arrivals_bounded_by_sum_max_arrivals : Prop :=
        ltac:(body_of (fun s : S.statement_fp_hep_arrivals_bounded_by_sum_max_arrivals =>
          s Task maR Job jtR fR arrR tsR)).
      Definition tgt_fp_hep_arrivals_bounded_by_sum_max_arrivals : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ArrivalCurves_fp_hep_arrivals_bounded_by_sum_max_arrivals
          Task dT maL Job dJ jtL fL arrL tsL)).
      Theorem fp_hep_arrivals_bounded_by_sum_max_arrivals_correspondence :
        PropSPropRel src_fp_hep_arrivals_bounded_by_sum_max_arrivals
          tgt_fp_hep_arrivals_bounded_by_sum_max_arrivals.
      Proof.
        apply ar_imp_correspondence; [exact (fac_all_jobs_from_taskset_related tsR tsL Hts)|].
        apply ar_imp_correspondence; [exact RESP|].
        apply ar_forall_identity_correspondence => j.
        apply ar_forall_nat_correspondence => t1R t1L H1.
        apply ar_forall_nat_correspondence => dR dL Hd.
        exact (sub_nat_le_correspondence _ _ _ _
          (ari_size_related Job _ _ (ar_filter_related Job _ _ _ _ (fun x => fac_fp_hep_job_related x j)
            (WIN _ _ _ _ H1 Hd)))
          (fac_sum_filter_related Task _ _ _ _ _ _ (fac_fp_task_pred j) (fun tsk => Hma tsk _ _ Hd) Hts)).
      Qed.
    End FP.
  End Bounds.
End ArrivalCurves.
