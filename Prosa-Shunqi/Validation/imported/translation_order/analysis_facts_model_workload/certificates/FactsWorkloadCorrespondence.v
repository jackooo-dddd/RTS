From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import FactsWorkloadSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsWorkload ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  WorkloadCorrespondence.

Module I := ImportedFactsWorkload.
Module S := FactsWorkloadSemanticSource.FactsWorkloadSemanticSource.

(** Statement correspondences for [analysis/facts/model/workload.v].

    Source side: the extracted statement [S.statement_X] specialised at its
    leading inputs (task and job types, the [JobTask]/[JobArrival]/[JobCost]
    classes and the JLFP policy when they are leading binders, the arrival
    sequence when leading); target side: the type of the imported Lean
    theorem at related inputs ([job_cost] pointwise by [SubNatRel],
    [job_task] by [Lean.eq], [ArJobArrivalRel], JLFP policies pointwise on
    Booleans, [ArArrivalSequenceRel]).  Job and task predicates and lists,
    jobs, tasks and instants bound later are covered in both directions.
    Workload definitions are the accepted workload certificates re-bound to
    this artifact.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators *)

Lemma fwk_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Lemma fwk_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma fwk_pred_rel_canonical {T : Type} (f : T -> bool) :
  ArPredRel f (fun x => ar_bool_to_imported (f x)).
Proof. intro x. exact (@Lean.eq_refl _ _). Qed.

Lemma fwk_pred_rel_surjective {T : Type} (g : T -> I.Bool) :
  ArPredRel (fun x => ar_bool_to_rocq (g x)) g.
Proof. intro x. exact (ar_bool_target_roundtrip (g x)). Qed.

Definition fwk_cover_pred (T : Type) :=
  fwk_forall_cover_sprop (T -> bool) (T -> I.Bool) ArPredRel
    (fun f x => ar_bool_to_imported (f x)) (fun g x => ar_bool_to_rocq (g x))
    fwk_pred_rel_canonical fwk_pred_rel_surjective.

Lemma fwk_list_rel_canonical {T : Type} (xs : seq T) : ArListRel xs (ar_list_to_imported xs).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma fwk_list_rel_surjective {T : Type} (xs : I.List T) : ArListRel (ar_list_to_rocq xs) xs.
Proof. exact (ar_list_target_roundtrip xs). Qed.

Definition fwk_cover_list (T : Type) :=
  fwk_forall_cover_sprop (seq T) (I.List T) ArListRel
    ar_list_to_imported ar_list_to_rocq fwk_list_rel_canonical fwk_list_rel_surjective.

Lemma fwk_bool_eq_correspondence (bR cR : bool) (bL cL : I.Bool) :
  ArBoolRel bR bL -> ArBoolRel cR cL -> PropSPropRel (bR = cR) (Lean.eq bL cL).
Proof.
  intros Hb Hc. apply prop_sprop_rel_intro.
  - intro E. destruct E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hb) Hc).
  - intro E. apply strictly_inhabits.
    have EL := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hb (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hc))).
    destruct bR, cR; cbn in EL; solve [reflexivity | discriminate EL].
Qed.

Lemma fwk_bool_not_related (bR : bool) (bL : I.Bool) :
  ArBoolRel bR bL -> ArBoolRel (~~ bR) (I.Bool_not bL).
Proof.
  intro H. unfold ArBoolRel in *. destruct H. destruct bR; exact (@Lean.eq_refl _ _).
Qed.

Lemma fwk_cond_related (bR : bool) (bL : I.Bool) (xR : nat) (xL : Lean.Nat) :
  ArBoolRel bR bL -> SubNatRel xR xL ->
  SubNatRel (if bR then xR else O) (I.cond I.Prosa_Behavior_Job_work bL xL
    (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Job_work 0 (I.instOfNatNat 0))).
Proof.
  intros Hb Hx. unfold ArBoolRel in Hb. destruct Hb.
  destruct bR; cbn; [exact Hx | exact (sub_nat_rel_canonical O)].
Qed.

(** ** Job-level predicates *)

Section Preds.
  Context (Task Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let dT := ar_decidable_eq Task.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).

  Lemma fwk_job_task_eq_related (j : Job) (tsk : Task) :
    ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
      (I.Decidable_decide (Lean.eq (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j) tsk)
        (ar_decidable_eq Task (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j) tsk)).
  Proof.
    exact (fwk_lean_transport
      (fun x => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
         (I.Decidable_decide (Lean.eq x tsk) (ar_decidable_eq Task x tsk)))
      _ _ (Hjt j) (ari_decide_eq_related Task _ tsk)).
  Qed.

  Lemma fwk_job_task_mem_related (j : Job) tsR tsL :
    ArListRel tsR tsL ->
    ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j \in tsR)
      (ar_target_decide_mem Task (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j) tsL).
  Proof.
    intro Hts.
    exact (fwk_lean_transport
      (fun x => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j \in tsR)
         (ar_target_decide_mem Task x tsL))
      _ _ (Hjt j) (ar_decide_mem_related Task _ tsR tsL Hts)).
  Qed.

  Section Priority.
    Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
    Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
    Hypothesis Hp : forall x y : Job,
      ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
        (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

    Lemma fwk_another_hep_job_related (x y : Job) :
      ArBoolRel (@prosa.model.priority.definitions.another_hep_job Job pR x y)
        (I.Prosa_Model_Priority_Definitions_another_hep_job Job dJ pL x y).
    Proof.
      unfold prosa.model.priority.definitions.another_hep_job.
      cbn [I.Prosa_Model_Priority_Definitions_another_hep_job].
      exact (ar_bool_and_related _ _ _ _ (Hp x y) (wl_ne_observation Job x y)).
    Qed.

    Lemma fwk_another_task_hep_job_related (x y : Job) :
      ArBoolRel (@prosa.model.priority.definitions.another_task_hep_job Task Job jtR pR x y)
        (I.Prosa_Model_Priority_Definitions_another_task_hep_job Task dT Job dJ jtL pL x y).
    Proof.
      unfold prosa.model.priority.definitions.another_task_hep_job.
      cbn [I.Prosa_Model_Priority_Definitions_another_task_hep_job].
      apply (ar_bool_and_related _ _ _ _ (Hp x y)).
      exact (fwk_lean_transport
        (fun a => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR x !=
             @prosa.model.task.concept.job_task Job Task jtR y)
           (I.Decidable_decide (I.Ne Task a (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))
              (I.instDecidableNot (Lean.eq a (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))
                 (ar_decidable_eq Task a (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y)))))
        _ _ (Hjt x)
        (fwk_lean_transport
          (fun b => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR x !=
               @prosa.model.task.concept.job_task Job Task jtR y)
             (I.Decidable_decide (I.Ne Task (@prosa.model.task.concept.job_task Job Task jtR x) b)
                (I.instDecidableNot (Lean.eq (@prosa.model.task.concept.job_task Job Task jtR x) b)
                   (ar_decidable_eq Task (@prosa.model.task.concept.job_task Job Task jtR x) b))))
          _ _ (Hjt y) (wl_ne_observation Task _ _))).
    Qed.

    Lemma fwk_another_hep_job_of_same_task_related (x y : Job) :
      ArBoolRel (@prosa.model.priority.definitions.another_hep_job_of_same_task Task Job jtR pR x y)
        (I.Prosa_Model_Priority_Definitions_another_hep_job_of_same_task Task dT Job dJ jtL pL x y).
    Proof.
      unfold prosa.model.priority.definitions.another_hep_job_of_same_task.
      cbn [I.Prosa_Model_Priority_Definitions_another_hep_job_of_same_task].
      apply (ar_bool_and_related _ _ _ _ (fwk_another_hep_job_related x y)).
      exact (fwk_lean_transport
        (fun a => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR x ==
             @prosa.model.task.concept.job_task Job Task jtR y)
           (I.Decidable_decide (Lean.eq a (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))
              (ar_decidable_eq Task a (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))))
        _ _ (Hjt x)
        (fwk_lean_transport
          (fun b => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR x ==
               @prosa.model.task.concept.job_task Job Task jtR y)
             (I.Decidable_decide (Lean.eq (@prosa.model.task.concept.job_task Job Task jtR x) b)
                (ar_decidable_eq Task (@prosa.model.task.concept.job_task Job Task jtR x) b)))
          _ _ (Hjt y) (ari_decide_eq_related Task _ _))).
    Qed.
  End Priority.
End Preds.

(** ** Statements *)

Section Statements.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).

  Let WL := workload_of_jobs_correspondence Job costR costL Hcost.
  Let cover_pred := fwk_cover_pred Job.
  Let cover_list := fwk_cover_list Job.

  Lemma fwk_mem_truth (j : Job) jsR jsL :
    ArListRel jsR jsL ->
    PropSPropRel (is_true (j \in jsR)) (Lean.eq (ar_target_decide_mem Job j jsL) I.Bool_true).
  Proof. intro H. exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Job j jsR jsL H)). Qed.

  Definition src_workload_of_jobs_filter : Prop :=
    ltac:(body_of (fun s : S.statement_workload_of_jobs_filter => s Job costR)).
  Definition tgt_workload_of_jobs_filter : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_filter Job dJ costL)).
  Theorem workload_of_jobs_filter_correspondence :
    PropSPropRel src_workload_of_jobs_filter tgt_workload_of_jobs_filter.
  Proof.
    apply cover_pred. intros P1R P1L H1.
    apply cover_pred. intros P2R P2L H2.
    apply cover_list. intros jR jL Hj.
    apply ar_imp_correspondence.
    - apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (fwk_mem_truth j _ _ Hj)|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (H1 j))|].
      exact (ar_bool_truth_correspondence _ _ (H2 j)).
    - exact (sub_nat_eq_correspondence _ _ _ _ (WL P1R P1L H1 jR jL Hj)
        (WL P1R P1L H1 _ _ (ar_filter_related Job P2R P2L jR jL H2 Hj))).
  Qed.

  Definition src_workload_of_jobs_weaken : Prop :=
    ltac:(body_of (fun s : S.statement_workload_of_jobs_weaken => s Job costR)).
  Definition tgt_workload_of_jobs_weaken : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_weaken Job dJ costL)).
  Theorem workload_of_jobs_weaken_correspondence :
    PropSPropRel src_workload_of_jobs_weaken tgt_workload_of_jobs_weaken.
  Proof.
    apply cover_pred. intros P1R P1L H1.
    apply cover_pred. intros P2R P2L H2.
    apply cover_list. intros jR jL Hj.
    apply ar_imp_correspondence.
    - apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (H1 j))|].
      exact (ar_bool_truth_correspondence _ _ (H2 j)).
    - exact (sub_nat_le_correspondence _ _ _ _ (WL P1R P1L H1 jR jL Hj) (WL P2R P2L H2 jR jL Hj)).
  Qed.

  Definition src_workload_of_jobs0 : Prop :=
    ltac:(body_of (fun s : S.statement_workload_of_jobs0 => s Job costR)).
  Definition tgt_workload_of_jobs0 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_of_jobs0 Job dJ costL)).
  Theorem workload_of_jobs0_correspondence :
    PropSPropRel src_workload_of_jobs0 tgt_workload_of_jobs0.
  Proof.
    apply cover_pred. intros PR PL HP.
    exact (sub_nat_eq_correspondence _ _ _ _ (WL PR PL HP [::] _ (@Lean.eq_refl _ _))
      (sub_nat_rel_canonical O)).
  Qed.

  Definition src_workload_of_jobs_pred0 : Prop :=
    ltac:(body_of (fun s : S.statement_workload_of_jobs_pred0 => s Job costR)).
  Definition tgt_workload_of_jobs_pred0 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_pred0 Job dJ costL)).
  Theorem workload_of_jobs_pred0_correspondence :
    PropSPropRel src_workload_of_jobs_pred0 tgt_workload_of_jobs_pred0.
  Proof.
    apply cover_list. intros jR jL Hj.
    exact (sub_nat_eq_correspondence _ _ _ _
      (WL pred0 (fun _ => I.Bool_false) (fun _ => @Lean.eq_refl _ _) jR jL Hj)
      (sub_nat_rel_canonical O)).
  Qed.

  Definition src_workload_of_jobs_case_on_pred : Prop :=
    ltac:(body_of (fun s : S.statement_workload_of_jobs_case_on_pred => s Job costR)).
  Definition tgt_workload_of_jobs_case_on_pred : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_case_on_pred Job dJ costL)).
  Theorem workload_of_jobs_case_on_pred_correspondence :
    PropSPropRel src_workload_of_jobs_case_on_pred tgt_workload_of_jobs_case_on_pred.
  Proof.
    apply cover_list. intros jR jL Hj.
    apply cover_pred. intros PR PL HP.
    apply cover_pred. intros QR QL HQ.
    exact (sub_nat_eq_correspondence _ _ _ _ (WL PR PL HP jR jL Hj)
      (sub_add_correspondence _ _ _ _
        (WL _ _ (fun j => ar_bool_and_related _ _ _ _ (HP j) (HQ j)) jR jL Hj)
        (WL _ _ (fun j => ar_bool_and_related _ _ _ _ (HP j) (fwk_bool_not_related _ _ (HQ j))) jR jL Hj))).
  Qed.

  Definition src_workload_of_jobs_equiv_pred : Prop :=
    ltac:(body_of (fun s : S.statement_workload_of_jobs_equiv_pred => s Job costR)).
  Definition tgt_workload_of_jobs_equiv_pred : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_equiv_pred Job dJ costL)).
  Theorem workload_of_jobs_equiv_pred_correspondence :
    PropSPropRel src_workload_of_jobs_equiv_pred tgt_workload_of_jobs_equiv_pred.
  Proof.
    apply cover_list. intros jR jL Hj.
    apply cover_pred. intros PR PL HP.
    apply cover_pred. intros QR QL HQ.
    apply ar_imp_correspondence.
    - unfold prop_in1, inPhantom, eqfun.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (fwk_mem_truth j _ _ Hj)|].
      exact (fwk_bool_eq_correspondence _ _ _ _ (HP j) (HQ j)).
    - exact (sub_nat_eq_correspondence _ _ _ _ (WL PR PL HP jR jL Hj) (WL QR QL HQ jR jL Hj)).
  Qed.

  Section Minus.
    Definition src_workload_minus_job_cost' : Prop :=
      ltac:(body_of (fun s : S.statement_workload_minus_job_cost' => s Job costR)).
    Definition tgt_workload_minus_job_cost' : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_minus_job_cost' Job dJ costL)).
    Theorem workload_minus_job_cost'_correspondence :
      PropSPropRel src_workload_minus_job_cost' tgt_workload_minus_job_cost'.
    Proof.
      apply ar_forall_identity_correspondence. intro j.
      apply cover_list. intros jR jL Hj.
      apply ar_imp_correspondence; [exact (ar_uniq_correspondence Job jR jL Hj)|].
      apply ar_imp_correspondence; [exact (fwk_mem_truth j _ _ Hj)|].
      apply cover_pred. intros PR PL HP.
      exact (sub_nat_eq_correspondence _ _ _ _
        (WL _ _ (fun x => ar_bool_and_related _ _ _ _ (HP x) (wl_ne_observation Job x j)) jR jL Hj)
        (ari_nat_sub_related _ _ _ _ (WL PR PL HP jR jL Hj) (fwk_cond_related _ _ _ _ (HP j) (Hcost j)))).
    Qed.

    Definition src_workload_minus_job_cost : Prop :=
      ltac:(body_of (fun s : S.statement_workload_minus_job_cost => s Job costR)).
    Definition tgt_workload_minus_job_cost : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_minus_job_cost Job dJ costL)).
    Theorem workload_minus_job_cost_correspondence :
      PropSPropRel src_workload_minus_job_cost tgt_workload_minus_job_cost.
    Proof.
      apply ar_forall_identity_correspondence. intro j.
      apply cover_list. intros jR jL Hj.
      apply ar_imp_correspondence; [exact (ar_uniq_correspondence Job jR jL Hj)|].
      apply ar_imp_correspondence; [exact (fwk_mem_truth j _ _ Hj)|].
      exact (sub_nat_eq_correspondence _ _ _ _
        (WL _ _ (fun x => wl_ne_observation Job x j) jR jL Hj)
        (ari_nat_sub_related _ _ _ _ (WL predT (fun _ => I.Bool_true) (fun _ => @Lean.eq_refl _ _) jR jL Hj)
          (Hcost j))).
    Qed.
  End Minus.

  Section Arrivals.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Let BETWEEN t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :=
      arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2.

    Definition src_workload_of_jobs_cat : Prop :=
      ltac:(body_of (fun s : S.statement_workload_of_jobs_cat => s Job costR arrR)).
    Definition tgt_workload_of_jobs_cat : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_cat Job dJ costL arrL)).
    Theorem workload_of_jobs_cat_correspondence :
      PropSPropRel src_workload_of_jobs_cat tgt_workload_of_jobs_cat.
    Proof.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
      apply cover_pred. intros PR PL HP.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
          (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_le_related _ _ _ _ Ht Ht2)))|].
      exact (sub_nat_eq_correspondence _ _ _ _ (WL PR PL HP _ _ (BETWEEN _ _ _ _ Ht1 Ht2))
        (sub_add_correspondence _ _ _ _ (WL PR PL HP _ _ (BETWEEN _ _ _ _ Ht1 Ht))
          (WL PR PL HP _ _ (BETWEEN _ _ _ _ Ht Ht2)))).
    Qed.

    Definition src_workload_of_jobs_reduce_range : Prop :=
      ltac:(body_of (fun s : S.statement_workload_of_jobs_reduce_range => s Job costR arrR)).
    Definition tgt_workload_of_jobs_reduce_range : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_reduce_range Job dJ costL arrL)).
    Theorem workload_of_jobs_reduce_range_correspondence :
      PropSPropRel src_workload_of_jobs_reduce_range tgt_workload_of_jobs_reduce_range.
    Proof.
      apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
      apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
      apply ar_forall_nat_correspondence. intros t3R t3L Ht3.
      apply cover_pred. intros PR PL HP.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht1 Ht2)|].
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht2 Ht3)|].
      exact (sub_nat_le_correspondence _ _ _ _ (WL PR PL HP _ _ (BETWEEN _ _ _ _ Ht1 Ht2))
        (WL PR PL HP _ _ (BETWEEN _ _ _ _ Ht1 Ht3))).
    Qed.

    Section Priority.
      Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
      Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
      Hypothesis Hp : forall x y : Job,
        ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
          (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

      Definition src_workload_job_and_ahep_eq_workload_hep : Prop :=
        ltac:(body_of (fun s : S.statement_workload_job_and_ahep_eq_workload_hep => s Job costR arrR pR)).
      Definition tgt_workload_job_and_ahep_eq_workload_hep : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_job_and_ahep_eq_workload_hep
          Job dJ costL arrL pL)).
      Theorem workload_job_and_ahep_eq_workload_hep_correspondence :
        PropSPropRel src_workload_job_and_ahep_eq_workload_hep tgt_workload_job_and_ahep_eq_workload_hep.
      Proof.
        apply ar_imp_correspondence.
        - unfold prosa.model.priority.definitions.reflexive_job_priorities, reflexive.
          cbn [I.Prosa_Model_Priority_Definitions_reflexive_job_priorities].
          apply ar_forall_identity_correspondence. intro j.
          exact (ar_bool_truth_correspondence _ _ (Hp j j)).
        - apply ar_forall_identity_correspondence. intro j.
          apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
          apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
          exact (sub_nat_eq_correspondence _ _ _ _
            (sub_add_correspondence _ _ _ _
              (workload_of_job_correspondence Job costR costL Hcost arrR arrL Harr j _ _ _ _ Ht1 Ht2)
              (workload_of_other_hep_jobs_correspondence Job costR costL Hcost arrR arrL Harr pR pL Hp j
                _ _ _ _ Ht1 Ht2))
            (workload_of_hep_jobs_correspondence Job costR costL Hcost arrR arrL Harr pR pL Hp j
              _ _ _ _ Ht1 Ht2)).
      Qed.
    End Priority.

    Section Arrival.
      Variable jaR : prosa.behavior.job.JobArrival Job.
      Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
      Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

      Let CONS := consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.

      Definition src_workload_of_job_eq_job_arrival : Prop :=
        ltac:(body_of (fun s : S.statement_workload_of_job_eq_job_arrival => s Job jaR costR arrR)).
      Definition tgt_workload_of_job_eq_job_arrival : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_of_job_eq_job_arrival
          Job dJ jaL costL arrL)).
      Theorem workload_of_job_eq_job_arrival_correspondence :
        PropSPropRel src_workload_of_job_eq_job_arrival tgt_workload_of_job_eq_job_arrival.
      Proof.
        apply ar_imp_correspondence; [exact CONS|].
        apply ar_imp_correspondence; [exact (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr)|].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
        apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
        apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
        exact (sub_nat_eq_correspondence _ _ _ _
          (workload_of_job_correspondence Job costR costL Hcost arrR arrL Harr j _ _ _ _ Ht1 Ht2)
          (fwk_cond_related _ _ _ _
            (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ht1 (Hja j))
              (ar_decide_lt_related _ _ _ _ (Hja j) Ht2))
            (Hcost j))).
      Qed.

      Definition src_workload_of_jobs_nil_tail : Prop :=
        ltac:(body_of (fun s : S.statement_workload_of_jobs_nil_tail => s Job jaR costR arrR)).
      Definition tgt_workload_of_jobs_nil_tail : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_nil_tail
          Job dJ jaL costL arrL)).
      Theorem workload_of_jobs_nil_tail_correspondence :
        PropSPropRel src_workload_of_jobs_nil_tail tgt_workload_of_jobs_nil_tail.
      Proof.
        apply ar_imp_correspondence; [exact CONS|].
        apply cover_pred. intros PR PL HP.
        apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
        apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Ht2)|].
        apply ar_imp_correspondence.
        - apply ar_forall_identity_correspondence. intro j.
          apply ar_imp_correspondence; [exact (fwk_mem_truth j _ _ (BETWEEN _ _ _ _ Ht1 Ht2))|].
          apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht (Hja j))|].
          exact (ar_bool_truth_correspondence _ _ (fwk_bool_not_related _ _ (HP j))).
        - exact (sub_nat_eq_correspondence _ _ _ _ (WL PR PL HP _ _ (BETWEEN _ _ _ _ Ht1 Ht2))
            (WL PR PL HP _ _ (BETWEEN _ _ _ _ Ht1 Ht))).
      Qed.

      Definition src_workload_equal_subset : Prop :=
        ltac:(body_of (fun s : S.statement_workload_equal_subset => s Job jaR costR arrR)).
      Definition tgt_workload_equal_subset : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_equal_subset
          Job dJ jaL costL arrL)).
      Theorem workload_equal_subset_correspondence :
        PropSPropRel src_workload_equal_subset tgt_workload_equal_subset.
      Proof.
        apply ar_imp_correspondence; [exact CONS|].
        apply ar_imp_correspondence;
          [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
        apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
        apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply cover_pred. intros PR PL HP.
        exact (sub_nat_le_correspondence _ _ _ _
          (WL _ _ (fun j => ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ (Hja j) Ht) (HP j))
            _ _ (BETWEEN _ _ _ _ Ht1 Ht2))
          (WL _ _ HP _ _ (BETWEEN _ _ _ _ Ht1 (sub_add_correspondence _ _ _ _ Ht (sub_nat_rel_canonical 1))))).
      Qed.
    End Arrival.
  End Arrivals.

  Section Tasks.
    Context (Task : eqType).
    Let dT := ar_decidable_eq Task.
    Variable jtR : prosa.model.task.concept.JobTask Job Task.
    Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
    Hypothesis Hjt : forall j : Job,
      Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).

    Let cover_tpred := fwk_cover_pred Task.
    Let cover_tlist := fwk_cover_list Task.

    Lemma fwk_part_pred_related PR PL (HP : ArPredRel PR PL) (tsk : Task) :
      ArPredRel (fun j => PR j && (@prosa.model.task.concept.job_task Job Task jtR j == tsk))
        (fun j => I.Bool_and (PL j)
          (I.Decidable_decide (Lean.eq (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j) tsk)
            (ar_decidable_eq Task (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j) tsk))).
    Proof.
      intro j. exact (ar_bool_and_related _ _ _ _ (HP j) (fwk_job_task_eq_related Task Job jtR jtL Hjt j tsk)).
    Qed.

    Lemma fwk_q_task_related QR QL (HQ : ArPredRel QR QL) (j : Job) :
      ArBoolRel (QR (@prosa.model.task.concept.job_task Job Task jtR j))
        (QL (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
    Proof.
      exact (fwk_lean_transport (fun x => ArBoolRel (QR (@prosa.model.task.concept.job_task Job Task jtR j)) (QL x))
        _ _ (Hjt j) (HQ _)).
    Qed.

    Definition src_workload_of_jobs_le_sum_over_partitions : Prop :=
      ltac:(body_of (fun s : S.statement_workload_of_jobs_le_sum_over_partitions => s Task Job jtR costR)).
    Definition tgt_workload_of_jobs_le_sum_over_partitions : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_le_sum_over_partitions
        Task dT Job dJ jtL costL)).
    Theorem workload_of_jobs_le_sum_over_partitions_correspondence :
      PropSPropRel src_workload_of_jobs_le_sum_over_partitions tgt_workload_of_jobs_le_sum_over_partitions.
    Proof.
      apply cover_pred. intros PR PL HP.
      apply cover_tpred. intros QR QL HQ.
      apply cover_list. intros jR jL Hj.
      apply cover_tlist. intros tR tL Ht.
      apply ar_imp_correspondence.
      { unfold prop_in1, inPhantom. apply ar_forall_identity_correspondence. intro j.
        apply ar_imp_correspondence; [exact (fwk_mem_truth j _ _ Hj)|].
        exact (ar_bool_truth_correspondence _ _ (fwk_job_task_mem_related Task Job jtR jtL Hjt j tR tL Ht)). }
      apply ar_imp_correspondence.
      { unfold prop_in1, inPhantom. apply ar_forall_identity_correspondence. intro j.
        apply ar_imp_correspondence; [exact (fwk_mem_truth j _ _ Hj)|].
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (HP j))|].
        exact (ar_bool_truth_correspondence _ _ (fwk_q_task_related QR QL HQ j)). }
      cbv zeta.
      exact (sub_nat_le_correspondence _ _ _ _ (WL PR PL HP jR jL Hj)
        (wl_sum_filter_related Task QR QL _ _ tR tL HQ
          (fun tsk => WL _ _ (fwk_part_pred_related PR PL HP tsk) jR jL Hj) Ht)).
    Qed.

    Definition src_workload_of_jobs_partitioned_by_tasks : Prop :=
      ltac:(body_of (fun s : S.statement_workload_of_jobs_partitioned_by_tasks => s Task Job jtR costR)).
    Definition tgt_workload_of_jobs_partitioned_by_tasks : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_of_jobs_partitioned_by_tasks
        Task dT Job dJ jtL costL)).
    Theorem workload_of_jobs_partitioned_by_tasks_correspondence :
      PropSPropRel src_workload_of_jobs_partitioned_by_tasks tgt_workload_of_jobs_partitioned_by_tasks.
    Proof.
      apply cover_pred. intros PR PL HP.
      apply cover_tpred. intros QR QL HQ.
      apply cover_list. intros jR jL Hj.
      apply cover_tlist. intros tR tL Ht.
      apply ar_imp_correspondence.
      { unfold prop_in1, inPhantom. apply ar_forall_identity_correspondence. intro j.
        apply ar_imp_correspondence; [exact (fwk_mem_truth j _ _ Hj)|].
        exact (ar_bool_truth_correspondence _ _ (fwk_job_task_mem_related Task Job jtR jtL Hjt j tR tL Ht)). }
      apply ar_imp_correspondence.
      { unfold prop_in1, inPhantom. apply ar_forall_identity_correspondence. intro j.
        apply ar_imp_correspondence; [exact (fwk_mem_truth j _ _ Hj)|].
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (HP j))|].
        exact (ar_bool_truth_correspondence _ _ (fwk_q_task_related QR QL HQ j)). }
      apply ar_imp_correspondence; [exact (ar_uniq_correspondence Job jR jL Hj)|].
      apply ar_imp_correspondence; [exact (ar_uniq_correspondence Task tR tL Ht)|].
      cbv zeta.
      exact (sub_nat_eq_correspondence _ _ _ _ (WL PR PL HP jR jL Hj)
        (wl_sum_filter_related Task QR QL _ _ tR tL HQ
          (fun tsk => WL _ _ (fwk_part_pred_related PR PL HP tsk) jR jL Hj) Ht)).
    Qed.

    Section Priority.
      Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
      Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
      Hypothesis Hp : forall x y : Job,
        ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
          (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

      Definition src_workload_of_other_jobs_split : Prop :=
        ltac:(body_of (fun s : S.statement_workload_of_other_jobs_split => s Task Job jtR costR pR)).
      Definition tgt_workload_of_other_jobs_split : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Workload_workload_of_other_jobs_split
          Task dT Job dJ jtL costL pL)).
      Theorem workload_of_other_jobs_split_correspondence :
        PropSPropRel src_workload_of_other_jobs_split tgt_workload_of_other_jobs_split.
      Proof.
        apply cover_list. intros jR jL Hj.
        apply ar_forall_identity_correspondence. intro j.
        exact (sub_nat_eq_correspondence _ _ _ _
          (WL _ _ (fun x => fwk_another_hep_job_related Job pR pL Hp x j) jR jL Hj)
          (sub_add_correspondence _ _ _ _
            (WL _ _ (fun x => fwk_another_task_hep_job_related Task Job jtR jtL Hjt pR pL Hp x j) jR jL Hj)
            (WL _ _ (fun x => fwk_another_hep_job_of_same_task_related Task Job jtR jtL Hjt pR pL Hp x j) jR jL Hj))).
      Qed.
    End Priority.
  End Tasks.
End Statements.
