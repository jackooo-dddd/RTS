From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import JlfpWithFpSemanticSource.
From prosa Require Import analysis.definitions.priority.classes.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJlfpWithFp ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  WorkloadCorrespondence.

Module I := ImportedJlfpWithFp.
Module S := JlfpWithFpSemanticSource.JlfpWithFpSemanticSource.

(** Certificates for [analysis/facts/priority/jlfp_with_fp.v].

    Source side: the extracted byte-identical definition blocks and the three
    extracted lemma statements, specialised at their leading inputs; target
    side: the compiled Lean declarations.  Inputs: the FP and JLFP policies
    pointwise on Booleans, [job_task] by [Lean.eq], [job_cost] pointwise by
    [SubNatRel], [job_arrival] by [ArJobArrivalRel]; arrival sequences and
    task sets are covered in both directions where they are quantified
    inside a statement.  Workloads are closed by the accepted
    [WorkloadCorrespondence], task membership and arrivals by the accepted
    arrival-sequence certificates.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma jwf_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xR xL, ArListRel xR xL -> PropSPropRel (PR xR) (PL xL)) ->
  PropSPropRel (forall xR, PR xR) (forall xL, PL xL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR xL. exact (prop_to_sprop _ _ (H _ _ (ar_list_target_roundtrip xL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro xR.
    exact (sprop_to_prop _ _ (H xR (ar_list_to_imported xR) (@Lean.eq_refl _ _)) (HL _)).
Qed.

Definition jwf_arrival_sequence_to_source (Job : eqType)
    (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job)) :
    prosa.behavior.arrival_sequence.arrival_sequence Job :=
  fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

Lemma jwf_arrival_sequence_to_source_rel (Job : eqType) arrL :
  ArArrivalSequenceRel Job (jwf_arrival_sequence_to_source Job arrL) arrL.
Proof.
  intros tR tL Ht. unfold ArListRel, jwf_arrival_sequence_to_source.
  refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
  exact (sub_imported_eq_congr arrL _ _ Ht).
Qed.

Lemma jwf_forall_arrival_sequence (Job : eqType)
    (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
    (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job) -> SProp) :
  (forall arrR arrL, ArArrivalSequenceRel Job arrR arrL -> PropSPropRel (PR arrR) (PL arrL)) ->
  PropSPropRel (forall arrR, PR arrR) (forall arrL, PL arrL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR arrL.
    exact (prop_to_sprop _ _ (H _ _ (jwf_arrival_sequence_to_source_rel Job arrL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro arrR.
    exact (sprop_to_prop _ _ (H _ _ (ar_arrival_sequence_canonical Job arrR)) (HL _)).
Qed.

Lemma jwf_ne_transport (T : eqType) (xR yR xL yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL ->
  ArBoolRel (xR != yR)
    (I.Decidable_decide (I.Ne T xL yL) (I.instDecidableNot (Lean.eq xL yL) (ar_decidable_eq T xL yL))).
Proof.
  intros Hx Hy.
  refine (ari_lean_transport
    (fun v => ArBoolRel (xR != yR)
      (I.Decidable_decide (I.Ne T v yL) (I.instDecidableNot (Lean.eq v yL) (ar_decidable_eq T v yL))))
    _ _ Hx _).
  refine (ari_lean_transport
    (fun w => ArBoolRel (xR != yR)
      (I.Decidable_decide (I.Ne T xR w) (I.instDecidableNot (Lean.eq xR w) (ar_decidable_eq T xR w))))
    _ _ Hy _).
  exact (wl_ne_observation T xR yR).
Qed.

Lemma jwf_eq_transport (T : eqType) (xR yR xL yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL ->
  ArBoolRel (xR == yR) (I.Decidable_decide (Lean.eq xL yL) (ar_decidable_eq T xL yL)).
Proof.
  intros Hx Hy.
  refine (ari_lean_transport
    (fun v => ArBoolRel (xR == yR) (I.Decidable_decide (Lean.eq v yL) (ar_decidable_eq T v yL)))
    _ _ Hx _).
  refine (ari_lean_transport
    (fun w => ArBoolRel (xR == yR) (I.Decidable_decide (Lean.eq xR w) (ar_decidable_eq T xR w)))
    _ _ Hy _).
  exact (ari_decide_eq_related T xR yR).
Qed.

Lemma jwf_bool_not_related bR bL :
  ArBoolRel bR bL -> ArBoolRel (~~ bR) (I.Bool_not bL).
Proof.
  intro Hb. unfold ArBoolRel in *.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_congr I.Bool_not _ _ Hb)).
  destruct bR; exact (@Lean.eq_refl _ _).
Qed.

(** ** Task-level priority observations *)

Section Fp.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable fpR : prosa.model.priority.definitions.FP_policy Task.
  Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hfp : forall x y : Task,
    ArBoolRel (@prosa.model.priority.definitions.hep_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL x y).

  Lemma jwf_ep_task_related (xR yR xL yL : Task) :
    Lean.eq xR xL -> Lean.eq yR yL ->
    ArBoolRel (@prosa.model.priority.definitions.ep_task Task fpR xR yR)
      (I.Prosa_Model_Priority_Definitions_ep_task Task dT fpL xL yL).
  Proof.
    intros Hx Hy. unfold prosa.model.priority.definitions.ep_task.
    cbn [I.Prosa_Model_Priority_Definitions_ep_task].
    apply ar_bool_and_related.
    - exact (sub_imported_eq_trans _ _ _ (Hfp xR yR)
        (sub_imported_eq_congr2 (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL)
          _ _ _ _ Hx Hy)).
    - exact (sub_imported_eq_trans _ _ _ (Hfp yR xR)
        (sub_imported_eq_congr2 (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL)
          _ _ _ _ Hy Hx)).
  Qed.

  Lemma jwf_hp_task_related (xR yR xL yL : Task) :
    Lean.eq xR xL -> Lean.eq yR yL ->
    ArBoolRel (@prosa.model.priority.definitions.hp_task Task fpR xR yR)
      (I.Prosa_Model_Priority_Definitions_hp_task Task dT fpL xL yL).
  Proof.
    intros Hx Hy. unfold prosa.model.priority.definitions.hp_task.
    cbn [I.Prosa_Model_Priority_Definitions_hp_task].
    apply ar_bool_and_related.
    - exact (sub_imported_eq_trans _ _ _ (Hfp xR yR)
        (sub_imported_eq_congr2 (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL)
          _ _ _ _ Hx Hy)).
    - apply jwf_bool_not_related.
      exact (sub_imported_eq_trans _ _ _ (Hfp yR xR)
        (sub_imported_eq_congr2 (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL)
          _ _ _ _ Hy Hx)).
  Qed.

  Theorem other_ep_task_correspondence (tsk tsk_o : Task) :
    ArBoolRel (@S.other_ep_task Task fpR tsk tsk_o)
      (I.Prosa_Analysis_Facts_Priority_JlfpWithFp_other_ep_task Task dT fpL tsk tsk_o).
  Proof.
    unfold S.other_ep_task.
    cbn [I.Prosa_Analysis_Facts_Priority_JlfpWithFp_other_ep_task].
    apply ar_bool_and_related.
    - exact (jwf_ep_task_related _ _ _ _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _)).
    - exact (wl_ne_observation Task tsk_o tsk).
  Qed.
End Fp.

(** ** Job-level predicates *)

Section Jobs.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable fpR : prosa.model.priority.definitions.FP_policy Task.
  Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hfp : forall x y : Task,
    ArBoolRel (@prosa.model.priority.definitions.hep_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL x y).
  Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hp : forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Let EP (j j' : Job) := jwf_ep_task_related Task fpR fpL Hfp _ _ _ _ (Hjt j') (Hjt j).
  Let HP (j j' : Job) := jwf_hp_task_related Task fpR fpL Hfp _ _ _ _ (Hjt j') (Hjt j).

  Theorem hep_job_of_ep_other_task_correspondence (j j' : Job) :
    ArBoolRel (@S.hep_job_of_ep_other_task Task Job jtR fpR pR j j')
      (I.Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_job_of_ep_other_task Task dT Job dJ jtL fpL pL j j').
  Proof.
    unfold S.hep_job_of_ep_other_task.
    cbn [I.Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_job_of_ep_other_task].
    apply ar_bool_and_related; [apply ar_bool_and_related|].
    - exact (Hp j' j).
    - exact (EP j j').
    - exact (jwf_ne_transport Task _ _ _ _ (Hjt j') (Hjt j)).
  Qed.

  Theorem from_hp_task_correspondence (j j' : Job) :
    ArBoolRel (@S.from_hp_task Task Job jtR fpR j j')
      (I.Prosa_Analysis_Facts_Priority_JlfpWithFp_from_hp_task Task dT Job dJ jtL fpL j j').
  Proof.
    unfold S.from_hp_task.
    cbn [I.Prosa_Analysis_Facts_Priority_JlfpWithFp_from_hp_task].
    exact (HP j j').
  Qed.

  Theorem hep_from_hp_task_correspondence (j j' : Job) :
    ArBoolRel (@S.hep_from_hp_task Task Job jtR fpR pR j j')
      (I.Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_from_hp_task Task dT Job dJ jtL fpL pL j j').
  Proof.
    unfold S.hep_from_hp_task.
    cbn [I.Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_from_hp_task].
    exact (ar_bool_and_related _ _ _ _ (Hp j' j) (HP j j')).
  Qed.

  Theorem hep_from_ep_task_correspondence (j j' : Job) :
    ArBoolRel (@S.hep_from_ep_task Task Job jtR fpR pR j j')
      (I.Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_from_ep_task Task dT Job dJ jtL fpL pL j j').
  Proof.
    unfold S.hep_from_ep_task.
    cbn [I.Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_from_ep_task].
    exact (ar_bool_and_related _ _ _ _ (Hp j' j) (EP j j')).
  Qed.

  Lemma jwf_compatible_related :
    PropSPropRel (@prosa.analysis.definitions.priority.classes.JLFP_FP_compatible Task Job jtR pR fpR)
      (I.Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible Task dT Job dJ jtL pL fpL).
  Proof.
    unfold prosa.analysis.definitions.priority.classes.JLFP_FP_compatible.
    cbn [I.Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible].
    apply ar_and_correspondence.
    - apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp j1 j2))|].
      apply ar_bool_truth_correspondence.
      exact (sub_imported_eq_trans _ _ _ (Hfp _ _)
        (sub_imported_eq_congr2 (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL)
          _ _ _ _ (Hjt j1) (Hjt j2))).
    - apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (HP j2 j1))|].
      exact (ar_bool_truth_correspondence _ _ (Hp j1 j2)).
  Qed.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).

  Let WL := workload_of_jobs_correspondence Job costR costL Hcost.

  Definition src_hep_hp_workload_hp : Prop :=
    ltac:(body_of (fun s : S.statement_hep_hp_workload_hp => s Task Job jtR costR fpR pR)).
  Definition tgt_hep_hp_workload_hp : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_hp_workload_hp
      Task dT Job dJ jtL costL fpL pL)).

  Theorem hep_hp_workload_hp_correspondence :
    PropSPropRel src_hep_hp_workload_hp tgt_hep_hp_workload_hp.
  Proof.
    apply ar_imp_correspondence; [exact jwf_compatible_related|].
    apply jwf_forall_arrival_sequence. intros arrR arrL Harr.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    have Hjobs := arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2.
    apply sub_nat_eq_correspondence.
    - exact (WL _ _ (hep_from_hp_task_correspondence j) _ _ Hjobs).
    - exact (WL _ _ (from_hp_task_correspondence j) _ _ Hjobs).
  Qed.

  Definition src_hep_workload_partitioning_taskwise : Prop :=
    ltac:(body_of (fun s : S.statement_hep_workload_partitioning_taskwise => s Task Job jtR costR fpR pR)).
  Definition tgt_hep_workload_partitioning_taskwise : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_workload_partitioning_taskwise
      Task dT Job dJ jtL costL fpL pL)).

  Theorem hep_workload_partitioning_taskwise_correspondence :
    PropSPropRel src_hep_workload_partitioning_taskwise tgt_hep_workload_partitioning_taskwise.
  Proof.
    apply ar_imp_correspondence; [exact jwf_compatible_related|].
    apply jwf_forall_arrival_sequence. intros arrR arrL Harr.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    have Hjobs := arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2.
    apply sub_nat_eq_correspondence.
    - exact (workload_of_hep_jobs_correspondence Job costR costL Hcost arrR arrL Harr pR pL Hp j _ _ _ _ H1 H2).
    - exact (sub_add_correspondence _ _ _ _
        (WL _ _ (hep_from_hp_task_correspondence j) _ _ Hjobs)
        (WL _ _ (hep_from_ep_task_correspondence j) _ _ Hjobs)).
  Qed.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma jwf_all_jobs_from_taskset_related tsR tsL :
    ArListRel tsR tsL ->
    PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
      (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
  Proof.
    intro Hts. unfold prosa.model.task.concept.all_jobs_from_taskset.
    cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_bool_truth_correspondence.
    refine (ari_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j \in tsR)
        (ar_target_decide_mem Task v tsL)) _ _ (Hjt j) _).
    exact (ar_decide_mem_related Task _ _ _ Hts).
  Qed.

  Definition src_hep_workload_from_other_ep_partitioned_by_tasks : Prop :=
    ltac:(body_of (fun s : S.statement_hep_workload_from_other_ep_partitioned_by_tasks =>
      s Task Job jaR jtR costR fpR pR arrR)).
  Definition tgt_hep_workload_from_other_ep_partitioned_by_tasks : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_workload_from_other_ep_partitioned_by_tasks
      Task dT Job dJ jaL jtL costL fpL pL arrL)).

  Theorem hep_workload_from_other_ep_partitioned_by_tasks_correspondence :
    PropSPropRel src_hep_workload_from_other_ep_partitioned_by_tasks
      tgt_hep_workload_from_other_ep_partitioned_by_tasks.
  Proof.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply jwf_forall_list. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (ar_uniq_correspondence Task _ _ Hts)|].
    apply ar_imp_correspondence; [exact (jwf_all_jobs_from_taskset_related _ _ Hts)|].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _
        (job_of_task_related Job Task jtR jtL Hjt tsk tsk (@Lean.eq_refl _ _) j))|].
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    have Hjobs := arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2.
    apply sub_nat_eq_correspondence.
    - exact (WL _ _ (hep_job_of_ep_other_task_correspondence j) _ _ Hjobs).
    - apply wl_sum_filter_related; [| |exact Hts].
      + intro tsk_o. exact (other_ep_task_correspondence Task fpR fpL Hfp tsk tsk_o).
      + intro tsk_o.
        refine (WL _ _ _ _ _ Hjobs).
        intro j0.
        exact (ar_bool_and_related _ _ _ _ (hep_job_of_ep_other_task_correspondence j j0)
          (jwf_eq_transport Task _ _ _ _ (Hjt j0) (@Lean.eq_refl _ tsk_o))).
  Qed.
End Jobs.
