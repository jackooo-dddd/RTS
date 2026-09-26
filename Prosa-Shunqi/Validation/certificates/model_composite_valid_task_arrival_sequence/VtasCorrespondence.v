From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.composite.valid_task_arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedVtas ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence CurvesCorrespondence.

Module I := ImportedVtas.

(** Certificates for [model/composite/valid_task_arrival_sequence.v]: the
    definition (related inputs give related propositions) and the five
    projection lemmas (source: exact elaborated type of the pinned lemma via
    [type of]; target: type of the imported theorem; task set and arrival
    sequence covered in both directions). *)

Ltac type_of_term t := let T := type of t in exact T.

Lemma vt_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xR xL, ArListRel xR xL -> PropSPropRel (PR xR) (PL xL)) ->
  PropSPropRel (forall xR, PR xR) (forall xL, PL xL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR xL. exact (prop_to_sprop _ _ (H _ _ (ar_list_target_roundtrip xL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro xR.
    exact (sprop_to_prop _ _ (H xR (ar_list_to_imported xR) (@Lean.eq_refl _ _)) (HL _)).
Qed.

Definition vt_arrival_sequence_to_source (Job : eqType)
    (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job)) :
    prosa.behavior.arrival_sequence.arrival_sequence Job :=
  fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

Lemma vt_arrival_sequence_to_source_rel (Job : eqType) arrL :
  ArArrivalSequenceRel Job (vt_arrival_sequence_to_source Job arrL) arrL.
Proof.
  intros tR tL Ht. unfold ArListRel, vt_arrival_sequence_to_source.
  refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
  exact (sub_imported_eq_congr arrL _ _ Ht).
Qed.

Lemma vt_forall_arrival_sequence (Job : eqType)
    (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
    (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job) -> SProp) :
  (forall arrR arrL, ArArrivalSequenceRel Job arrR arrL -> PropSPropRel (PR arrR) (PL arrL)) ->
  PropSPropRel (forall arrR, PR arrR) (forall arrL, PL arrL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR arrL. exact (prop_to_sprop _ _ (H _ _ (vt_arrival_sequence_to_source_rel Job arrL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro arrR.
    exact (sprop_to_prop _ _ (H _ _ (ar_arrival_sequence_canonical Job arrR)) (HL _)).
Qed.

Section Vtas.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.

  Definition VtTaskCostRel (tcR : prosa.model.task.concept.TaskCost Task)
      (tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT) : SProp :=
    forall tsk, SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Lemma TaskCost_source_total tcR : VtTaskCostRel tcR
    (I.Prosa_Model_Task_Concept_TaskCost_mk Task dT (fun tsk => sub_nat_to_imported (tcR tsk))).
  Proof. intro tsk. exact (sub_nat_rel_canonical _). Qed.
  Lemma TaskCost_target_total tcL : VtTaskCostRel
    (fun tsk => sub_nat_to_rocq (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk)) tcL.
  Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : VtTaskCostRel tcR tcL.
  Variable maxR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maxL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hmax : CvMaxArrivalsRel Task maxR maxL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j) (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

  Lemma vt_valid_job_cost_related (j : Job) :
    ArBoolRel (@prosa.model.task.concept.valid_job_cost Task tcR Job jtR costR j)
      (I.Prosa_Model_Task_Concept_valid_job_cost Task dT tcL Job dJ jtL costL j).
  Proof.
    unfold prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_valid_job_cost].
    apply ar_decide_le_related; [exact (Hcost j)|].
    exact (ari_lean_transport (fun v => SubNatRel _ (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v))
      _ _ (Hjt j) (Htc _)).
  Qed.

  Lemma vt_arrivals_have_valid_job_costs_related arrR arrL :
    ArArrivalSequenceRel Job arrR arrL ->
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
  Proof.
    intro Harr.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (ar_bool_truth_correspondence _ _ (vt_valid_job_cost_related j)).
  Qed.

  Lemma vt_all_jobs_from_taskset_related arrR arrL tsR tsL :
    ArArrivalSequenceRel Job arrR arrL -> ArListRel tsR tsL ->
    PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
      (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
  Proof.
    intros Harr Hts.
    unfold prosa.model.task.concept.all_jobs_from_taskset.
    cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    have E := imported_eq_to_coq_eq _ _ (Hjt j).
    rewrite -E.
    exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task _ _ _ Hts)).
  Qed.

  Theorem valid_task_arrival_sequence_correspondence tsR tsL arrR arrL :
    ArListRel tsR tsL -> ArArrivalSequenceRel Job arrR arrL ->
    PropSPropRel
      (@prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence
        Task tcR maxR Job jtR costR jaR tsR arrR)
      (I.Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence
        Task dT tcL maxL Job dJ jtL costL jaL tsL arrL).
  Proof.
    intros Hts Harr.
    unfold prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence.
    cbn [I.Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence].
    apply ar_and_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ar_and_correspondence; [exact (vt_arrivals_have_valid_job_costs_related arrR arrL Harr)|].
    apply ar_and_correspondence; [exact (vt_all_jobs_from_taskset_related arrR arrL tsR tsL Harr Hts)|].
    apply ar_and_correspondence;
      [exact (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maxR maxL Hmax)|].
    exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hmax).
  Qed.

  Let VTAS := valid_task_arrival_sequence_correspondence.

  Definition src_valid_arrivals : Prop := ltac:(type_of_term
    (@prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_valid_arrivals
      Task tcR maxR Job jtR costR jaR)).
  Definition tgt_valid_arrivals : SProp := ltac:(type_of_term
    (@I.Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence_valid_arrivals
      Task dT tcL maxL Job dJ jtL costL jaL)).
  Theorem valid_task_arrival_sequence_valid_arrivals_correspondence :
    PropSPropRel src_valid_arrivals tgt_valid_arrivals.
  Proof.
    apply vt_forall_list => tsR tsL Hts.
    apply (vt_forall_arrival_sequence Job) => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (VTAS tsR tsL arrR arrL Hts Harr)|].
    exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
  Qed.

  Definition src_valid_costs : Prop := ltac:(type_of_term
    (@prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_valid_costs
      Task tcR maxR Job jtR costR jaR)).
  Definition tgt_valid_costs : SProp := ltac:(type_of_term
    (@I.Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence_valid_costs
      Task dT tcL maxL Job dJ jtL costL jaL)).
  Theorem valid_task_arrival_sequence_valid_costs_correspondence :
    PropSPropRel src_valid_costs tgt_valid_costs.
  Proof.
    apply vt_forall_list => tsR tsL Hts.
    apply (vt_forall_arrival_sequence Job) => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (VTAS tsR tsL arrR arrL Hts Harr)|].
    exact (vt_arrivals_have_valid_job_costs_related arrR arrL Harr).
  Qed.

  Definition src_from_taskset : Prop := ltac:(type_of_term
    (@prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_from_taskset
      Task tcR maxR Job jtR costR jaR)).
  Definition tgt_from_taskset : SProp := ltac:(type_of_term
    (@I.Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence_from_taskset
      Task dT tcL maxL Job dJ jtL costL jaL)).
  Theorem valid_task_arrival_sequence_from_taskset_correspondence :
    PropSPropRel src_from_taskset tgt_from_taskset.
  Proof.
    apply vt_forall_list => tsR tsL Hts.
    apply (vt_forall_arrival_sequence Job) => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (VTAS tsR tsL arrR arrL Hts Harr)|].
    exact (vt_all_jobs_from_taskset_related arrR arrL tsR tsL Harr Hts).
  Qed.

  Definition src_respects_max : Prop := ltac:(type_of_term
    (@prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_respects_max
      Task tcR maxR Job jtR costR jaR)).
  Definition tgt_respects_max : SProp := ltac:(type_of_term
    (@I.Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence_respects_max
      Task dT tcL maxL Job dJ jtL costL jaL)).
  Theorem valid_task_arrival_sequence_respects_max_correspondence :
    PropSPropRel src_respects_max tgt_respects_max.
  Proof.
    apply vt_forall_list => tsR tsL Hts.
    apply (vt_forall_arrival_sequence Job) => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (VTAS tsR tsL arrR arrL Hts Harr)|].
    exact (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maxR maxL Hmax).
  Qed.

  Definition src_valid_curve : Prop := ltac:(type_of_term
    (@prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_valid_curve
      Task tcR maxR Job jtR costR jaR)).
  Definition tgt_valid_curve : SProp := ltac:(type_of_term
    (@I.Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence_valid_curve
      Task dT tcL maxL Job dJ jtL costL jaL)).
  Theorem valid_task_arrival_sequence_valid_curve_correspondence :
    PropSPropRel src_valid_curve tgt_valid_curve.
  Proof.
    apply vt_forall_list => tsR tsL Hts.
    apply (vt_forall_arrival_sequence Job) => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (VTAS tsR tsL arrR arrL Hts Harr)|].
    exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hmax).
  Qed.
End Vtas.
