From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import CurveAsRbfSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedCurveAsRbf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence CurvesCorrespondence RbfCorrespondence.

Module I := ImportedCurveAsRbf.
Module S := CurveAsRbfSemanticSource.CurveAsRbfSemanticSource.

(** Certificates for [model/task/arrival/curve_as_rbf.v].

    Definitions/instances: related inputs (task cost / min-cost classes and
    arrival-curve families, each with two-way coverage) give related outputs.
    Theorems: source side is the extracted statement [S.statement_X]
    specialised at the leading input binders; target side is the type of the
    imported Lean theorem.  Inner binders (tasks, curve families, task sets,
    arrival sequences) are covered in both directions. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Coverage for inner binders *)

Lemma cr_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xR xL, ArListRel xR xL -> PropSPropRel (PR xR) (PL xL)) ->
  PropSPropRel (forall xR, PR xR) (forall xL, PL xL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR xL. exact (prop_to_sprop _ _ (H _ _ (ar_list_target_roundtrip xL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro xR.
    exact (sprop_to_prop _ _ (H xR (ar_list_to_imported xR) (@Lean.eq_refl _ _)) (HL _)).
Qed.

Definition cr_arrival_sequence_to_source (Job : eqType)
    (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job)) :
    prosa.behavior.arrival_sequence.arrival_sequence Job :=
  fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

Lemma cr_arrival_sequence_to_source_rel (Job : eqType) arrL :
  ArArrivalSequenceRel Job (cr_arrival_sequence_to_source Job arrL) arrL.
Proof.
  intros tR tL Ht. unfold ArListRel, cr_arrival_sequence_to_source.
  refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
  exact (sub_imported_eq_congr arrL _ _ Ht).
Qed.

Lemma cr_forall_arrival_sequence (Job : eqType)
    (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
    (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job) -> SProp) :
  (forall arrR arrL, ArArrivalSequenceRel Job arrR arrL -> PropSPropRel (PR arrR) (PL arrL)) ->
  PropSPropRel (forall arrR, PR arrR) (forall arrL, PL arrL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR arrL. exact (prop_to_sprop _ _ (H _ _ (cr_arrival_sequence_to_source_rel Job arrL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro arrR.
    exact (sprop_to_prop _ _ (H _ _ (ar_arrival_sequence_canonical Job arrR)) (HL _)).
Qed.

Lemma cr_forall_family (Task : eqType)
    (PR : (Task -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall aR aL, CvCurveFamilyRel Task aR aL -> PropSPropRel (PR aR) (PL aL)) ->
  PropSPropRel (forall aR, PR aR) (forall aL, PL aL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR aL. exact (prop_to_sprop _ _ (H _ _ (cv_family_export Task aL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro aR.
    exact (sprop_to_prop _ _ (H _ _ (cv_family_import Task aR)) (HL _)).
Qed.

Section CurveAsRbf.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.

  (** Task cost / min-cost classes: input relations with two-way coverage. *)
  Definition CrTaskCostRel (tcR : prosa.model.task.concept.TaskCost Task)
      (tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT) : SProp :=
    forall tsk, SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Lemma TaskCost_source_total tcR : CrTaskCostRel tcR
    (I.Prosa_Model_Task_Concept_TaskCost_mk Task dT (fun tsk => sub_nat_to_imported (tcR tsk))).
  Proof. intro tsk. exact (sub_nat_rel_canonical _). Qed.
  Lemma TaskCost_target_total tcL : CrTaskCostRel
    (fun tsk => sub_nat_to_rocq (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk)) tcL.
  Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

  Definition CrTaskMinCostRel (tmR : prosa.model.task.concept.TaskMinCost Task)
      (tmL : I.Prosa_Model_Task_Concept_TaskMinCost Task dT) : SProp :=
    forall tsk, SubNatRel (@prosa.model.task.concept.task_min_cost Task tmR tsk)
      (I.Prosa_Model_Task_Concept_TaskMinCost_task_min_cost Task dT tmL tsk).
  Lemma TaskMinCost_source_total tmR : CrTaskMinCostRel tmR
    (I.Prosa_Model_Task_Concept_TaskMinCost_mk Task dT (fun tsk => sub_nat_to_imported (tmR tsk))).
  Proof. intro tsk. exact (sub_nat_rel_canonical _). Qed.
  Lemma TaskMinCost_target_total tmL : CrTaskMinCostRel
    (fun tsk => sub_nat_to_rocq (I.Prosa_Model_Task_Concept_TaskMinCost_task_min_cost Task dT tmL tsk)) tmL.
  Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : CrTaskCostRel tcR tcL.
  Variable tmR : prosa.model.task.concept.TaskMinCost Task.
  Variable tmL : I.Prosa_Model_Task_Concept_TaskMinCost Task dT.
  Hypothesis Htm : CrTaskMinCostRel tmR tmL.

  (** ** Definitions and instances *)

  Theorem task_max_rbf_correspondence aR aL :
    CvCurveFamilyRel Task aR aL ->
    CvCurveFamilyRel Task (@S.task_max_rbf Task tcR aR)
      (I.Prosa_Model_Task_Arrival_CurveAsRbf_task_max_rbf Task dT tcL aL).
  Proof.
    intros Ha tsk nR nL Hn.
    exact (sub_mul_correspondence _ _ _ _ (Htc tsk) (Ha tsk nR nL Hn)).
  Qed.

  Theorem task_min_rbf_correspondence aR aL :
    CvCurveFamilyRel Task aR aL ->
    CvCurveFamilyRel Task (@S.task_min_rbf Task tmR aR)
      (I.Prosa_Model_Task_Arrival_CurveAsRbf_task_min_rbf Task dT tmL aL).
  Proof.
    intros Ha tsk nR nL Hn.
    exact (sub_mul_correspondence _ _ _ _ (Htm tsk) (Ha tsk nR nL Hn)).
  Qed.

  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : CvMaxArrivalsRel Task maR maL.
  Variable miR : prosa.model.task.arrival.curves.MinArrivals Task.
  Variable miL : I.Prosa_Model_Task_Arrival_Curves_MinArrivals Task dT.
  Hypothesis Hmi : CvMinArrivalsRel Task miR miL.

  Theorem MaxArrivalsRBF_correspondence :
    RbMaxRel Task (@S.MaxArrivalsRBF Task tcR maR)
      (I.Prosa_Model_Task_Arrival_CurveAsRbf_MaxArrivalsRBF Task dT tcL maL).
  Proof. exact (task_max_rbf_correspondence _ _ Hma). Qed.

  Theorem MinArrivalsRBF_correspondence :
    RbMinRel Task (@S.MinArrivalsRBF Task tmR miR)
      (I.Prosa_Model_Task_Arrival_CurveAsRbf_MinArrivalsRBF Task dT tmL miL).
  Proof. exact (task_min_rbf_correspondence _ _ Hmi). Qed.

  (** ** Task-level theorems (no job context) *)

  Definition src_valid_arrival_curve_to_max_rbf : Prop :=
    ltac:(body_of (fun s : S.statement_valid_arrival_curve_to_max_rbf => s Task tcR)).
  Definition tgt_valid_arrival_curve_to_max_rbf : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_CurveAsRbf_valid_arrival_curve_to_max_rbf Task dT tcL)).
  Theorem valid_arrival_curve_to_max_rbf_correspondence :
    PropSPropRel src_valid_arrival_curve_to_max_rbf tgt_valid_arrival_curve_to_max_rbf.
  Proof.
    apply ar_forall_identity_correspondence => tsk.
    apply cr_forall_family => aR aL Ha.
    apply ar_imp_correspondence; [exact (valid_arrival_curve_correspondence _ _ (Ha tsk))|].
    exact (valid_request_bound_function_correspondence _ _ (task_max_rbf_correspondence _ _ Ha tsk)).
  Qed.

  Definition src_valid_arrival_curve_to_min_rbf : Prop :=
    ltac:(body_of (fun s : S.statement_valid_arrival_curve_to_min_rbf => s Task tmR)).
  Definition tgt_valid_arrival_curve_to_min_rbf : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_CurveAsRbf_valid_arrival_curve_to_min_rbf Task dT tmL)).
  Theorem valid_arrival_curve_to_min_rbf_correspondence :
    PropSPropRel src_valid_arrival_curve_to_min_rbf tgt_valid_arrival_curve_to_min_rbf.
  Proof.
    apply ar_forall_identity_correspondence => tsk.
    apply cr_forall_family => aR aL Ha.
    apply ar_imp_correspondence; [exact (valid_arrival_curve_correspondence _ _ (Ha tsk))|].
    exact (valid_request_bound_function_correspondence _ _ (task_min_rbf_correspondence _ _ Ha tsk)).
  Qed.

  Definition src_valid_taskset_arrival_curve_to_max_rbf : Prop :=
    ltac:(body_of (fun s : S.statement_valid_taskset_arrival_curve_to_max_rbf => s Task tcR maR)).
  Definition tgt_valid_taskset_arrival_curve_to_max_rbf : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_CurveAsRbf_valid_taskset_arrival_curve_to_max_rbf Task dT tcL maL)).
  Theorem valid_taskset_arrival_curve_to_max_rbf_correspondence :
    PropSPropRel src_valid_taskset_arrival_curve_to_max_rbf tgt_valid_taskset_arrival_curve_to_max_rbf.
  Proof.
    apply cr_forall_list => tsR tsL Hts.
    apply ar_imp_correspondence;
      [exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hma)|].
    exact (valid_taskset_request_bound_function_correspondence Task tsR tsL _ _ Hts
      MaxArrivalsRBF_correspondence).
  Qed.

  Definition src_valid_taskset_arrival_curve_to_min_rbf : Prop :=
    ltac:(body_of (fun s : S.statement_valid_taskset_arrival_curve_to_min_rbf => s Task tmR miR)).
  Definition tgt_valid_taskset_arrival_curve_to_min_rbf : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_CurveAsRbf_valid_taskset_arrival_curve_to_min_rbf Task dT tmL miL)).
  Theorem valid_taskset_arrival_curve_to_min_rbf_correspondence :
    PropSPropRel src_valid_taskset_arrival_curve_to_min_rbf tgt_valid_taskset_arrival_curve_to_min_rbf.
  Proof.
    apply cr_forall_list => tsR tsL Hts.
    apply ar_imp_correspondence;
      [exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hmi)|].
    exact (valid_taskset_request_bound_function_correspondence Task tsR tsL _ _ Hts
      MinArrivalsRBF_correspondence).
  Qed.

  (** ** Job-level theorems *)

  Section WithJobs.
    Context (Job : eqType).
    Let dJ := ar_decidable_eq Job.
    Variable jtR : prosa.model.task.concept.JobTask Job Task.
    Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
    Hypothesis Hjt : forall j : Job,
      Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
    Variable costR : prosa.behavior.job.JobCost Job.
    Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
    Hypothesis Hcost : forall j : Job,
      SubNatRel (@prosa.behavior.job.job_cost Job costR j)
        (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).

    Lemma cr_valid_job_cost_related (j : Job) :
      ArBoolRel (@prosa.model.task.concept.valid_job_cost Task tcR Job jtR costR j)
        (I.Prosa_Model_Task_Concept_valid_job_cost Task dT tcL Job dJ jtL costL j).
    Proof.
      unfold prosa.model.task.concept.valid_job_cost.
      cbn [I.Prosa_Model_Task_Concept_valid_job_cost].
      apply ar_decide_le_related; [exact (Hcost j)|].
      exact (ari_lean_transport (fun v => SubNatRel _ (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v))
        _ _ (Hjt j) (Htc _)).
    Qed.

    Lemma cr_valid_min_job_cost_related (j : Job) :
      ArBoolRel (@prosa.model.task.concept.valid_min_job_cost Task tmR Job jtR costR j)
        (I.Prosa_Model_Task_Concept_valid_min_job_cost Task dT tmL Job dJ jtL costL j).
    Proof.
      unfold prosa.model.task.concept.valid_min_job_cost.
      cbn [I.Prosa_Model_Task_Concept_valid_min_job_cost].
      apply ar_decide_le_related; [|exact (Hcost j)].
      exact (ari_lean_transport (fun v => SubNatRel _ (I.Prosa_Model_Task_Concept_TaskMinCost_task_min_cost Task dT tmL v))
        _ _ (Hjt j) (Htm _)).
    Qed.

    Lemma cr_jobs_have_valid_job_costs_related :
      PropSPropRel (@prosa.model.task.concept.jobs_have_valid_job_costs Task tcR Job jtR costR)
        (I.Prosa_Model_Task_Concept_jobs_have_valid_job_costs Task dT tcL Job dJ jtL costL).
    Proof.
      unfold prosa.model.task.concept.jobs_have_valid_job_costs.
      cbn [I.Prosa_Model_Task_Concept_jobs_have_valid_job_costs].
      apply ar_forall_identity_correspondence => j.
      exact (ar_bool_truth_correspondence _ _ (cr_valid_job_cost_related j)).
    Qed.

    Lemma cr_jobs_have_valid_min_job_costs_related :
      PropSPropRel (@prosa.model.task.concept.jobs_have_valid_min_job_costs Task tmR Job jtR costR)
        (I.Prosa_Model_Task_Concept_jobs_have_valid_min_job_costs Task dT tmL Job dJ jtL costL).
    Proof.
      unfold prosa.model.task.concept.jobs_have_valid_min_job_costs.
      cbn [I.Prosa_Model_Task_Concept_jobs_have_valid_min_job_costs].
      apply ar_forall_identity_correspondence => j.
      exact (ar_bool_truth_correspondence _ _ (cr_valid_min_job_cost_related j)).
    Qed.

    Definition src_respects_arrival_curve_to_max_rbf : Prop :=
      ltac:(body_of (fun s : S.statement_respects_arrival_curve_to_max_rbf => s Task tcR Job jtR costR maR)).
    Definition tgt_respects_arrival_curve_to_max_rbf : SProp :=
      ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_CurveAsRbf_respects_arrival_curve_to_max_rbf
        Task dT tcL Job dJ jtL costL maL)).
    Theorem respects_arrival_curve_to_max_rbf_correspondence :
      PropSPropRel src_respects_arrival_curve_to_max_rbf tgt_respects_arrival_curve_to_max_rbf.
    Proof.
      apply ar_forall_identity_correspondence => tsk.
      apply (cr_forall_arrival_sequence Job) => arrR arrL Harr.
      apply ar_imp_correspondence; [exact cr_jobs_have_valid_job_costs_related|].
      apply ar_imp_correspondence;
        [exact (respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsk _ _ (Hma tsk))|].
      exact (respects_max_request_bound_correspondence Task Job jtR jtL Hjt costR costL Hcost
        arrR arrL Harr tsk _ _ (task_max_rbf_correspondence _ _ Hma tsk)).
    Qed.

    Definition src_respects_arrival_curve_to_min_rbf : Prop :=
      ltac:(body_of (fun s : S.statement_respects_arrival_curve_to_min_rbf => s Task tmR Job jtR costR miR)).
    Definition tgt_respects_arrival_curve_to_min_rbf : SProp :=
      ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_CurveAsRbf_respects_arrival_curve_to_min_rbf
        Task dT tmL Job dJ jtL costL miL)).
    Theorem respects_arrival_curve_to_min_rbf_correspondence :
      PropSPropRel src_respects_arrival_curve_to_min_rbf tgt_respects_arrival_curve_to_min_rbf.
    Proof.
      apply ar_forall_identity_correspondence => tsk.
      apply (cr_forall_arrival_sequence Job) => arrR arrL Harr.
      apply ar_imp_correspondence; [exact cr_jobs_have_valid_min_job_costs_related|].
      apply ar_imp_correspondence;
        [exact (respects_min_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsk _ _ (Hmi tsk))|].
      exact (respects_min_request_bound_correspondence Task Job jtR jtL Hjt costR costL Hcost
        arrR arrL Harr tsk _ _ (task_min_rbf_correspondence _ _ Hmi tsk)).
    Qed.

    Definition src_taskset_respects_arrival_curve_to_max_rbf : Prop :=
      ltac:(body_of (fun s : S.statement_taskset_respects_arrival_curve_to_max_rbf => s Task tcR Job jtR costR maR)).
    Definition tgt_taskset_respects_arrival_curve_to_max_rbf : SProp :=
      ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_CurveAsRbf_taskset_respects_arrival_curve_to_max_rbf
        Task dT tcL Job dJ jtL costL maL)).
    Theorem taskset_respects_arrival_curve_to_max_rbf_correspondence :
      PropSPropRel src_taskset_respects_arrival_curve_to_max_rbf tgt_taskset_respects_arrival_curve_to_max_rbf.
    Proof.
      apply cr_forall_list => tsR tsL Hts.
      apply (cr_forall_arrival_sequence Job) => arrR arrL Harr.
      apply ar_imp_correspondence; [exact cr_jobs_have_valid_job_costs_related|].
      apply ar_imp_correspondence;
        [exact (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr
                  tsR tsL Hts _ _ Hma)|].
      exact (taskset_respects_max_request_bound_correspondence Task Job jtR jtL Hjt costR costL Hcost
        arrR arrL Harr tsR tsL Hts _ _ MaxArrivalsRBF_correspondence).
    Qed.

    Definition src_taskset_respects_arrival_curve_to_min_rbf : Prop :=
      ltac:(body_of (fun s : S.statement_taskset_respects_arrival_curve_to_min_rbf => s Task tmR Job jtR costR miR)).
    Definition tgt_taskset_respects_arrival_curve_to_min_rbf : SProp :=
      ltac:(type_of_term (@I.Prosa_Model_Task_Arrival_CurveAsRbf_taskset_respects_arrival_curve_to_min_rbf
        Task dT tmL Job dJ jtL costL miL)).
    Theorem taskset_respects_arrival_curve_to_min_rbf_correspondence :
      PropSPropRel src_taskset_respects_arrival_curve_to_min_rbf tgt_taskset_respects_arrival_curve_to_min_rbf.
    Proof.
      apply cr_forall_list => tsR tsL Hts.
      apply (cr_forall_arrival_sequence Job) => arrR arrL Harr.
      apply ar_imp_correspondence; [exact cr_jobs_have_valid_min_job_costs_related|].
      apply ar_imp_correspondence;
        [exact (taskset_respects_min_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr
                  tsR tsL Hts _ _ Hmi)|].
      exact (taskset_respects_min_request_bound_correspondence Task Job jtR jtL Hjt costR costL Hcost
        arrR arrL Harr tsR tsL Hts _ _ MinArrivalsRBF_correspondence).
    Qed.
  End WithJobs.
End CurveAsRbf.
