From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.task.arrival.request_bound_functions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRbf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence.

Module I := ImportedRbf.

(** Definition certificates for [model/task/arrival/request_bound_functions.v]: for related
    inputs, each source definition and the compiled Lean definition are
    related.  Request-bound inputs are related pointwise on Nat ([SubNatFunRel]);
    every relation used as an input comes with import/export witnesses in both
    directions, so none of them is vacuous. *)

(** ** Request-bound functions on Nat: two-way coverage *)

Lemma rb_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Definition rb_import_fun (fR : nat -> nat) : Lean.Nat -> Lean.Nat :=
  fun n => sub_nat_to_imported (fR (sub_nat_to_rocq n)).
Definition rb_export_fun (fL : Lean.Nat -> Lean.Nat) : nat -> nat :=
  fun n => sub_nat_to_rocq (fL (sub_nat_to_imported n)).

Lemma rb_import_fun_rel fR : SubNatFunRel fR (rb_import_fun fR).
Proof.
  intros nR nL Hn. unfold SubNatRel, rb_import_fun.
  rewrite (rb_nat_input nR nL Hn). exact (@Lean.eq_refl _ _).
Qed.

Lemma rb_export_fun_rel fL : SubNatFunRel (rb_export_fun fL) fL.
Proof.
  intros nR nL Hn. unfold SubNatRel, rb_export_fun.
  exact (sub_imported_eq_trans _ _ _ (sub_nat_imported_roundtrip _)
    (sub_imported_eq_congr fL _ _ Hn)).
Qed.

Theorem valid_request_bound_function_correspondence fR fL :
  SubNatFunRel fR fL ->
  PropSPropRel (@prosa.model.task.arrival.request_bound_functions.valid_request_bound_function fR)
    (I.Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_request_bound_function fL).
Proof.
  intro Hf.
  unfold prosa.model.task.arrival.request_bound_functions.valid_request_bound_function.
  cbn [I.Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_request_bound_function].
  apply ar_and_correspondence.
  - exact (sub_nat_eq_correspondence _ _ _ _
      (Hf O Lean.Nat_zero (sub_nat_rel_canonical O)) (sub_nat_rel_canonical O)).
  - unfold prosa.util.rel.monotone. cbn [I.Prosa_Util_Rel_monotone].
    apply ar_forall_nat_correspondence => xR xL Hx.
    apply ar_forall_nat_correspondence => yR yL Hy.
    apply ar_imp_correspondence.
    + exact (ar_bool_truth_correspondence _ _ (ar_decide_le_related _ _ _ _ Hx Hy)).
    + exact (ar_bool_truth_correspondence _ _
        (ar_decide_le_related _ _ _ _ (Hf _ _ Hx) (Hf _ _ Hy))).
Qed.

Section Rbf.
  Context (Task Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let dT := ar_decidable_eq Task.
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
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let COST tsk t1R t1L t2R t2L H1 H2 :=
    cost_of_task_arrivals_correspondence Job Task jtR jtL Hjt arrR arrL Harr costR costL Hcost
      tsk tsk t1R t1L t2R t2L (@Lean.eq_refl _ tsk) H1 H2.

  Theorem respects_max_request_bound_correspondence (tsk : Task) fR fL :
    SubNatFunRel fR fL ->
    PropSPropRel
      (@prosa.model.task.arrival.request_bound_functions.respects_max_request_bound Task Job jtR costR arrR tsk fR)
      (I.Prosa_Model_Task_Arrival_RequestBoundFunctions_respects_max_request_bound Task dT Job dJ jtL costL arrL tsk fL).
  Proof.
    intro Hf.
    unfold prosa.model.task.arrival.request_bound_functions.respects_max_request_bound.
    cbn [I.Prosa_Model_Task_Arrival_RequestBoundFunctions_respects_max_request_bound].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
    exact (sub_nat_le_correspondence _ _ _ _ (COST tsk _ _ _ _ H1 H2)
      (Hf _ _ (ari_nat_sub_related _ _ _ _ H2 H1))).
  Qed.

  Theorem respects_min_request_bound_correspondence (tsk : Task) fR fL :
    SubNatFunRel fR fL ->
    PropSPropRel
      (@prosa.model.task.arrival.request_bound_functions.respects_min_request_bound Task Job jtR costR arrR tsk fR)
      (I.Prosa_Model_Task_Arrival_RequestBoundFunctions_respects_min_request_bound Task dT Job dJ jtL costL arrL tsk fL).
  Proof.
    intro Hf.
    unfold prosa.model.task.arrival.request_bound_functions.respects_min_request_bound.
    cbn [I.Prosa_Model_Task_Arrival_RequestBoundFunctions_respects_min_request_bound].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (Hf _ _ (ari_nat_sub_related _ _ _ _ H2 H1)) (COST tsk _ _ _ _ H1 H2)).
  Qed.
End Rbf.

Section TaskSet.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.

  Definition RbFamilyRel (fR : Task -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat) : SProp :=
    forall tsk : Task, SubNatFunRel (fR tsk) (fL tsk).

  Lemma rb_family_import fR : RbFamilyRel fR (fun tsk => rb_import_fun (fR tsk)).
  Proof. intro tsk. exact (rb_import_fun_rel _). Qed.
  Lemma rb_family_export fL : RbFamilyRel (fun tsk => rb_export_fun (fL tsk)) fL.
  Proof. intro tsk. exact (rb_export_fun_rel _). Qed.

  Definition RbMaxRel (cR : prosa.model.task.arrival.request_bound_functions.MaxRequestBound Task)
      (cL : I.Prosa_Model_Task_Arrival_RequestBoundFunctions_MaxRequestBound Task dT) : SProp :=
    RbFamilyRel (@prosa.model.task.arrival.request_bound_functions.max_request_bound Task cR)
      (I.Prosa_Model_Task_Arrival_RequestBoundFunctions_MaxRequestBound_max_request_bound Task dT cL).
  Definition RbMinRel (cR : prosa.model.task.arrival.request_bound_functions.MinRequestBound Task)
      (cL : I.Prosa_Model_Task_Arrival_RequestBoundFunctions_MinRequestBound Task dT) : SProp :=
    RbFamilyRel (@prosa.model.task.arrival.request_bound_functions.min_request_bound Task cR)
      (I.Prosa_Model_Task_Arrival_RequestBoundFunctions_MinRequestBound_min_request_bound Task dT cL).

  Lemma MaxRequestBound_source_total cR : RbMaxRel cR
    (I.Prosa_Model_Task_Arrival_RequestBoundFunctions_MaxRequestBound_mk Task dT (fun tsk => rb_import_fun (cR tsk))).
  Proof. exact (rb_family_import _). Qed.
  Lemma MaxRequestBound_target_total cL : RbMaxRel
    (fun tsk => rb_export_fun (I.Prosa_Model_Task_Arrival_RequestBoundFunctions_MaxRequestBound_max_request_bound Task dT cL tsk)) cL.
  Proof. exact (rb_family_export _). Qed.
  Lemma MinRequestBound_source_total cR : RbMinRel cR
    (I.Prosa_Model_Task_Arrival_RequestBoundFunctions_MinRequestBound_mk Task dT (fun tsk => rb_import_fun (cR tsk))).
  Proof. exact (rb_family_import _). Qed.
  Lemma MinRequestBound_target_total cL : RbMinRel
    (fun tsk => rb_export_fun (I.Prosa_Model_Task_Arrival_RequestBoundFunctions_MinRequestBound_min_request_bound Task dT cL tsk)) cL.
  Proof. exact (rb_family_export _). Qed.

  Theorem valid_taskset_request_bound_function_correspondence tsR tsL aR aL :
    ArListRel tsR tsL -> RbFamilyRel aR aL ->
    PropSPropRel
      (@prosa.model.task.arrival.request_bound_functions.valid_taskset_request_bound_function Task tsR aR)
      (I.Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_taskset_request_bound_function Task dT tsL aL).
  Proof.
    intros Hts Ha.
    unfold prosa.model.task.arrival.request_bound_functions.valid_taskset_request_bound_function.
    cbn [I.Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_taskset_request_bound_function].
    apply ar_forall_identity_correspondence => tsk.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    exact (valid_request_bound_function_correspondence _ _ (Ha tsk)).
  Qed.

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
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
    Variable tsR : prosa.model.task.concept.TaskSet Task.
    Variable tsL : I.Prosa_Model_Task_Concept_TaskSet Task.
    Hypothesis Hts : ArListRel tsR tsL.

    Let MEM tsk := ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts).

    Theorem taskset_respects_max_request_bound_correspondence cR cL :
      RbMaxRel cR cL ->
      PropSPropRel
        (@prosa.model.task.arrival.request_bound_functions.taskset_respects_max_request_bound Task Job jtR costR arrR cR tsR)
        (I.Prosa_Model_Task_Arrival_RequestBoundFunctions_taskset_respects_max_request_bound Task dT Job dJ jtL costL arrL cL tsL).
    Proof.
      intro Hc.
      unfold prosa.model.task.arrival.request_bound_functions.taskset_respects_max_request_bound.
      cbn [I.Prosa_Model_Task_Arrival_RequestBoundFunctions_taskset_respects_max_request_bound].
      apply ar_forall_identity_correspondence => tsk.
      apply ar_imp_correspondence; [exact (MEM tsk)|].
      exact (respects_max_request_bound_correspondence Task Job jtR jtL Hjt costR costL Hcost
        arrR arrL Harr tsk _ _ (Hc tsk)).
    Qed.

    Theorem taskset_respects_min_request_bound_correspondence cR cL :
      RbMinRel cR cL ->
      PropSPropRel
        (@prosa.model.task.arrival.request_bound_functions.taskset_respects_min_request_bound Task Job jtR costR arrR cR tsR)
        (I.Prosa_Model_Task_Arrival_RequestBoundFunctions_taskset_respects_min_request_bound Task dT Job dJ jtL costL arrL cL tsL).
    Proof.
      intro Hc.
      unfold prosa.model.task.arrival.request_bound_functions.taskset_respects_min_request_bound.
      cbn [I.Prosa_Model_Task_Arrival_RequestBoundFunctions_taskset_respects_min_request_bound].
      apply ar_forall_identity_correspondence => tsk.
      apply ar_imp_correspondence; [exact (MEM tsk)|].
      exact (respects_min_request_bound_correspondence Task Job jtR jtL Hjt costR costL Hcost
        arrR arrL Harr tsk _ _ (Hc tsk)).
    Qed.
  End WithJobs.
End TaskSet.
