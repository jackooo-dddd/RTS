From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.task.jitter.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskJitter ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence TaskJitterBaseAdapter.

Module I := ImportedTaskJitter.

(** Correspondence certificates for [model/task/jitter.v].  The logical and
    membership combinators are the accepted Sporadic ones (bodies copied and
    rechecked against this artifact); no source or target theorem is used. *)

Definition tj_target_false_elim (Q : SProp) (H : I.False) : Q :=
  match H return Q with end.

Lemma tj_decide_bool_correspondence (b : bool) (Q : SProp) (d : I.Decidable Q) :
  PropSPropRel (is_true b) Q -> ArBoolRel b (I.Decidable_decide Q d).
Proof.
  intro Hrel. unfold ArBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (tj_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (tj_target_false_elim _ (ar_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Definition tj_target_decide_mem (T : eqType) (x : T) (xs : I.List T) : I.Bool :=
  I.Decidable_decide (ar_target_mem x xs)
    (I.List_instDecidableMemOfLawfulBEq T
      (I.instBEqOfDecidableEq T (ar_decidable_eq T))
      (I.instLawfulBEq T (ar_decidable_eq T)) x xs).

Lemma tj_decide_mem_related (T : eqType) (x : T) (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL -> ArBoolRel (x \in xsR) (tj_target_decide_mem T x xsL).
Proof.
  intro Hxs. apply tj_decide_bool_correspondence.
  exact (ar_membership_correspondence T x xsR xsL Hxs).
Qed.

Lemma tj_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. apply (prop_to_sprop _ _ HQ). exact (H (sprop_to_prop _ _ HP p)).
  - intro H. apply strictly_inhabits. intro p.
    apply (sprop_to_prop _ _ HQ). exact (H (prop_to_sprop _ _ HP p)).
Qed.

Lemma tj_forall_identity_correspondence (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (HP x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x. exact (sprop_to_prop _ _ (HP x) (HL x)).
Qed.

Lemma tj_eq_correspondence (T : Type) (xR xL yR yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hx) Hy).
  - intro Heq. apply strictly_inhabits.
    exact (imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hx (sub_imported_eq_trans _ _ _ Heq
        (sub_imported_eq_sym _ _ Hy)))).
Qed.

(** ** TaskJitter class: carrier coverage in both directions *)

Definition TjTaskJitterRel (Task : eqType)
    (tjR : prosa.model.task.jitter.TaskJitter Task)
    (tjL : I.Prosa_Model_Task_Jitter_TaskJitter Task (ar_decidable_eq Task)) : SProp :=
  forall tsk : Task,
    SubNatRel (@prosa.model.task.jitter.task_jitter Task tjR tsk)
      (I.Prosa_Model_Task_Jitter_TaskJitter_task_jitter Task (ar_decidable_eq Task) tjL tsk).

Definition tj_import_task_jitter (Task : eqType)
    (tjR : prosa.model.task.jitter.TaskJitter Task) :
    I.Prosa_Model_Task_Jitter_TaskJitter Task (ar_decidable_eq Task) :=
  I.Prosa_Model_Task_Jitter_TaskJitter_mk Task (ar_decidable_eq Task)
    (fun tsk => sub_nat_to_imported (@prosa.model.task.jitter.task_jitter Task tjR tsk)).

Definition tj_export_task_jitter (Task : eqType)
    (tjL : I.Prosa_Model_Task_Jitter_TaskJitter Task (ar_decidable_eq Task)) :
    prosa.model.task.jitter.TaskJitter Task :=
  fun tsk => sub_nat_to_rocq
    (I.Prosa_Model_Task_Jitter_TaskJitter_task_jitter Task (ar_decidable_eq Task) tjL tsk).

Lemma TaskJitter_source_total (Task : eqType) (tjR : prosa.model.task.jitter.TaskJitter Task) :
  TjTaskJitterRel Task tjR (tj_import_task_jitter Task tjR).
Proof. intro tsk. exact (@Lean.eq_refl _ _). Qed.

Lemma TaskJitter_target_total (Task : eqType)
    (tjL : I.Prosa_Model_Task_Jitter_TaskJitter Task (ar_decidable_eq Task)) :
  TjTaskJitterRel Task (tj_export_task_jitter Task tjL) tjL.
Proof. intro tsk. exact (sub_nat_imported_roundtrip _). Qed.

Lemma TaskJitter_source_roundtrip (Task : eqType)
    (tjR : prosa.model.task.jitter.TaskJitter Task) (tsk : Task) :
  Logic.eq (@prosa.model.task.jitter.task_jitter Task
      (tj_export_task_jitter Task (tj_import_task_jitter Task tjR)) tsk)
    (@prosa.model.task.jitter.task_jitter Task tjR tsk).
Proof. exact (sub_nat_rocq_roundtrip _). Qed.

(** ** valid_jitter and valid_jitter_bounds *)

Section ValidJitter.
  Context (Task Job : eqType).
  Variable tjR : prosa.model.task.jitter.TaskJitter Task.
  Variable tjL : I.Prosa_Model_Task_Jitter_TaskJitter Task (ar_decidable_eq Task).
  Hypothesis Htj : TjTaskJitterRel Task tjR tjL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job (ar_decidable_eq Job)
    Task (ar_decidable_eq Task).
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job (ar_decidable_eq Job)
        Task (ar_decidable_eq Task) jtL j).
  Variable jjR : prosa.model.readiness.jitter.JobJitter Job.
  Variable jjL : I.Prosa_Model_Readiness_Jitter_JobJitter Job (ar_decidable_eq Job).
  Hypothesis Hjj : forall j : Job,
    SubNatRel (@prosa.model.readiness.jitter.job_jitter Job jjR j)
      (I.Prosa_Model_Readiness_Jitter_JobJitter_job_jitter Job (ar_decidable_eq Job) jjL j).

  Lemma valid_jitter_correspondence (tsk : Task) :
    PropSPropRel
      (@prosa.model.task.jitter.valid_jitter Task tjR Job jtR jjR tsk)
      (I.Prosa_Model_Task_Jitter_valid_jitter Task (ar_decidable_eq Task) tjL
        Job (ar_decidable_eq Job) jtL jjL tsk).
  Proof.
    unfold prosa.model.task.jitter.valid_jitter.
    cbn [I.Prosa_Model_Task_Jitter_valid_jitter].
    apply tj_forall_identity_correspondence. intro j.
    apply tj_imp_correspondence.
    - exact (tj_eq_correspondence Task _ _ tsk tsk (Hjt j) (@Lean.eq_refl _ _)).
    - exact (sub_nat_le_correspondence _ _ _ _ (Hjj j) (Htj tsk)).
  Qed.

  Lemma valid_jitter_bounds_correspondence
      (tsR : prosa.model.task.concept.TaskSet Task)
      (tsL : I.Prosa_Model_Task_Concept_TaskSet Task) :
    ArListRel tsR tsL ->
    PropSPropRel
      (@prosa.model.task.jitter.valid_jitter_bounds Task tjR Job jtR jjR tsR)
      (I.Prosa_Model_Task_Jitter_valid_jitter_bounds Task (ar_decidable_eq Task) tjL
        Job (ar_decidable_eq Job) jtL jjL tsL).
  Proof.
    intro Hts.
    unfold prosa.model.task.jitter.valid_jitter_bounds.
    cbn [I.Prosa_Model_Task_Jitter_valid_jitter_bounds].
    apply tj_forall_identity_correspondence. intro tsk.
    apply tj_imp_correspondence.
    - apply ar_bool_truth_correspondence.
      exact (tj_decide_mem_related Task tsk tsR tsL Hts).
    - exact (valid_jitter_correspondence tsk).
  Qed.
End ValidJitter.

(** Exact-type guards against the imported declarations. *)
Definition tj_target_valid_jitter_type_guard :=
  @I.Prosa_Model_Task_Jitter_valid_jitter.
Definition tj_target_valid_jitter_bounds_type_guard :=
  @I.Prosa_Model_Task_Jitter_valid_jitter_bounds.

Print Assumptions valid_jitter_bounds_correspondence.
