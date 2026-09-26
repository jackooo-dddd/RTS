From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import analysis.definitions.overheads.priority_bump.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityBump.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

Module I := ImportedPriorityBump.

(** Certificate for [analysis/definitions/overheads/priority_bump.v].

    A minimal artifact-local adapter for this imported artifact (Booleans,
    decidable equality, options, the Overheads processor state and
    schedules, JLFP policies), following the accepted
    overheads/schedule_change and priority certificates, then the
    definition certificate.  Every input relation has two-way totals. *)

Inductive PbFalse : SProp := .
Inductive PbTrue : SProp := pb_true_intro.

Definition pb_coq_false_to_target (H : Logic.False) : I.False :=
  match H return I.False with end.

Definition pb_bool_to_imported (b : bool) : I.Bool :=
  match b with true => I.Bool_true | false => I.Bool_false end.
Definition pb_bool_to_rocq (b : I.Bool) : bool :=
  match b with I.Bool_true => true | I.Bool_false => false end.
Definition PbBoolRel (bR : bool) (bL : I.Bool) : SProp :=
  Lean.eq (pb_bool_to_imported bR) bL.

Lemma pb_bool_target_roundtrip (b : I.Bool) :
  Lean.eq (pb_bool_to_imported (pb_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma pb_bool_not_related bR bL :
  PbBoolRel bR bL -> PbBoolRel (~~ bR) (I.Bool_not bL).
Proof.
  intro Hb. unfold PbBoolRel in *.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_congr I.Bool_not _ _ Hb)).
  destruct bR; exact (@Lean.eq_refl _ _).
Qed.

Definition pb_decidable_eq (T : eqType) : I.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => I.Decidable_isTrue (Lean.eq x y) (coq_eq_to_imported_eq x y H)
    | ReflectF H => I.Decidable_isFalse (Lean.eq x y)
        (fun HL => pb_coq_false_to_target (H (imported_eq_to_coq_eq x y HL)))
    end.

(** Options and the Overheads processor state. *)
Definition pb_option_to_imported {T : Type} (x : option T) : I.Option T :=
  match x with None => I.Option_none T | Some j => I.Option_some T j end.
Definition pb_option_to_rocq {T : Type} (x : I.Option T) : option T :=
  match x with I.Option_none => None | I.Option_some j => Some j end.
Definition PbOptionRel {T : Type} (xR : option T) (xL : I.Option T) : SProp :=
  Lean.eq (pb_option_to_imported xR) xL.

Definition pb_state_to_imported (Job : eqType)
    (s : @prosa.model.processor.overheads.proc_state Job) :
    I.Prosa_Model_Processor_Overheads_proc_state Job :=
  match s with
  | prosa.model.processor.overheads.Idle =>
      I.Prosa_Model_Processor_Overheads_proc_state_Idle Job
  | prosa.model.processor.overheads.ContextSwitch j1 j2 =>
      I.Prosa_Model_Processor_Overheads_proc_state_ContextSwitch Job
        (pb_option_to_imported j1) (pb_option_to_imported j2)
  | prosa.model.processor.overheads.Dispatch j =>
      I.Prosa_Model_Processor_Overheads_proc_state_Dispatch Job (pb_option_to_imported j)
  | prosa.model.processor.overheads.CacheRelatedPreemptionDelay j =>
      I.Prosa_Model_Processor_Overheads_proc_state_CacheRelatedPreemptionDelay Job j
  | prosa.model.processor.overheads.Progress j =>
      I.Prosa_Model_Processor_Overheads_proc_state_Progress Job j
  end.

Definition pb_state_to_rocq (Job : eqType)
    (s : I.Prosa_Model_Processor_Overheads_proc_state Job) :
    @prosa.model.processor.overheads.proc_state Job :=
  match s with
  | I.Prosa_Model_Processor_Overheads_proc_state_Idle =>
      @prosa.model.processor.overheads.Idle Job
  | I.Prosa_Model_Processor_Overheads_proc_state_ContextSwitch j1 j2 =>
      @prosa.model.processor.overheads.ContextSwitch Job (pb_option_to_rocq j1) (pb_option_to_rocq j2)
  | I.Prosa_Model_Processor_Overheads_proc_state_Dispatch j =>
      @prosa.model.processor.overheads.Dispatch Job (pb_option_to_rocq j)
  | I.Prosa_Model_Processor_Overheads_proc_state_CacheRelatedPreemptionDelay j =>
      @prosa.model.processor.overheads.CacheRelatedPreemptionDelay Job j
  | I.Prosa_Model_Processor_Overheads_proc_state_Progress j =>
      @prosa.model.processor.overheads.Progress Job j
  end.

Lemma pb_state_target_roundtrip (Job : eqType) s :
  Lean.eq (pb_state_to_imported Job (pb_state_to_rocq Job s)) s.
Proof.
  destruct s as [|a b|a|a|a]; cbn;
    try destruct a; try destruct b; exact (@Lean.eq_refl _ _).
Qed.

Definition PbScheduleRel (Job : eqType)
    (schedR : @prosa.behavior.schedule.schedule Job
      (@prosa.model.processor.overheads.processor_state Job))
    (schedL : Lean.Nat -> I.Prosa_Model_Processor_Overheads_proc_state Job) : SProp :=
  forall tR tL, SubNatRel tR tL ->
    Lean.eq (pb_state_to_imported Job (schedR tR)) (schedL tL).

Lemma PbSchedule_source_total (Job : eqType) schedR :
  PbScheduleRel Job schedR
    (fun tL => pb_state_to_imported Job (schedR (sub_nat_to_rocq tL))).
Proof.
  move=> tR tL Ht.
  have Ht' : Logic.eq (sub_nat_to_rocq tL) tR :=
    Logic.eq_trans (f_equal sub_nat_to_rocq (Logic.eq_sym (imported_eq_to_coq_eq _ _ Ht)))
      (sub_nat_rocq_roundtrip tR).
  rewrite Ht'. exact (@Lean.eq_refl _ _).
Qed.

Lemma PbSchedule_target_total (Job : eqType) schedL :
  PbScheduleRel Job (fun tR => pb_state_to_rocq Job (schedL (sub_nat_to_imported tR))) schedL.
Proof.
  move=> tR tL Ht.
  refine (sub_imported_eq_trans _ _ _ (pb_state_target_roundtrip Job _) _).
  exact (sub_imported_eq_congr schedL _ _ Ht).
Qed.

Lemma pb_scheduled_job_related (Job : eqType) schedR schedL (tR : nat) (tL : Lean.Nat) :
  PbScheduleRel Job schedR schedL -> SubNatRel tR tL ->
  PbOptionRel (@prosa.model.processor.overheads.scheduled_job Job schedR tR)
    (I.Prosa_Model_Processor_Overheads_scheduled_job Job (pb_decidable_eq Job) schedL tL).
Proof.
  intros Hsched Ht.
  unfold prosa.model.processor.overheads.scheduled_job,
    I.Prosa_Model_Processor_Overheads_scheduled_job.
  have Hstate : Logic.eq (pb_state_to_imported Job (schedR tR)) (schedL tL) :=
    imported_eq_to_coq_eq _ _ (Hsched tR tL Ht).
  rewrite <- Hstate.
  destruct (schedR tR) as [|a b|a|a|a]; cbn; exact (@Lean.eq_refl _ _).
Qed.

Lemma pb_pred_related (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> SubNatRel nR.-1 (I.Nat_pred nL).
Proof.
  intro Hn. unfold SubNatRel in Hn |- *.
  have Hn' := imported_eq_to_coq_eq _ _ Hn.
  rewrite <- Hn'. destruct nR; cbn; exact (@Lean.eq_refl _ _).
Qed.

(** JLFP policies. *)
Definition PbJLFPRel (Job : eqType)
    (pR : prosa.model.priority.definitions.JLFP_policy Job)
    (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job (pb_decidable_eq Job)) : SProp :=
  forall x y : Job,
    PbBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job (pb_decidable_eq Job) pL x y).

Lemma JLFP_policy_source_total (Job : eqType) pR :
  PbJLFPRel Job pR
    (I.Prosa_Model_Priority_Definitions_JLFP_policy_mk Job (pb_decidable_eq Job)
      (fun x y => pb_bool_to_imported (@prosa.model.priority.definitions.hep_job Job pR x y))).
Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

Lemma JLFP_policy_target_total (Job : eqType) pL :
  PbJLFPRel Job
    (fun x y => pb_bool_to_rocq
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job (pb_decidable_eq Job) pL x y)) pL.
Proof. intros x y. exact (pb_bool_target_roundtrip _). Qed.

Lemma pb_transport {A : Type} (P : A -> SProp) (x y : A) : Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Section PriorityBump.
  Context (Job : eqType).
  Let dJ := pb_decidable_eq Job.
  Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hp : PbJLFPRel Job pR pL.

  Definition pb_source_match (a b : option Job) : bool :=
    match a, b with
    | None, None => false
    | None, Some _ => true
    | Some _, None => false
    | Some j1, Some j2 => ~~ @prosa.model.priority.definitions.hep_job Job pR j1 j2
    end.

  Definition pb_target_match (a b : I.Option Job) : I.Bool :=
    I.Prosa_Analysis_Definitions_Overheads_PriorityBump_priority_bump_match_1 Job
      (fun _ _ => I.Bool) a b (fun _ => I.Bool_false) (fun _ => I.Bool_true)
      (fun _ => I.Bool_false)
      (fun j1 j2 => I.Bool_not (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL j1 j2)).

  Lemma pb_match_related (a b : option Job) (aL bL : I.Option Job) :
    PbOptionRel a aL -> PbOptionRel b bL ->
    PbBoolRel (pb_source_match a b) (pb_target_match aL bL).
  Proof.
    intros Ha Hb.
    refine (pb_transport (fun x => PbBoolRel _ (pb_target_match x bL)) _ _ Ha _).
    refine (pb_transport (fun x => PbBoolRel _ (pb_target_match (pb_option_to_imported a) x)) _ _ Hb _).
    destruct a as [j1|], b as [j2|]; cbn.
    - exact (pb_bool_not_related _ _ (Hp j1 j2)).
    - exact (@Lean.eq_refl _ _).
    - exact (@Lean.eq_refl _ _).
    - exact (@Lean.eq_refl _ _).
  Qed.

  Theorem priority_bump_correspondence schedR schedL (tR : nat) (tL : Lean.Nat) :
    PbScheduleRel Job schedR schedL -> SubNatRel tR tL ->
    PbBoolRel (@prosa.analysis.definitions.overheads.priority_bump.priority_bump Job pR schedR tR)
      (I.Prosa_Analysis_Definitions_Overheads_PriorityBump_priority_bump Job dJ pL schedL tL).
  Proof.
    intros Hsched Ht.
    exact (pb_match_related _ _ _ _
      (pb_scheduled_job_related Job schedR schedL _ _ Hsched (pb_pred_related tR tL Ht))
      (pb_scheduled_job_related Job schedR schedL _ _ Hsched Ht)).
  Qed.
End PriorityBump.
