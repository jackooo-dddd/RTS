(* Re-bound copy of the accepted certificates/model_priority_definitions/PriorityBaseAdapter.v:
   only the imported module (ImportedPriorityDefinitions -> ImportedPriorityCoercion),
   the certificate module prefix (Priority -> Pco) and its logical path are renamed. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From prosa Require Import model.priority.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityCoercion.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence.

(** Artifact-local Boolean, equality, and class bridges.  Every right-hand
    operation below is from the actual compiled priority artifact. *)

Definition pd_bool_to_imported (b : bool) : ImportedPriorityCoercion.Bool :=
  match b with
  | true => ImportedPriorityCoercion.Bool_true
  | false => ImportedPriorityCoercion.Bool_false
  end.

Definition pd_bool_to_rocq (b : ImportedPriorityCoercion.Bool) : bool :=
  match b with
  | ImportedPriorityCoercion.Bool_true => true
  | ImportedPriorityCoercion.Bool_false => false
  end.

Definition PdBoolRel (bR : bool) (bL : ImportedPriorityCoercion.Bool) : SProp :=
  Lean.eq (pd_bool_to_imported bR) bL.

Lemma pd_bool_source_roundtrip (b : bool) :
  Logic.eq (pd_bool_to_rocq (pd_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma pd_bool_target_roundtrip (b : ImportedPriorityCoercion.Bool) :
  Lean.eq (pd_bool_to_imported (pd_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Inductive PdFalse : SProp := .
Inductive PdTrue : SProp := pd_true_intro.

Definition pd_false_ne_true
    (H : Lean.eq ImportedPriorityCoercion.Bool_false
      ImportedPriorityCoercion.Bool_true) : PdFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedPriorityCoercion.Bool_false => PdTrue
    | ImportedPriorityCoercion.Bool_true => PdFalse
    end
  with Lean.eq_refl => pd_true_intro end.

Definition pd_false_to_strict (H : PdFalse) :
    StrictlyInhabited Logic.False := match H with end.

Lemma pd_bool_truth_correspondence bR bL :
  PdBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedPriorityCoercion.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (pd_false_to_strict (pd_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Lemma pd_bool_or_canonical aR bR :
  Lean.eq (pd_bool_to_imported (aR || bR))
    (ImportedPriorityCoercion.Bool_or
      (pd_bool_to_imported aR) (pd_bool_to_imported bR)).
Proof. destruct aR, bR; exact (@Lean.eq_refl _ _). Qed.

Lemma pd_bool_or_related aR aL bR bL :
  PdBoolRel aR aL -> PdBoolRel bR bL ->
  PdBoolRel (aR || bR) (ImportedPriorityCoercion.Bool_or aL bL).
Proof.
  intros Ha Hb. unfold PdBoolRel in *.
  exact (sub_imported_eq_trans _ _ _ (pd_bool_or_canonical aR bR)
    (sub_imported_eq_congr2 ImportedPriorityCoercion.Bool_or
      _ _ _ _ Ha Hb)).
Qed.

Lemma pd_bool_and_canonical aR bR :
  Lean.eq (pd_bool_to_imported (aR && bR))
    (ImportedPriorityCoercion.Bool_and
      (pd_bool_to_imported aR) (pd_bool_to_imported bR)).
Proof. destruct aR, bR; exact (@Lean.eq_refl _ _). Qed.

Lemma pd_bool_and_related aR aL bR bL :
  PdBoolRel aR aL -> PdBoolRel bR bL ->
  PdBoolRel (aR && bR) (ImportedPriorityCoercion.Bool_and aL bL).
Proof.
  intros Ha Hb. unfold PdBoolRel in *.
  exact (sub_imported_eq_trans _ _ _ (pd_bool_and_canonical aR bR)
    (sub_imported_eq_congr2 ImportedPriorityCoercion.Bool_and
      _ _ _ _ Ha Hb)).
Qed.

Lemma pd_bool_not_canonical bR :
  Lean.eq (pd_bool_to_imported (~~ bR))
    (ImportedPriorityCoercion.Bool_not (pd_bool_to_imported bR)).
Proof. destruct bR; exact (@Lean.eq_refl _ _). Qed.

Lemma pd_bool_not_related bR bL :
  PdBoolRel bR bL ->
  PdBoolRel (~~ bR) (ImportedPriorityCoercion.Bool_not bL).
Proof.
  intro Hb. unfold PdBoolRel in *.
  exact (sub_imported_eq_trans _ _ _ (pd_bool_not_canonical bR)
    (sub_imported_eq_congr ImportedPriorityCoercion.Bool_not _ _ Hb)).
Qed.

Definition pd_false_to_imported (H : Logic.False) :
    ImportedPriorityCoercion.False :=
  match H return ImportedPriorityCoercion.False with end.

Definition pd_decidable_eq (T : eqType) :
    ImportedPriorityCoercion.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H =>
        ImportedPriorityCoercion.Decidable_isTrue (Lean.eq x y)
          (coq_eq_to_imported_eq x y H)
    | ReflectF H =>
        ImportedPriorityCoercion.Decidable_isFalse (Lean.eq x y)
          (fun HL => pd_false_to_imported
            (H (imported_eq_to_coq_eq x y HL)))
    end.

Lemma pd_eq_observation (T : eqType) (x y : T) :
  PdBoolRel (x == y)
    (ImportedPriorityCoercion.Decidable_decide (Lean.eq x y)
      (pd_decidable_eq T x y)).
Proof.
  unfold pd_decidable_eq, PdBoolRel.
  destruct (@eqP T x y); cbn; exact (@Lean.eq_refl _ _).
Qed.

Lemma pd_ne_observation (T : eqType) (x y : T) :
  PdBoolRel (x != y)
    (ImportedPriorityCoercion.Decidable_decide
      (ImportedPriorityCoercion.Ne T x y)
      (ImportedPriorityCoercion.instDecidableNot (Lean.eq x y)
        (pd_decidable_eq T x y))).
Proof.
  unfold pd_decidable_eq, PdBoolRel.
  destruct (@eqP T x y); cbn; exact (@Lean.eq_refl _ _).
Qed.

Definition pd_target_decide_eq (T : eqType) (x y : T) :
    ImportedPriorityCoercion.Bool :=
  ImportedPriorityCoercion.Decidable_decide (Lean.eq x y)
    (pd_decidable_eq T x y).

Definition pd_target_decide_ne (T : eqType) (x y : T) :
    ImportedPriorityCoercion.Bool :=
  ImportedPriorityCoercion.Decidable_decide
    (ImportedPriorityCoercion.Ne T x y)
    (ImportedPriorityCoercion.instDecidableNot (Lean.eq x y)
      (pd_decidable_eq T x y)).

Lemma pd_eq_observation_transport (T : eqType)
    (xR yR xL yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL ->
  PdBoolRel (xR == yR) (pd_target_decide_eq T xL yL).
Proof.
  intros Hx Hy. unfold PdBoolRel.
  exact (sub_imported_eq_trans _ _ _ (pd_eq_observation T xR yR)
    (sub_imported_eq_congr2 (pd_target_decide_eq T)
      _ _ _ _ Hx Hy)).
Qed.

Lemma pd_ne_observation_transport (T : eqType)
    (xR yR xL yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL ->
  PdBoolRel (xR != yR) (pd_target_decide_ne T xL yL).
Proof.
  intros Hx Hy. unfold PdBoolRel.
  exact (sub_imported_eq_trans _ _ _ (pd_ne_observation T xR yR)
    (sub_imported_eq_congr2 (pd_target_decide_ne T)
      _ _ _ _ Hx Hy)).
Qed.

Definition PdJobTaskRel (Job Task : eqType)
    (jtR : prosa.model.task.concept.JobTask Job Task)
    (jtL : ImportedPriorityCoercion.Prosa_Model_Task_Concept_JobTask
      Job (pd_decidable_eq Job) Task (pd_decidable_eq Task)) : SProp :=
  forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (ImportedPriorityCoercion.Prosa_Model_Task_Concept_JobTask_job_task
        Job (pd_decidable_eq Job) Task (pd_decidable_eq Task) jtL j).

Definition pd_import_job_task (Job Task : eqType)
    (jtR : prosa.model.task.concept.JobTask Job Task) :
    ImportedPriorityCoercion.Prosa_Model_Task_Concept_JobTask
      Job (pd_decidable_eq Job) Task (pd_decidable_eq Task) :=
  ImportedPriorityCoercion.Prosa_Model_Task_Concept_JobTask_mk
    Job (pd_decidable_eq Job) Task (pd_decidable_eq Task)
    (fun j => @prosa.model.task.concept.job_task Job Task jtR j).

Lemma pd_job_task_import_certificate (Job Task : eqType)
    (jtR : prosa.model.task.concept.JobTask Job Task) :
  PdJobTaskRel Job Task jtR (pd_import_job_task Job Task jtR).
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Definition pd_export_job_task (Job Task : eqType)
    (jtL : ImportedPriorityCoercion.Prosa_Model_Task_Concept_JobTask
      Job (pd_decidable_eq Job) Task (pd_decidable_eq Task)) :
    prosa.model.task.concept.JobTask Job Task :=
  fun j => ImportedPriorityCoercion.Prosa_Model_Task_Concept_JobTask_job_task
    Job (pd_decidable_eq Job) Task (pd_decidable_eq Task) jtL j.

Lemma pd_job_task_export_certificate (Job Task : eqType)
    (jtL : ImportedPriorityCoercion.Prosa_Model_Task_Concept_JobTask
      Job (pd_decidable_eq Job) Task (pd_decidable_eq Task)) :
  PdJobTaskRel Job Task (pd_export_job_task Job Task jtL) jtL.
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Definition PdJobArrivalRel (Job : eqType)
    (aR : prosa.behavior.job.JobArrival Job)
    (aL : ImportedPriorityCoercion.Prosa_Behavior_Job_JobArrival
      Job (pd_decidable_eq Job)) : SProp :=
  forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job aR j)
      (ImportedPriorityCoercion.Prosa_Behavior_Job_JobArrival_job_arrival
        Job (pd_decidable_eq Job) aL j).

Definition pd_import_job_arrival (Job : eqType)
    (aR : prosa.behavior.job.JobArrival Job) :
    ImportedPriorityCoercion.Prosa_Behavior_Job_JobArrival
      Job (pd_decidable_eq Job) :=
  ImportedPriorityCoercion.Prosa_Behavior_Job_JobArrival_mk
    Job (pd_decidable_eq Job)
    (fun j => sub_nat_to_imported
      (@prosa.behavior.job.job_arrival Job aR j)).

Lemma pd_job_arrival_import_certificate (Job : eqType)
    (aR : prosa.behavior.job.JobArrival Job) :
  PdJobArrivalRel Job aR (pd_import_job_arrival Job aR).
Proof. intro j. exact (sub_nat_rel_canonical _). Qed.

Definition pd_export_job_arrival (Job : eqType)
    (aL : ImportedPriorityCoercion.Prosa_Behavior_Job_JobArrival
      Job (pd_decidable_eq Job)) :
    prosa.behavior.job.JobArrival Job :=
  fun j => sub_nat_to_rocq
    (ImportedPriorityCoercion.Prosa_Behavior_Job_JobArrival_job_arrival
      Job (pd_decidable_eq Job) aL j).

Lemma pd_job_arrival_export_certificate (Job : eqType)
    (aL : ImportedPriorityCoercion.Prosa_Behavior_Job_JobArrival
      Job (pd_decidable_eq Job)) :
  PdJobArrivalRel Job (pd_export_job_arrival Job aL) aL.
Proof. intro j. exact (sub_nat_rel_surjective _). Qed.

Definition pd_target_false_elim (Q : SProp)
    (H : ImportedPriorityCoercion.False) : Q :=
  match H return Q with end.

Lemma pd_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedPriorityCoercion.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  PdBoolRel b (ImportedPriorityCoercion.Decidable_decide Q d).
Proof.
  intro Hrel. unfold PdBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (pd_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (pd_target_false_elim _ (pd_false_to_imported
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Definition pd_target_le (a b : Lean.Nat) : SProp :=
  ImportedPriorityCoercion.LE_le_inst1 Lean.Nat
    ImportedPriorityCoercion.instLENat a b.

Definition pd_target_decide_le (a b : Lean.Nat) :
    ImportedPriorityCoercion.Bool :=
  ImportedPriorityCoercion.Decidable_decide (pd_target_le a b)
    (ImportedPriorityCoercion.Nat_decLe a b).

Lemma pd_decide_le_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PdBoolRel (leq aR bR) (pd_target_decide_le aL bL).
Proof.
  intros Ha Hb. apply pd_decide_bool_correspondence.
  unfold pd_target_le.
  exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma pd_bool_eq_correspondence aR aL bR bL :
  PdBoolRel aR aL -> PdBoolRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Ha) Hb).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (pd_bool_to_imported aR)
        (pd_bool_to_imported bR) :=
      sub_imported_eq_trans _ _ _ Ha
        (sub_imported_eq_trans _ _ _ Heq
          (sub_imported_eq_sym _ _ Hb)).
    have Hdecoded := f_equal pd_bool_to_rocq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (pd_bool_source_roundtrip aR) in Hdecoded.
    rewrite (pd_bool_source_roundtrip bR) in Hdecoded.
    exact Hdecoded.
Qed.

Definition PdFPRel (Task : eqType)
    (pR : prosa.model.priority.definitions.FP_policy Task)
    (pL : ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_FP_policy
      Task (pd_decidable_eq Task)) : SProp :=
  forall x y : Task,
    PdBoolRel (@prosa.model.priority.definitions.hep_task Task pR x y)
      (ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_FP_policy_hep_task
        Task (pd_decidable_eq Task) pL x y).

Definition pd_import_fp (Task : eqType)
    (pR : prosa.model.priority.definitions.FP_policy Task) :
    ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_FP_policy
      Task (pd_decidable_eq Task) :=
  ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_FP_policy_mk
    Task (pd_decidable_eq Task)
    (fun x y => pd_bool_to_imported
      (@prosa.model.priority.definitions.hep_task Task pR x y)).

Definition pd_export_fp (Task : eqType)
    (pL : ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_FP_policy
      Task (pd_decidable_eq Task)) :
    prosa.model.priority.definitions.FP_policy Task :=
  fun x y => pd_bool_to_rocq
    (ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_FP_policy_hep_task
      Task (pd_decidable_eq Task) pL x y).

Lemma pd_fp_import_certificate (Task : eqType)
    (pR : prosa.model.priority.definitions.FP_policy Task) :
  PdFPRel Task pR (pd_import_fp Task pR).
Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

Lemma pd_fp_export_certificate (Task : eqType)
    (pL : ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_FP_policy
      Task (pd_decidable_eq Task)) :
  PdFPRel Task (pd_export_fp Task pL) pL.
Proof. intros x y. exact (pd_bool_target_roundtrip _). Qed.

Definition PdJLFPRel (Job : eqType)
    (pR : prosa.model.priority.definitions.JLFP_policy Job)
    (pL : ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLFP_policy
      Job (pd_decidable_eq Job)) : SProp :=
  forall x y : Job,
    PdBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job
        Job (pd_decidable_eq Job) pL x y).

Definition pd_import_jlfp (Job : eqType)
    (pR : prosa.model.priority.definitions.JLFP_policy Job) :
    ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLFP_policy
      Job (pd_decidable_eq Job) :=
  ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLFP_policy_mk
    Job (pd_decidable_eq Job)
    (fun x y => pd_bool_to_imported
      (@prosa.model.priority.definitions.hep_job Job pR x y)).

Definition pd_export_jlfp (Job : eqType)
    (pL : ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLFP_policy
      Job (pd_decidable_eq Job)) :
    prosa.model.priority.definitions.JLFP_policy Job :=
  fun x y => pd_bool_to_rocq
    (ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job
      Job (pd_decidable_eq Job) pL x y).

Lemma pd_jlfp_import_certificate (Job : eqType)
    (pR : prosa.model.priority.definitions.JLFP_policy Job) :
  PdJLFPRel Job pR (pd_import_jlfp Job pR).
Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

Lemma pd_jlfp_export_certificate (Job : eqType)
    (pL : ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLFP_policy
      Job (pd_decidable_eq Job)) :
  PdJLFPRel Job (pd_export_jlfp Job pL) pL.
Proof. intros x y. exact (pd_bool_target_roundtrip _). Qed.

Definition PdJLDPRel (Job : eqType)
    (pR : prosa.model.priority.definitions.JLDP_policy Job)
    (pL : ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLDP_policy
      Job (pd_decidable_eq Job)) : SProp :=
  forall (t : nat) (x y : Job),
    PdBoolRel (@prosa.model.priority.definitions.hep_job_at Job pR t x y)
      (ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at
        Job (pd_decidable_eq Job) pL (sub_nat_to_imported t) x y).

Definition pd_import_jldp (Job : eqType)
    (pR : prosa.model.priority.definitions.JLDP_policy Job) :
    ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLDP_policy
      Job (pd_decidable_eq Job) :=
  ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLDP_policy_mk
    Job (pd_decidable_eq Job)
    (fun t x y => pd_bool_to_imported
      (@prosa.model.priority.definitions.hep_job_at Job pR
        (sub_nat_to_rocq t) x y)).

Definition pd_export_jldp (Job : eqType)
    (pL : ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLDP_policy
      Job (pd_decidable_eq Job)) :
    prosa.model.priority.definitions.JLDP_policy Job :=
  fun t x y => pd_bool_to_rocq
    (ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at
      Job (pd_decidable_eq Job) pL (sub_nat_to_imported t) x y).

Lemma pd_jldp_import_certificate (Job : eqType)
    (pR : prosa.model.priority.definitions.JLDP_policy Job) :
  PdJLDPRel Job pR (pd_import_jldp Job pR).
Proof.
  intros t x y. unfold PdBoolRel, pd_import_jldp.
  unfold ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at.
  cbn.
  rw sub_nat_rocq_roundtrip.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma pd_jldp_export_certificate (Job : eqType)
    (pL : ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLDP_policy
      Job (pd_decidable_eq Job)) :
  PdJLDPRel Job (pd_export_jldp Job pL) pL.
Proof. intros t x y. exact (pd_bool_target_roundtrip _). Qed.

Lemma pd_jldp_field_at (Job : eqType)
    (pR : prosa.model.priority.definitions.JLDP_policy Job)
    (pL : ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLDP_policy
      Job (pd_decidable_eq Job))
    (tR : nat) (tL : Lean.Nat) (x y : Job) :
  PdJLDPRel Job pR pL -> SubNatRel tR tL ->
  PdBoolRel (@prosa.model.priority.definitions.hep_job_at Job pR tR x y)
    (ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at
      Job (pd_decidable_eq Job) pL tL x y).
Proof.
  intros Hp Ht. unfold PdBoolRel in *.
  exact (sub_imported_eq_trans _ _ _ (Hp tR x y)
    (sub_imported_eq_congr
      (fun t => ImportedPriorityCoercion.Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at
        Job (pd_decidable_eq Job) pL t x y)
      _ _ Ht)).
Qed.

Print Assumptions pd_fp_import_certificate.
Print Assumptions pd_fp_export_certificate.
Print Assumptions pd_jlfp_import_certificate.
Print Assumptions pd_jlfp_export_certificate.
Print Assumptions pd_jldp_import_certificate.
Print Assumptions pd_jldp_export_certificate.
Print Assumptions pd_jldp_field_at.
Print Assumptions pd_bool_truth_correspondence.
Print Assumptions pd_bool_or_related.
Print Assumptions pd_bool_and_related.
Print Assumptions pd_bool_not_related.
Print Assumptions pd_job_task_import_certificate.
Print Assumptions pd_job_task_export_certificate.
Print Assumptions pd_job_arrival_import_certificate.
Print Assumptions pd_job_arrival_export_certificate.
