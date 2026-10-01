(* Copy of the accepted certificates/implementation_definitions_task/ImplTaskCorrespondence.v, re-bound to this export; only the
   imported module name differs, and the eqn_task/eqn_job statement correspondences and their target types are dropped (the Lean BoolReflect family and the
   eqn_task/eqn_job statements are not targets of this export); every kept block is unchanged. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From prosa Require Import implementation.definitions.task.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsJobConstructor ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence EacFullCorrespondence AbCorrespondence.

Module I := ImportedFactsJobConstructor.
Module T := prosa.implementation.definitions.task.

(** Correspondences for [implementation/definitions/task.v].  Concrete tasks
    and jobs are related by their fieldwise canonical import (Nat fields by
    the canonical Nat map, the arrival bound by the accepted canonical
    arrival-bound map, the job's task by the task map); every source value
    has a related compiled value and conversely.  The Boolean equalities are
    related through the source's own definitions (never through [eqn_task],
    [eqn_job] or the Lean reflection proofs); the informative reflection
    views are related by constructor-preserving maps in both directions; the
    arrival-bound definitions go through the accepted extrapolated-curve
    correspondences; the seven parameter instances are related pointwise. *)

(** ** Concrete tasks *)

Definition it_task_export (tR : T.concrete_task) : I.Prosa_Implementation_Definitions_Task_concrete_task :=
  I.Prosa_Implementation_Definitions_Task_concrete_task_mk
    (sub_nat_to_imported (T.task_id tR)) (sub_nat_to_imported (T.task_cost tR))
    (ab_export_bound (T.task_arrival tR)) (sub_nat_to_imported (T.task_deadline tR))
    (sub_nat_to_imported (T.task_priority tR)).

Definition it_task_import (tL : I.Prosa_Implementation_Definitions_Task_concrete_task) : T.concrete_task :=
  {| T.task_id := sub_nat_to_rocq (I.Prosa_Implementation_Definitions_Task_concrete_task_task_id tL);
     T.task_cost := sub_nat_to_rocq (I.Prosa_Implementation_Definitions_Task_concrete_task_task_cost tL);
     T.task_arrival := ab_import_bound (I.Prosa_Implementation_Definitions_Task_concrete_task_task_arrival tL);
     T.task_deadline := sub_nat_to_rocq (I.Prosa_Implementation_Definitions_Task_concrete_task_task_deadline tL);
     T.task_priority := sub_nat_to_rocq (I.Prosa_Implementation_Definitions_Task_concrete_task_task_priority tL) |}.

Definition ItTaskRel (tR : T.concrete_task) (tL : I.Prosa_Implementation_Definitions_Task_concrete_task) : SProp :=
  Lean.eq (it_task_export tR) tL.

Lemma it_task_source_roundtrip tR : Logic.eq (it_task_import (it_task_export tR)) tR.
Proof.
  destruct tR as [a b c d e]. unfold it_task_import, it_task_export. cbn.
  rewrite (sub_nat_rocq_roundtrip a) (sub_nat_rocq_roundtrip b) (ab_source_roundtrip c)
    (sub_nat_rocq_roundtrip d) (sub_nat_rocq_roundtrip e).
  reflexivity.
Qed.

Lemma it_task_target_roundtrip tL : ItTaskRel (it_task_import tL) tL.
Proof.
  destruct tL as [a b c d e]. unfold ItTaskRel, it_task_import, it_task_export. cbn.
  have Ha := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip a).
  have Hb := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip b).
  have Hc := imported_eq_to_coq_eq _ _ (ab_target_roundtrip c).
  have Hd := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip d).
  have He := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip e).
  unfold AbRel in Hc. rewrite Ha Hb Hc Hd He. exact (@Lean.eq_refl _ _).
Qed.

Lemma concrete_task_source_total (tR : T.concrete_task) : ItTaskRel tR (it_task_export tR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma concrete_task_target_total (tL : I.Prosa_Implementation_Definitions_Task_concrete_task) :
  ItTaskRel (it_task_import tL) tL.
Proof. exact (it_task_target_roundtrip tL). Qed.

Lemma it_task_equality xR xL yR yL :
  ItTaskRel xR xL -> ItTaskRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal it_task_import (imported_eq_to_coq_eq _ _ Hxy).
    rewrite (it_task_source_roundtrip xR) (it_task_source_roundtrip yR) in Hdecoded.
    exact Hdecoded.
Qed.

Lemma it_task_id tR tL : ItTaskRel tR tL ->
  SubNatRel (T.task_id tR) (I.Prosa_Implementation_Definitions_Task_concrete_task_task_id tL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_cost tR tL : ItTaskRel tR tL ->
  SubNatRel (T.task_cost tR) (I.Prosa_Implementation_Definitions_Task_concrete_task_task_cost tL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_arrival tR tL : ItTaskRel tR tL ->
  AbRel (T.task_arrival tR) (I.Prosa_Implementation_Definitions_Task_concrete_task_task_arrival tL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_deadline tR tL : ItTaskRel tR tL ->
  SubNatRel (T.task_deadline tR) (I.Prosa_Implementation_Definitions_Task_concrete_task_task_deadline tL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_priority tR tL : ItTaskRel tR tL ->
  SubNatRel (T.task_priority tR) (I.Prosa_Implementation_Definitions_Task_concrete_task_task_priority tL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

(** Boolean equality on the source arrival bounds is its byte-identical
    [task_arrivals_bound_eqdef]; it is related to Lean [decide (_ = _)] through
    the accepted arrival-bound equality relation. *)
Lemma it_ab_decide_related xR xL yR yL :
  AbRel xR xL -> AbRel yR yL ->
  EacBoolRel (xR == yR)
    (I.Decidable_decide (Lean.eq xL yL)
      (I.Prosa_Implementation_Definitions_ArrivalBound_instDecidableEqTask_arrivals_bound xL yL)).
Proof.
  intros Hx Hy. apply eac_decide_bool_correspondence.
  have Heq := ab_equality_correspondence xR xL yR yL Hx Hy.
  have Hsrc := ab_source_eqdef_iff xR yR.
  apply prop_sprop_rel_intro.
  - intro H. apply (prop_to_sprop _ _ Heq). exact (proj1 Hsrc H).
  - intro H. apply strictly_inhabits. apply (proj2 Hsrc). exact (sprop_to_prop _ _ Heq H).
Qed.

Lemma it_nat_decide_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  EacBoolRel (aR == bR) (I.Decidable_decide (Lean.eq aL bL) (I.instDecidableEqNat aL bL)).
Proof. exact (eac_nat_eq_bool_correspondence aR aL bR bL). Qed.

Theorem task_eqdef_correspondence xR xL yR yL :
  ItTaskRel xR xL -> ItTaskRel yR yL ->
  EacBoolRel (T.task_eqdef xR yR) (I.Prosa_Implementation_Definitions_Task_task_eqdef xL yL).
Proof.
  intros Hx Hy. unfold T.task_eqdef. cbn [I.Prosa_Implementation_Definitions_Task_task_eqdef].
  refine (eac_bool_and_correspondence _ _ _ _ _ (it_nat_decide_related _ _ _ _ (it_task_priority _ _ Hx) (it_task_priority _ _ Hy))).
  refine (eac_bool_and_correspondence _ _ _ _ _ (it_nat_decide_related _ _ _ _ (it_task_deadline _ _ Hx) (it_task_deadline _ _ Hy))).
  refine (eac_bool_and_correspondence _ _ _ _ _ (it_ab_decide_related _ _ _ _ (it_task_arrival _ _ Hx) (it_task_arrival _ _ Hy))).
  exact (eac_bool_and_correspondence _ _ _ _
    (it_nat_decide_related _ _ _ _ (it_task_id _ _ Hx) (it_task_id _ _ Hy))
    (it_nat_decide_related _ _ _ _ (it_task_cost _ _ Hx) (it_task_cost _ _ Hy))).
Qed.

(** The source Boolean task equality decides equality; proved from its
    definition and the accepted arrival-bound fact, not from [eqn_task]. *)
Lemma it_task_eqdef_iff (x y : T.concrete_task) : is_true (T.task_eqdef x y) <-> Logic.eq x y.
Proof.
  destruct x as [a b c d e]; destruct y as [a' b' c' d' e']. unfold T.task_eqdef. cbn. split.
  - move/andP=> [/andP [/andP [/andP [/eqP Ha /eqP Hb] Hc] /eqP Hd] /eqP He].
    have Hc' := proj1 (ab_source_eqdef_iff c c') Hc. subst. reflexivity.
  - intro H. injection H => He Hd Hc Hb Ha. subst.
    have Hc : is_true (c' == c') := proj2 (ab_source_eqdef_iff c' c') (Logic.eq_refl c').
    repeat (apply/andP; split).
    all: first [exact Hc | exact (eqnn _) | exact (eqxx _)].
Qed.

Definition src_eqn_task : Type := ltac:(let T := type of (@T.eqn_task) in exact T).
Definition it_job_export (jR : T.concrete_job) : I.Prosa_Implementation_Definitions_Task_concrete_job :=
  I.Prosa_Implementation_Definitions_Task_concrete_job_mk
    (sub_nat_to_imported (T.job_id jR)) (sub_nat_to_imported (T.job_arrival jR))
    (sub_nat_to_imported (T.job_cost jR)) (sub_nat_to_imported (T.job_deadline jR))
    (it_task_export (T.job_task jR)).

Definition it_job_import (jL : I.Prosa_Implementation_Definitions_Task_concrete_job) : T.concrete_job :=
  {| T.job_id := sub_nat_to_rocq (I.Prosa_Implementation_Definitions_Task_concrete_job_job_id jL);
     T.job_arrival := sub_nat_to_rocq (I.Prosa_Implementation_Definitions_Task_concrete_job_job_arrival jL);
     T.job_cost := sub_nat_to_rocq (I.Prosa_Implementation_Definitions_Task_concrete_job_job_cost jL);
     T.job_deadline := sub_nat_to_rocq (I.Prosa_Implementation_Definitions_Task_concrete_job_job_deadline jL);
     T.job_task := it_task_import (I.Prosa_Implementation_Definitions_Task_concrete_job_job_task jL) |}.

Definition ItJobRel (jR : T.concrete_job) (jL : I.Prosa_Implementation_Definitions_Task_concrete_job) : SProp :=
  Lean.eq (it_job_export jR) jL.

Lemma it_job_source_roundtrip jR : Logic.eq (it_job_import (it_job_export jR)) jR.
Proof.
  destruct jR as [a b c d e]. unfold it_job_import, it_job_export. cbn.
  rewrite (sub_nat_rocq_roundtrip a) (sub_nat_rocq_roundtrip b) (sub_nat_rocq_roundtrip c)
    (sub_nat_rocq_roundtrip d) (it_task_source_roundtrip e).
  reflexivity.
Qed.

Lemma it_job_target_roundtrip jL : ItJobRel (it_job_import jL) jL.
Proof.
  destruct jL as [a b c d e]. unfold ItJobRel, it_job_import, it_job_export. cbn.
  have Ha := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip a).
  have Hb := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip b).
  have Hc := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip c).
  have Hd := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip d).
  have He := imported_eq_to_coq_eq _ _ (it_task_target_roundtrip e).
  rewrite Ha Hb Hc Hd He. exact (@Lean.eq_refl _ _).
Qed.

Lemma concrete_job_source_total (jR : T.concrete_job) : ItJobRel jR (it_job_export jR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma concrete_job_target_total (jL : I.Prosa_Implementation_Definitions_Task_concrete_job) :
  ItJobRel (it_job_import jL) jL.
Proof. exact (it_job_target_roundtrip jL). Qed.

Lemma it_job_equality xR xL yR yL :
  ItJobRel xR xL -> ItJobRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal it_job_import (imported_eq_to_coq_eq _ _ Hxy).
    rewrite (it_job_source_roundtrip xR) (it_job_source_roundtrip yR) in Hdecoded.
    exact Hdecoded.
Qed.

Lemma it_job_id jR jL : ItJobRel jR jL ->
  SubNatRel (T.job_id jR) (I.Prosa_Implementation_Definitions_Task_concrete_job_job_id jL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_job_arrival jR jL : ItJobRel jR jL ->
  SubNatRel (T.job_arrival jR) (I.Prosa_Implementation_Definitions_Task_concrete_job_job_arrival jL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_job_cost jR jL : ItJobRel jR jL ->
  SubNatRel (T.job_cost jR) (I.Prosa_Implementation_Definitions_Task_concrete_job_job_cost jL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_job_deadline jR jL : ItJobRel jR jL ->
  SubNatRel (T.job_deadline jR) (I.Prosa_Implementation_Definitions_Task_concrete_job_job_deadline jL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_job_task jR jL : ItJobRel jR jL ->
  ItTaskRel (T.job_task jR) (I.Prosa_Implementation_Definitions_Task_concrete_job_job_task jL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

(** Boolean equality on the source concrete tasks is [task_eqdef]. *)
Lemma it_task_decide_related xR xL yR yL :
  ItTaskRel xR xL -> ItTaskRel yR yL ->
  EacBoolRel (xR == yR)
    (I.Decidable_decide (Lean.eq xL yL)
      (I.Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task xL yL)).
Proof.
  intros Hx Hy. apply eac_decide_bool_correspondence.
  have Heq := it_task_equality xR xL yR yL Hx Hy.
  have Hsrc := it_task_eqdef_iff xR yR.
  apply prop_sprop_rel_intro.
  - intro H. apply (prop_to_sprop _ _ Heq). exact (proj1 Hsrc H).
  - intro H. apply strictly_inhabits. apply (proj2 Hsrc). exact (sprop_to_prop _ _ Heq H).
Qed.

Theorem job_eqdef_correspondence xR xL yR yL :
  ItJobRel xR xL -> ItJobRel yR yL ->
  EacBoolRel (T.job_eqdef xR yR) (I.Prosa_Implementation_Definitions_Task_job_eqdef xL yL).
Proof.
  intros Hx Hy. unfold T.job_eqdef. cbn [I.Prosa_Implementation_Definitions_Task_job_eqdef].
  refine (eac_bool_and_correspondence _ _ _ _ _ (it_task_decide_related _ _ _ _ (it_job_task _ _ Hx) (it_job_task _ _ Hy))).
  refine (eac_bool_and_correspondence _ _ _ _ _ (it_nat_decide_related _ _ _ _ (it_job_deadline _ _ Hx) (it_job_deadline _ _ Hy))).
  refine (eac_bool_and_correspondence _ _ _ _ _ (it_nat_decide_related _ _ _ _ (it_job_cost _ _ Hx) (it_job_cost _ _ Hy))).
  exact (eac_bool_and_correspondence _ _ _ _
    (it_nat_decide_related _ _ _ _ (it_job_id _ _ Hx) (it_job_id _ _ Hy))
    (it_nat_decide_related _ _ _ _ (it_job_arrival _ _ Hx) (it_job_arrival _ _ Hy))).
Qed.

Lemma it_job_eqdef_iff (x y : T.concrete_job) : is_true (T.job_eqdef x y) <-> Logic.eq x y.
Proof.
  destruct x as [a b c d e]; destruct y as [a' b' c' d' e']. unfold T.job_eqdef. cbn. split.
  - move/andP=> [/andP [/andP [/andP [/eqP Ha /eqP Hb] /eqP Hc] /eqP Hd] He].
    have He' := proj1 (it_task_eqdef_iff e e') He. subst. reflexivity.
  - intro H. injection H => He Hd Hc Hb Ha. subst.
    have He : is_true (e' == e') := proj2 (it_task_eqdef_iff e' e') (Logic.eq_refl e').
    repeat (apply/andP; split).
    all: first [exact He | exact (eqnn _) | exact (eqxx _)].
Qed.

Definition src_eqn_job : Type := ltac:(let T := type of (@T.eqn_job) in exact T).
Theorem get_arrival_curve_prefix_correspondence tR tL :
  ItTaskRel tR tL ->
  EacPrefixRel (T.get_arrival_curve_prefix tR)
    (I.Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix tL).
Proof.
  intro H. destruct H. destruct tR as [a b c d e]. destruct c as [p|p|s];
    unfold T.get_arrival_curve_prefix; cbn.
  - exact (eac_inter_arrival_to_prefix_correspondence p _ (sub_nat_rel_canonical p)).
  - exact (eac_inter_arrival_to_prefix_correspondence p _ (sub_nat_rel_canonical p)).
  - exact (@Lean.eq_refl _ _).
Qed.

Theorem concrete_max_arrivals_correspondence tR tL dR dL :
  ItTaskRel tR tL -> SubNatRel dR dL ->
  SubNatRel (T.concrete_max_arrivals tR dR)
    (I.Prosa_Implementation_Definitions_Task_concrete_max_arrivals tL dL).
Proof.
  intros Ht Hd. unfold T.concrete_max_arrivals.
  cbn [I.Prosa_Implementation_Definitions_Task_concrete_max_arrivals].
  exact (eac_extrapolated_arrival_curve_correspondence _ _ _ _
    (get_arrival_curve_prefix_correspondence tR tL Ht) Hd).
Qed.

(** ** Task and job parameter instances *)

(** The compiled instances inhabit the classes at the universe instance of the
    concrete types (the importer's [_instN] copies); their single field is read
    by matching on the class constructor. *)
Definition it_cT := I.Prosa_Implementation_Definitions_Task_concrete_task.
Definition it_dT := I.Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task.
Definition it_cJ := I.Prosa_Implementation_Definitions_Task_concrete_job.
Definition it_dJ := I.Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job.

Definition it_task_cost_field (c : I.Prosa_Model_Task_Concept_TaskCost_inst1 it_cT it_dT) (t : it_cT) :=
  match c with I.Prosa_Model_Task_Concept_TaskCost_mk_inst1 f => f t end.
Definition it_task_priority_field
    (c : I.Prosa_Model_Priority_NumericFixedPriority_TaskPriority_inst1 it_cT it_dT) (t : it_cT) :=
  match c with I.Prosa_Model_Priority_NumericFixedPriority_TaskPriority_mk_inst1 f => f t end.
Definition it_task_deadline_field (c : I.Prosa_Model_Task_Concept_TaskDeadline_inst1 it_cT it_dT) (t : it_cT) :=
  match c with I.Prosa_Model_Task_Concept_TaskDeadline_mk_inst1 f => f t end.
Definition it_max_arrivals_field (c : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_inst1 it_cT it_dT)
    (t : it_cT) (d : Lean.Nat) :=
  match c with I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_mk_inst1 f => f t d end.
Definition it_job_task_field (c : I.Prosa_Model_Task_Concept_JobTask_inst3 it_cJ it_dJ it_cT it_dT) (j : it_cJ) :=
  match c with I.Prosa_Model_Task_Concept_JobTask_mk_inst3 f => f j end.
Definition it_job_arrival_field (c : I.Prosa_Behavior_Job_JobArrival_inst1 it_cJ it_dJ) (j : it_cJ) :=
  match c with I.Prosa_Behavior_Job_JobArrival_mk_inst1 f => f j end.
Definition it_job_cost_field (c : I.Prosa_Behavior_Job_JobCost_inst1 it_cJ it_dJ) (j : it_cJ) :=
  match c with I.Prosa_Behavior_Job_JobCost_mk_inst1 f => f j end.

Theorem TaskCost_correspondence tR tL :
  ItTaskRel tR tL ->
  SubNatRel (@prosa.model.task.concept.task_cost _ T.TaskCost tR)
    (it_task_cost_field I.Prosa_Implementation_Definitions_Task_TaskCost tL).
Proof. exact (it_task_cost tR tL). Qed.

Theorem TaskPriority_correspondence tR tL :
  ItTaskRel tR tL ->
  SubNatRel (@prosa.model.priority.numeric_fixed_priority.task_priority _ T.TaskPriority tR)
    (it_task_priority_field I.Prosa_Implementation_Definitions_Task_TaskPriority tL).
Proof. exact (it_task_priority tR tL). Qed.

Theorem TaskDeadline_correspondence tR tL :
  ItTaskRel tR tL ->
  SubNatRel (@prosa.model.task.concept.task_deadline _ T.TaskDeadline tR)
    (it_task_deadline_field I.Prosa_Implementation_Definitions_Task_TaskDeadline tL).
Proof. exact (it_task_deadline tR tL). Qed.

Theorem ConcreteMaxArrivals_correspondence tR tL dR dL :
  ItTaskRel tR tL -> SubNatRel dR dL ->
  SubNatRel (@prosa.model.task.arrival.curves.max_arrivals _ T.ConcreteMaxArrivals tR dR)
    (it_max_arrivals_field I.Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals tL dL).
Proof. exact (concrete_max_arrivals_correspondence tR tL dR dL). Qed.

Theorem JobTask_correspondence jR jL :
  ItJobRel jR jL ->
  ItTaskRel (@prosa.model.task.concept.job_task _ _ T.JobTask jR)
    (it_job_task_field I.Prosa_Implementation_Definitions_Task_JobTask jL).
Proof. exact (it_job_task jR jL). Qed.

Theorem JobArrival_correspondence jR jL :
  ItJobRel jR jL ->
  SubNatRel (@prosa.behavior.job.job_arrival _ T.JobArrival jR)
    (it_job_arrival_field I.Prosa_Implementation_Definitions_Task_JobArrival jL).
Proof. exact (it_job_arrival jR jL). Qed.

Theorem JobCost_correspondence jR jL :
  ItJobRel jR jL ->
  SubNatRel (@prosa.behavior.job.job_cost _ T.JobCost jR)
    (it_job_cost_field I.Prosa_Implementation_Definitions_Task_JobCost jL).
Proof. exact (it_job_cost jR jL). Qed.
