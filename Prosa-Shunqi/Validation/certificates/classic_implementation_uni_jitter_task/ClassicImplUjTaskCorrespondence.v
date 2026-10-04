From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From prosa Require Import util.seqset classic.implementation.uni.jitter.task.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicImplUjTask.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicImplUjTaskBase ClassicImplUjTaskList1.

Module I := ImportedClassicImplUjTask.
Module TT := prosa.classic.implementation.uni.jitter.task.ConcreteTask.
Import (canonicals) TT.
Local Open Scope nat_scope.

(** Certificates for [classic/implementation/uni/jitter/task.v] (ProsaBuddy classic, commit f692cb7).

    Concrete tasks are related by their fieldwise canonical import (every field a natural number, by the canonical
    Nat map); every source value has a related compiled value and conversely (two-way totals).  [task_eqdef] is related
    through the source's own definition (never through [eqn_task] or the Lean reflection proof); the informative
    reflection [eqn_task] is related by constructor-preserving maps in both directions; [concrete_taskset] (sets of concrete
    tasks) is related by the elementwise image of the underlying sequence, with two-way totals.  The HB registration of [hasDecEq] is the Lean derived [DecidableEq] instance. *)

(** Informative reflections: constructor-preserving maps in both directions, given the
    relation of the propositions and of the Booleans. *)
Definition cr_reflect_forward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    reflect PR bR -> I.Prosa_Classic_Util_List_BoolReflect PL bL.
Proof.
  destruct Hb. intro HR. destruct HR as [Htrue | Hfalse].
  - exact (I.Prosa_Classic_Util_List_BoolReflect_isTrue PL (prop_to_sprop _ _ HP Htrue)).
  - exact (I.Prosa_Classic_Util_List_BoolReflect_isFalse PL
      (fun HL => ct_coq_false_to_target (Hfalse (sprop_to_prop _ _ HP HL)))).
Defined.

Definition cr_reflect_backward_at_bool (PR : Prop) (PL : SProp) (HP : PropSPropRel PR PL) (bL : I.Bool) :
    I.Prosa_Classic_Util_List_BoolReflect PL bL -> reflect PR (ct_l2b bL) :=
  fun HL =>
    match HL in I.Prosa_Classic_Util_List_BoolReflect _ b return reflect PR (ct_l2b b) with
    | I.Prosa_Classic_Util_List_BoolReflect_isTrue Htrue => ReflectT PR (sprop_to_prop _ _ HP Htrue)
    | I.Prosa_Classic_Util_List_BoolReflect_isFalse Hfalse =>
        ReflectF PR (fun HR => interpret_strict Logic.False
          (ct_target_false_to_strict (Hfalse (prop_to_sprop _ _ HP HR))))
    end.

Definition cr_reflect_backward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    I.Prosa_Classic_Util_List_BoolReflect PL bL -> reflect PR bR.
Proof. destruct Hb. destruct bR; cbn; exact (cr_reflect_backward_at_bool PR PL HP _). Defined.

(* ------------------------------------------------------------------ *)
(** * Concrete tasks *)

Definition it_export (r : TT.concrete_task) : I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task :=
  I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task_mk
    (sub_nat_to_imported (TT.task_id r)) (sub_nat_to_imported (TT.task_cost r)) (sub_nat_to_imported (TT.task_period r)) (sub_nat_to_imported (TT.task_deadline r)) (sub_nat_to_imported (TT.task_jitter r)).

Definition it_import (l : I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task) : TT.concrete_task :=
  {| TT.task_id := sub_nat_to_rocq (I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task_task_id l);
     TT.task_cost := sub_nat_to_rocq (I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task_task_cost l);
     TT.task_period := sub_nat_to_rocq (I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task_task_period l);
     TT.task_deadline := sub_nat_to_rocq (I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task_task_deadline l);
     TT.task_jitter := sub_nat_to_rocq (I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task_task_jitter l) |}.

Definition ItRel (r : TT.concrete_task) (l : I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task) : SProp := Lean.eq (it_export r) l.

Lemma it_source_roundtrip r : Logic.eq (it_import (it_export r)) r.
Proof.
  destruct r as [v0 v1 v2 v3 v4]. unfold it_import, it_export. cbn.
  rewrite (sub_nat_rocq_roundtrip v0) (sub_nat_rocq_roundtrip v1) (sub_nat_rocq_roundtrip v2) (sub_nat_rocq_roundtrip v3) (sub_nat_rocq_roundtrip v4).
  reflexivity.
Qed.

Lemma it_target_roundtrip l : Logic.eq (it_export (it_import l)) l.
Proof.
  destruct l as [v0 v1 v2 v3 v4]. unfold it_import, it_export. cbn.
  have Hv0 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v0).
  have Hv1 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v1).
  have Hv2 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v2).
  have Hv3 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v3).
  have Hv4 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v4).
  rewrite Hv0 Hv1 Hv2 Hv3 Hv4. reflexivity.
Qed.

Theorem ConcreteTask_concrete_task_source_total (r : TT.concrete_task) : ItRel r (it_export r).
Proof. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteTask_concrete_task_target_total (l : I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task) : ItRel (it_import l) l.
Proof. exact (coq_eq_to_imported_eq _ _ (it_target_roundtrip l)). Qed.

Lemma it_equality xR xL yR yL : ItRel xR xL -> ItRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal it_import (imported_eq_to_coq_eq _ _ Hxy).
    by rewrite !it_source_roundtrip in Hdecoded.
Qed.

Lemma it_task_id r l : ItRel r l -> SubNatRel (TT.task_id r) (I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task_task_id l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_cost r l : ItRel r l -> SubNatRel (TT.task_cost r) (I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task_task_cost l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_period r l : ItRel r l -> SubNatRel (TT.task_period r) (I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task_task_period l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_deadline r l : ItRel r l -> SubNatRel (TT.task_deadline r) (I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task_task_deadline l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_jitter r l : ItRel r l -> SubNatRel (TT.task_jitter r) (I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task_task_jitter l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteTask_task_eqdef_correspondence xR xL yR yL : ItRel xR xL -> ItRel yR yL ->
  CtBoolRel (TT.task_eqdef xR yR) (I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_task_eqdef xL yL).
Proof.
  intros Hx Hy. unfold TT.task_eqdef. cbn [I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_task_eqdef].
  exact (ct_bool_and _ _ _ _
    (ct_bool_and _ _ _ _
    (ct_bool_and _ _ _ _
    (ct_bool_and _ _ _ _
    (ct_decide_eq_nat _ _ _ _ (it_task_id _ _ Hx) (it_task_id _ _ Hy))
    (ct_decide_eq_nat _ _ _ _ (it_task_cost _ _ Hx) (it_task_cost _ _ Hy)))
    (ct_decide_eq_nat _ _ _ _ (it_task_period _ _ Hx) (it_task_period _ _ Hy)))
    (ct_decide_eq_nat _ _ _ _ (it_task_deadline _ _ Hx) (it_task_deadline _ _ Hy)))
    (ct_decide_eq_nat _ _ _ _ (it_task_jitter _ _ Hx) (it_task_jitter _ _ Hy))).
Qed.

Definition src_eqn_task : Type := ltac:(let X := type of (@TT.eqn_task) in exact X).
Definition tgt_eqn_task : Type := ltac:(let X := type of (@I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_eqn_task) in exact X).

Theorem ConcreteTask_eqn_task_correspondence :
  Datatypes.prod (src_eqn_task -> tgt_eqn_task) (tgt_eqn_task -> src_eqn_task).
Proof.
  split.
  - intros f xL yL.
    have Hx := ConcreteTask_concrete_task_target_total xL. have Hy := ConcreteTask_concrete_task_target_total yL.
    exact (cr_reflect_forward _ _ _ _ (it_equality _ _ _ _ Hx Hy)
      (ConcreteTask_task_eqdef_correspondence _ _ _ _ Hx Hy) (f (it_import xL) (it_import yL))).
  - intros g xR yR.
    have Hx := ConcreteTask_concrete_task_source_total xR. have Hy := ConcreteTask_concrete_task_source_total yR.
    exact (cr_reflect_backward _ _ _ _ (it_equality _ _ _ _ Hx Hy)
      (ConcreteTask_task_eqdef_correspondence _ _ _ _ Hx Hy) (g (it_export xR) (it_export yR))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Task sets *)

Lemma it_uniq_rel (s : seq TT.concrete_task) :
  PropSPropRel (uniq s) (I.List_Nodup_inst1 I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task (cl1_map it_export s)).
Proof. exact (cl1_uniq_rel _ _ it_export it_import it_source_roundtrip it_target_roundtrip s). Qed.

Definition its_list (sL : I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_taskset) : I.List_inst1 I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task :=
  match sL with I.Prosa_Util_Seqset_set_mk_inst1 xs _ => xs end.

Definition ItsRel (sR : TT.concrete_taskset) (sL : I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_taskset) : SProp :=
  Lean.eq (cl1_map it_export (@_set_seq TT.concrete_task sR)) (its_list sL).

Definition its_export (sR : TT.concrete_taskset) : I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_taskset :=
  match sR with
  | @Build_set _ xs Hu =>
      I.Prosa_Util_Seqset_set_mk_inst1 _ _ (cl1_map it_export xs) (prop_to_sprop _ _ (it_uniq_rel xs) Hu)
  end.

Lemma its_import_uniq (xs : I.List_inst1 I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task)
    (Hn : I.List_Nodup_inst1 _ xs) : uniq (cl1_unmap it_import xs).
Proof.
  apply (sprop_to_prop _ _ (it_uniq_rel (cl1_unmap it_import xs))).
  rewrite (cl1_map_unmap it_export it_import it_target_roundtrip xs). exact Hn.
Qed.

Definition its_import (sL : I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_taskset) : TT.concrete_taskset :=
  match sL with
  | I.Prosa_Util_Seqset_set_mk_inst1 xs Hn => @Build_set TT.concrete_task (cl1_unmap it_import xs) (its_import_uniq xs Hn)
  end.

Theorem ConcreteTask_concrete_taskset_source_total (sR : TT.concrete_taskset) : ItsRel sR (its_export sR).
Proof. destruct sR. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteTask_concrete_taskset_target_total (sL : I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_taskset) :
  ItsRel (its_import sL) sL.
Proof.
  destruct sL as [xs Hn]. unfold ItsRel, its_import, its_list. cbn.
  exact (coq_eq_to_imported_eq _ _ (cl1_map_unmap it_export it_import it_target_roundtrip xs)).
Qed.

