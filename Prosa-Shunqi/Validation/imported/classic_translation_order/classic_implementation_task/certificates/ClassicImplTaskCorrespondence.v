From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From prosa Require Import util.seqset classic.implementation.task.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicImplTask.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicImplTaskBase ClassicImplTaskList1.

Module I := ImportedClassicImplTask.
Module T := prosa.classic.implementation.task.ConcreteTask.
Import (canonicals) T.
Local Open Scope nat_scope.

(** Certificates for [classic/implementation/task.v] (ProsaBuddy classic, commit f692cb7).

    Concrete tasks are related by their fieldwise canonical import (every field a
    natural number, by the canonical Nat map); every source value has a related
    compiled value and conversely (two-way totals).  [task_eqdef] is related
    through the source's own definition (never through [eqn_task] or the Lean
    reflection proof); the informative reflection [eqn_task] is related by
    constructor-preserving maps in both directions; [concrete_taskset] (sets of
    concrete tasks) is related by the elementwise image of the underlying
    sequence, with two-way totals.  The HB registration of [hasDecEq] (the
    generated factory and canonical structure) is the Lean derived
    [DecidableEq] instance, related below through [task_eqdef]. *)

Definition it_export (tR : T.concrete_task) : I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task :=
  I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task_mk
    (sub_nat_to_imported (T.task_id tR)) (sub_nat_to_imported (T.task_cost tR))
    (sub_nat_to_imported (T.task_period tR)) (sub_nat_to_imported (T.task_deadline tR)).

Definition it_import (tL : I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task) : T.concrete_task :=
  {| T.task_id := sub_nat_to_rocq (I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task_task_id tL);
     T.task_cost := sub_nat_to_rocq (I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task_task_cost tL);
     T.task_period := sub_nat_to_rocq (I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task_task_period tL);
     T.task_deadline := sub_nat_to_rocq (I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task_task_deadline tL) |}.

Definition ItRel (tR : T.concrete_task) (tL : I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task) : SProp :=
  Lean.eq (it_export tR) tL.

Lemma it_source_roundtrip tR : Logic.eq (it_import (it_export tR)) tR.
Proof.
  destruct tR as [a b c d]. unfold it_import, it_export. cbn.
  rewrite (sub_nat_rocq_roundtrip a) (sub_nat_rocq_roundtrip b) (sub_nat_rocq_roundtrip c) (sub_nat_rocq_roundtrip d).
  reflexivity.
Qed.

Lemma it_target_roundtrip tL : Logic.eq (it_export (it_import tL)) tL.
Proof.
  destruct tL as [a b c d]. unfold it_import, it_export. cbn.
  have Ha := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip a).
  have Hb := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip b).
  have Hc := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip c).
  have Hd := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip d).
  rewrite Ha Hb Hc Hd. reflexivity.
Qed.

Theorem ConcreteTask_concrete_task_source_total (tR : T.concrete_task) : ItRel tR (it_export tR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteTask_concrete_task_target_total (tL : I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task) :
  ItRel (it_import tL) tL.
Proof. exact (coq_eq_to_imported_eq _ _ (it_target_roundtrip tL)). Qed.

Lemma it_equality xR xL yR yL : ItRel xR xL -> ItRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal it_import (imported_eq_to_coq_eq _ _ Hxy).
    by rewrite !it_source_roundtrip in Hdecoded.
Qed.

Lemma it_task_id tR tL : ItRel tR tL ->
  SubNatRel (T.task_id tR) (I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task_task_id tL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_cost tR tL : ItRel tR tL ->
  SubNatRel (T.task_cost tR) (I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task_task_cost tL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_period tR tL : ItRel tR tL ->
  SubNatRel (T.task_period tR) (I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task_task_period tL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_deadline tR tL : ItRel tR tL ->
  SubNatRel (T.task_deadline tR) (I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task_task_deadline tL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

(* ------------------------------------------------------------------ *)
(** * Boolean equality and its reflection *)

Theorem ConcreteTask_task_eqdef_correspondence xR xL yR yL : ItRel xR xL -> ItRel yR yL ->
  CtBoolRel (T.task_eqdef xR yR) (I.Prosa_Classic_Implementation_Task_ConcreteTask_task_eqdef xL yL).
Proof.
  intros Hx Hy. unfold T.task_eqdef. cbn [I.Prosa_Classic_Implementation_Task_ConcreteTask_task_eqdef].
  refine (ct_bool_and _ _ _ _ _ (ct_decide_eq_nat _ _ _ _ (it_task_deadline _ _ Hx) (it_task_deadline _ _ Hy))).
  refine (ct_bool_and _ _ _ _ _ (ct_decide_eq_nat _ _ _ _ (it_task_period _ _ Hx) (it_task_period _ _ Hy))).
  exact (ct_bool_and _ _ _ _ (ct_decide_eq_nat _ _ _ _ (it_task_id _ _ Hx) (it_task_id _ _ Hy))
           (ct_decide_eq_nat _ _ _ _ (it_task_cost _ _ Hx) (it_task_cost _ _ Hy))).
Qed.

Definition it_reflect_forward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    reflect PR bR -> I.Prosa_Classic_Util_List_BoolReflect PL bL.
Proof.
  destruct Hb. intro HR. destruct HR as [Htrue | Hfalse].
  - exact (I.Prosa_Classic_Util_List_BoolReflect_isTrue PL (prop_to_sprop _ _ HP Htrue)).
  - exact (I.Prosa_Classic_Util_List_BoolReflect_isFalse PL
      (fun HL => ct_coq_false_to_target (Hfalse (sprop_to_prop _ _ HP HL)))).
Defined.

Definition it_reflect_backward_at_bool (PR : Prop) (PL : SProp) (HP : PropSPropRel PR PL) (bL : I.Bool) :
    I.Prosa_Classic_Util_List_BoolReflect PL bL -> reflect PR (ct_l2b bL) :=
  fun HL =>
    match HL in I.Prosa_Classic_Util_List_BoolReflect _ b return reflect PR (ct_l2b b) with
    | I.Prosa_Classic_Util_List_BoolReflect_isTrue Htrue => ReflectT PR (sprop_to_prop _ _ HP Htrue)
    | I.Prosa_Classic_Util_List_BoolReflect_isFalse Hfalse =>
        ReflectF PR (fun HR => interpret_strict Logic.False
          (ct_target_false_to_strict (Hfalse (prop_to_sprop _ _ HP HR))))
    end.

Definition it_reflect_backward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    I.Prosa_Classic_Util_List_BoolReflect PL bL -> reflect PR bR.
Proof. destruct Hb. destruct bR; cbn; exact (it_reflect_backward_at_bool PR PL HP _). Defined.

Definition src_eqn_task : Type := ltac:(let X := type of (@T.eqn_task) in exact X).
Definition tgt_eqn_task : Type := ltac:(let X := type of (@I.Prosa_Classic_Implementation_Task_ConcreteTask_eqn_task) in exact X).

Theorem ConcreteTask_eqn_task_correspondence :
  Datatypes.prod (src_eqn_task -> tgt_eqn_task) (tgt_eqn_task -> src_eqn_task).
Proof.
  split.
  - intros f xL yL.
    have Hx := ConcreteTask_concrete_task_target_total xL. have Hy := ConcreteTask_concrete_task_target_total yL.
    exact (it_reflect_forward _ _ _ _ (it_equality _ _ _ _ Hx Hy)
      (ConcreteTask_task_eqdef_correspondence _ _ _ _ Hx Hy) (f (it_import xL) (it_import yL))).
  - intros g xR yR.
    have Hx := ConcreteTask_concrete_task_source_total xR. have Hy := ConcreteTask_concrete_task_source_total yR.
    exact (it_reflect_backward _ _ _ _ (it_equality _ _ _ _ Hx Hy)
      (ConcreteTask_task_eqdef_correspondence _ _ _ _ Hx Hy) (g (it_export xR) (it_export yR))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Task sets *)

Lemma it_uniq_rel (s : seq T.concrete_task) :
  PropSPropRel (uniq s) (I.List_Nodup_inst1 I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task (cl1_map it_export s)).
Proof. exact (cl1_uniq_rel _ _ it_export it_import it_source_roundtrip it_target_roundtrip s). Qed.

Definition its_list (sL : I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_taskset) :
    I.List_inst1 I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task :=
  match sL with I.Prosa_Util_Seqset_set_mk_inst1 xs _ => xs end.

Definition ItsRel (sR : T.concrete_taskset) (sL : I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_taskset) : SProp :=
  Lean.eq (cl1_map it_export (@_set_seq T.concrete_task sR)) (its_list sL).

Definition its_export (sR : T.concrete_taskset) : I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_taskset :=
  match sR with
  | @Build_set _ xs Hu =>
      I.Prosa_Util_Seqset_set_mk_inst1 _ _ (cl1_map it_export xs) (prop_to_sprop _ _ (it_uniq_rel xs) Hu)
  end.

Lemma its_import_uniq (xs : I.List_inst1 I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task)
    (Hn : I.List_Nodup_inst1 _ xs) : uniq (cl1_unmap it_import xs).
Proof.
  apply (sprop_to_prop _ _ (it_uniq_rel (cl1_unmap it_import xs))).
  rewrite (cl1_map_unmap it_export it_import it_target_roundtrip xs). exact Hn.
Qed.

Definition its_import (sL : I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_taskset) : T.concrete_taskset :=
  match sL with
  | I.Prosa_Util_Seqset_set_mk_inst1 xs Hn => @Build_set T.concrete_task (cl1_unmap it_import xs) (its_import_uniq xs Hn)
  end.

Theorem ConcreteTask_concrete_taskset_source_total (sR : T.concrete_taskset) : ItsRel sR (its_export sR).
Proof. destruct sR. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteTask_concrete_taskset_target_total (sL : I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_taskset) :
  ItsRel (its_import sL) sL.
Proof.
  destruct sL as [xs Hn]. unfold ItsRel, its_import, its_list. cbn.
  exact (coq_eq_to_imported_eq _ _ (cl1_map_unmap it_export it_import it_target_roundtrip xs)).
Qed.
