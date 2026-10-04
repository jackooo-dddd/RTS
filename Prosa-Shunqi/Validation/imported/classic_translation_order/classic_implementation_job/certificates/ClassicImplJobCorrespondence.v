From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From prosa Require Import classic.implementation.task classic.implementation.job.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicImplJob.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicImplJobBase.

Module I := ImportedClassicImplJob.
Module TT := prosa.classic.implementation.task.ConcreteTask.
Import (canonicals) TT.
Module TJ := prosa.classic.implementation.job.ConcreteJob.
Import (canonicals) TJ.
Local Open Scope nat_scope.

(** Certificates for [classic/implementation/job.v] (ProsaBuddy classic, commit f692cb7).

    Concrete jobs are related by their fieldwise canonical import (Nat fields by the canonical Nat map, the job's
    task by the concrete-task relation, re-bound below to this export); every source value has a related compiled value
    and conversely (two-way totals).  [job_eqdef] is related through the source's own definition (never through
    [eqn_job] or the Lean reflection proof); the informative reflection [eqn_job] is related by constructor-preserving
    maps in both directions.  The HB registration of [hasDecEq] is the Lean derived [DecidableEq] instance. *)

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

Definition it_export (r : TT.concrete_task) : I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task :=
  I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task_mk
    (sub_nat_to_imported (TT.task_id r)) (sub_nat_to_imported (TT.task_cost r)) (sub_nat_to_imported (TT.task_period r)) (sub_nat_to_imported (TT.task_deadline r)).

Definition it_import (l : I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task) : TT.concrete_task :=
  match l with I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task_mk p0 p1 p2 p3 =>
  {| TT.task_id := sub_nat_to_rocq p0;
     TT.task_cost := sub_nat_to_rocq p1;
     TT.task_period := sub_nat_to_rocq p2;
     TT.task_deadline := sub_nat_to_rocq p3 |} end.

Definition ItRel (r : TT.concrete_task) (l : I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task) : SProp := Lean.eq (it_export r) l.

Lemma it_source_roundtrip r : Logic.eq (it_import (it_export r)) r.
Proof.
  destruct r as [v0 v1 v2 v3]. unfold it_import, it_export. cbn.
  rewrite (sub_nat_rocq_roundtrip v0) (sub_nat_rocq_roundtrip v1) (sub_nat_rocq_roundtrip v2) (sub_nat_rocq_roundtrip v3).
  reflexivity.
Qed.

Lemma it_target_roundtrip l : Logic.eq (it_export (it_import l)) l.
Proof.
  destruct l as [v0 v1 v2 v3]. unfold it_import, it_export. cbn.
  have Hv0 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v0).
  have Hv1 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v1).
  have Hv2 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v2).
  have Hv3 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v3).
  rewrite Hv0 Hv1 Hv2 Hv3. reflexivity.
Qed.

Theorem it_concrete_task_source_total (r : TT.concrete_task) : ItRel r (it_export r).
Proof. exact (@Lean.eq_refl _ _). Qed.

Theorem it_concrete_task_target_total (l : I.Prosa_Classic_Implementation_Task_ConcreteTask_concrete_task) : ItRel (it_import l) l.
Proof. exact (coq_eq_to_imported_eq _ _ (it_target_roundtrip l)). Qed.

Lemma it_equality xR xL yR yL : ItRel xR xL -> ItRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal it_import (imported_eq_to_coq_eq _ _ Hxy).
    by rewrite !it_source_roundtrip in Hdecoded.
Qed.


(** Source [==] on concrete tasks (the registered [eqn_task]) against the derived Lean decision. *)
Lemma it_decide_eq xR xL yR yL : ItRel xR xL -> ItRel yR yL ->
  CtBoolRel (xR == yR) (I.Decidable_decide (Lean.eq xL yL) (I.Prosa_Classic_Implementation_Task_ConcreteTask_instDecidableEqConcrete_task xL yL)).
Proof.
  intros Hx Hy. apply ct_decide_bool. have E := it_equality _ _ _ _ Hx Hy. apply prop_sprop_rel_intro.
  - move=> /eqP H. exact (prop_to_sprop _ _ E H).
  - intro H. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ E H).
Qed.

(* ------------------------------------------------------------------ *)
(** * Concrete jobs *)

Definition ij_export (r : TJ.concrete_job) : I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job :=
  I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job_mk
    (sub_nat_to_imported (TJ.job_id r)) (sub_nat_to_imported (TJ.job_arrival r)) (sub_nat_to_imported (TJ.job_cost r)) (sub_nat_to_imported (TJ.job_deadline r)) (it_export (TJ.job_task r)).

Definition ij_import (l : I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job) : TJ.concrete_job :=
  {| TJ.job_id := sub_nat_to_rocq (I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job_job_id l);
     TJ.job_arrival := sub_nat_to_rocq (I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job_job_arrival l);
     TJ.job_cost := sub_nat_to_rocq (I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job_job_cost l);
     TJ.job_deadline := sub_nat_to_rocq (I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job_job_deadline l);
     TJ.job_task := it_import (I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job_job_task l) |}.

Definition IjRel (r : TJ.concrete_job) (l : I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job) : SProp := Lean.eq (ij_export r) l.

Lemma ij_source_roundtrip r : Logic.eq (ij_import (ij_export r)) r.
Proof.
  destruct r as [v0 v1 v2 v3 v4]. unfold ij_import, ij_export. cbn.
  rewrite (sub_nat_rocq_roundtrip v0) (sub_nat_rocq_roundtrip v1) (sub_nat_rocq_roundtrip v2) (sub_nat_rocq_roundtrip v3) (it_source_roundtrip v4).
  reflexivity.
Qed.

Lemma ij_target_roundtrip l : Logic.eq (ij_export (ij_import l)) l.
Proof.
  destruct l as [v0 v1 v2 v3 v4]. unfold ij_import, ij_export. cbn.
  have Hv0 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v0).
  have Hv1 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v1).
  have Hv2 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v2).
  have Hv3 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v3).
  have Hv4 := it_target_roundtrip v4.
  rewrite Hv0 Hv1 Hv2 Hv3 Hv4. reflexivity.
Qed.

Theorem ConcreteJob_concrete_job_source_total (r : TJ.concrete_job) : IjRel r (ij_export r).
Proof. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteJob_concrete_job_target_total (l : I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job) : IjRel (ij_import l) l.
Proof. exact (coq_eq_to_imported_eq _ _ (ij_target_roundtrip l)). Qed.

Lemma ij_equality xR xL yR yL : IjRel xR xL -> IjRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal ij_import (imported_eq_to_coq_eq _ _ Hxy).
    by rewrite !ij_source_roundtrip in Hdecoded.
Qed.

Lemma ij_job_id r l : IjRel r l -> SubNatRel (TJ.job_id r) (I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job_job_id l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma ij_job_arrival r l : IjRel r l -> SubNatRel (TJ.job_arrival r) (I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job_job_arrival l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma ij_job_cost r l : IjRel r l -> SubNatRel (TJ.job_cost r) (I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job_job_cost l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma ij_job_deadline r l : IjRel r l -> SubNatRel (TJ.job_deadline r) (I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job_job_deadline l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma ij_job_task r l : IjRel r l -> ItRel (TJ.job_task r) (I.Prosa_Classic_Implementation_Job_ConcreteJob_concrete_job_job_task l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteJob_job_eqdef_correspondence xR xL yR yL : IjRel xR xL -> IjRel yR yL ->
  CtBoolRel (TJ.job_eqdef xR yR) (I.Prosa_Classic_Implementation_Job_ConcreteJob_job_eqdef xL yL).
Proof.
  intros Hx Hy. unfold TJ.job_eqdef. cbn [I.Prosa_Classic_Implementation_Job_ConcreteJob_job_eqdef].
  exact (ct_bool_and _ _ _ _
    (ct_bool_and _ _ _ _
    (ct_bool_and _ _ _ _
    (ct_bool_and _ _ _ _
    (ct_decide_eq_nat _ _ _ _ (ij_job_id _ _ Hx) (ij_job_id _ _ Hy))
    (ct_decide_eq_nat _ _ _ _ (ij_job_arrival _ _ Hx) (ij_job_arrival _ _ Hy)))
    (ct_decide_eq_nat _ _ _ _ (ij_job_cost _ _ Hx) (ij_job_cost _ _ Hy)))
    (ct_decide_eq_nat _ _ _ _ (ij_job_deadline _ _ Hx) (ij_job_deadline _ _ Hy)))
    (it_decide_eq _ _ _ _ (ij_job_task _ _ Hx) (ij_job_task _ _ Hy))).
Qed.

Definition src_eqn_job : Type := ltac:(let X := type of (@TJ.eqn_job) in exact X).
Definition tgt_eqn_job : Type := ltac:(let X := type of (@I.Prosa_Classic_Implementation_Job_ConcreteJob_eqn_job) in exact X).

Theorem ConcreteJob_eqn_job_correspondence :
  Datatypes.prod (src_eqn_job -> tgt_eqn_job) (tgt_eqn_job -> src_eqn_job).
Proof.
  split.
  - intros f xL yL.
    have Hx := ConcreteJob_concrete_job_target_total xL. have Hy := ConcreteJob_concrete_job_target_total yL.
    exact (cr_reflect_forward _ _ _ _ (ij_equality _ _ _ _ Hx Hy)
      (ConcreteJob_job_eqdef_correspondence _ _ _ _ Hx Hy) (f (ij_import xL) (ij_import yL))).
  - intros g xR yR.
    have Hx := ConcreteJob_concrete_job_source_total xR. have Hy := ConcreteJob_concrete_job_source_total yR.
    exact (cr_reflect_backward _ _ _ _ (ij_equality _ _ _ _ Hx Hy)
      (ConcreteJob_job_eqdef_correspondence _ _ _ _ Hx Hy) (g (ij_export xR) (ij_export yR))).
Qed.

