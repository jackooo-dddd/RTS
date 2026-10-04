From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From prosa Require Import util.seqset classic.implementation.global.jitter.task classic.implementation.global.jitter.job.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicGJPeriodicArrivals.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicGJPeriodicArrivalsBase ClassicGJPeriodicArrivalsList1.



Module I := ImportedClassicGJPeriodicArrivals.
Module TT := prosa.classic.implementation.global.jitter.task.ConcreteTask.
Import (canonicals) TT.
Module TJ := prosa.classic.implementation.global.jitter.job.ConcreteJob.
Import (canonicals) TJ.
Local Open Scope nat_scope.

(** Record relations re-bound to this export (as in the accepted concrete task/job certificates): concrete tasks and jobs by their fieldwise canonical import (Nat fields by the canonical Nat map, the job's task by the concrete-task relation), with two-way totals and injectivity; concrete task sets by the elementwise image of the underlying sequence. *)

(* ------------------------------------------------------------------ *)
(** * Concrete tasks *)

Definition it_export (r : TT.concrete_task) : I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_task :=
  I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_task_mk
    (sub_nat_to_imported (TT.task_id r)) (sub_nat_to_imported (TT.task_cost r)) (sub_nat_to_imported (TT.task_period r)) (sub_nat_to_imported (TT.task_deadline r)) (sub_nat_to_imported (TT.task_jitter r)).

Definition it_import (l : I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_task) : TT.concrete_task :=
  match l with I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_task_mk p0 p1 p2 p3 p4 =>
  {| TT.task_id := sub_nat_to_rocq p0;
     TT.task_cost := sub_nat_to_rocq p1;
     TT.task_period := sub_nat_to_rocq p2;
     TT.task_deadline := sub_nat_to_rocq p3;
     TT.task_jitter := sub_nat_to_rocq p4 |} end.

Definition ItRel (r : TT.concrete_task) (l : I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_task) : SProp := Lean.eq (it_export r) l.

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

Theorem ConcreteTask_concrete_task_target_total (l : I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_task) : ItRel (it_import l) l.
Proof. exact (coq_eq_to_imported_eq _ _ (it_target_roundtrip l)). Qed.

Lemma it_equality xR xL yR yL : ItRel xR xL -> ItRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal it_import (imported_eq_to_coq_eq _ _ Hxy).
    by rewrite !it_source_roundtrip in Hdecoded.
Qed.

Lemma it_task_cost r l : ItRel r l -> SubNatRel (TT.task_cost r) (I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_task_task_cost l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_period r l : ItRel r l -> SubNatRel (TT.task_period r) (I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_task_task_period l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_deadline r l : ItRel r l -> SubNatRel (TT.task_deadline r) (I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_task_task_deadline l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma it_task_jitter r l : ItRel r l -> SubNatRel (TT.task_jitter r) (I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_task_task_jitter l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

(* ------------------------------------------------------------------ *)
(** * Task sets *)

Lemma it_uniq_rel (s : seq TT.concrete_task) :
  PropSPropRel (uniq s) (I.List_Nodup_inst1 I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_task (cl1_map it_export s)).
Proof. exact (cl1_uniq_rel _ _ it_export it_import it_source_roundtrip it_target_roundtrip s). Qed.

Definition its_list (sL : I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_taskset) : I.List_inst1 I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_task :=
  match sL with I.Prosa_Util_Seqset_set_mk_inst1 xs _ => xs end.

Definition ItsRel (sR : TT.concrete_taskset) (sL : I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_taskset) : SProp :=
  Lean.eq (cl1_map it_export (@_set_seq TT.concrete_task sR)) (its_list sL).

Definition its_export (sR : TT.concrete_taskset) : I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_taskset :=
  match sR with
  | @Build_set _ xs Hu =>
      I.Prosa_Util_Seqset_set_mk_inst1 _ _ (cl1_map it_export xs) (prop_to_sprop _ _ (it_uniq_rel xs) Hu)
  end.

Lemma its_import_uniq (xs : I.List_inst1 I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_task)
    (Hn : I.List_Nodup_inst1 _ xs) : uniq (cl1_unmap it_import xs).
Proof.
  apply (sprop_to_prop _ _ (it_uniq_rel (cl1_unmap it_import xs))).
  rewrite (cl1_map_unmap it_export it_import it_target_roundtrip xs). exact Hn.
Qed.

Definition its_import (sL : I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_taskset) : TT.concrete_taskset :=
  match sL with
  | I.Prosa_Util_Seqset_set_mk_inst1 xs Hn => @Build_set TT.concrete_task (cl1_unmap it_import xs) (its_import_uniq xs Hn)
  end.

Theorem ConcreteTask_concrete_taskset_source_total (sR : TT.concrete_taskset) : ItsRel sR (its_export sR).
Proof. destruct sR. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteTask_concrete_taskset_target_total (sL : I.Prosa_Classic_Implementation_Global_Jitter_Task_ConcreteTask_concrete_taskset) :
  ItsRel (its_import sL) sL.
Proof.
  destruct sL as [xs Hn]. unfold ItsRel, its_import, its_list. cbn.
  exact (coq_eq_to_imported_eq _ _ (cl1_map_unmap it_export it_import it_target_roundtrip xs)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Concrete jobs *)

Definition ij_export (r : TJ.concrete_job) : I.Prosa_Classic_Implementation_Global_Jitter_Job_ConcreteJob_concrete_job :=
  I.Prosa_Classic_Implementation_Global_Jitter_Job_ConcreteJob_concrete_job_mk
    (sub_nat_to_imported (TJ.job_id r)) (sub_nat_to_imported (TJ.job_arrival r)) (sub_nat_to_imported (TJ.job_cost r)) (sub_nat_to_imported (TJ.job_deadline r)) (sub_nat_to_imported (TJ.job_jitter r)) (it_export (TJ.job_task r)).

Definition ij_import (l : I.Prosa_Classic_Implementation_Global_Jitter_Job_ConcreteJob_concrete_job) : TJ.concrete_job :=
  match l with I.Prosa_Classic_Implementation_Global_Jitter_Job_ConcreteJob_concrete_job_mk p0 p1 p2 p3 p4 p5 =>
  {| TJ.job_id := sub_nat_to_rocq p0;
     TJ.job_arrival := sub_nat_to_rocq p1;
     TJ.job_cost := sub_nat_to_rocq p2;
     TJ.job_deadline := sub_nat_to_rocq p3;
     TJ.job_jitter := sub_nat_to_rocq p4;
     TJ.job_task := it_import p5 |} end.

Definition IjRel (r : TJ.concrete_job) (l : I.Prosa_Classic_Implementation_Global_Jitter_Job_ConcreteJob_concrete_job) : SProp := Lean.eq (ij_export r) l.

Lemma ij_source_roundtrip r : Logic.eq (ij_import (ij_export r)) r.
Proof.
  destruct r as [v0 v1 v2 v3 v4 v5]. unfold ij_import, ij_export. cbn.
  rewrite (sub_nat_rocq_roundtrip v0) (sub_nat_rocq_roundtrip v1) (sub_nat_rocq_roundtrip v2) (sub_nat_rocq_roundtrip v3) (sub_nat_rocq_roundtrip v4) (it_source_roundtrip v5).
  reflexivity.
Qed.

Lemma ij_target_roundtrip l : Logic.eq (ij_export (ij_import l)) l.
Proof.
  destruct l as [v0 v1 v2 v3 v4 v5]. unfold ij_import, ij_export. cbn.
  have Hv0 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v0).
  have Hv1 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v1).
  have Hv2 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v2).
  have Hv3 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v3).
  have Hv4 := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip v4).
  have Hv5 := it_target_roundtrip v5.
  rewrite Hv0 Hv1 Hv2 Hv3 Hv4 Hv5. reflexivity.
Qed.

Theorem ConcreteJob_concrete_job_source_total (r : TJ.concrete_job) : IjRel r (ij_export r).
Proof. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteJob_concrete_job_target_total (l : I.Prosa_Classic_Implementation_Global_Jitter_Job_ConcreteJob_concrete_job) : IjRel (ij_import l) l.
Proof. exact (coq_eq_to_imported_eq _ _ (ij_target_roundtrip l)). Qed.

Lemma ij_equality xR xL yR yL : IjRel xR xL -> IjRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal ij_import (imported_eq_to_coq_eq _ _ Hxy).
    by rewrite !ij_source_roundtrip in Hdecoded.
Qed.

Lemma ij_job_arrival r l : IjRel r l -> SubNatRel (TJ.job_arrival r) (I.Prosa_Classic_Implementation_Global_Jitter_Job_ConcreteJob_concrete_job_job_arrival l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma ij_job_cost r l : IjRel r l -> SubNatRel (TJ.job_cost r) (I.Prosa_Classic_Implementation_Global_Jitter_Job_ConcreteJob_concrete_job_job_cost l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma ij_job_deadline r l : IjRel r l -> SubNatRel (TJ.job_deadline r) (I.Prosa_Classic_Implementation_Global_Jitter_Job_ConcreteJob_concrete_job_job_deadline l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma ij_job_jitter r l : IjRel r l -> SubNatRel (TJ.job_jitter r) (I.Prosa_Classic_Implementation_Global_Jitter_Job_ConcreteJob_concrete_job_job_jitter l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Lemma ij_job_task r l : IjRel r l -> ItRel (TJ.job_task r) (I.Prosa_Classic_Implementation_Global_Jitter_Job_ConcreteJob_concrete_job_job_task l).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.


