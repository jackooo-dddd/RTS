From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From prosa Require Import implementation.definitions.job_constructor.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJobConstructor ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence EacFullCorrespondence AbCorrespondence ImplTaskCorrespondence.

Module I := ImportedJobConstructor.
Module T := prosa.implementation.definitions.task.
Module JC := prosa.implementation.definitions.job_constructor.

(** Correspondences for [implementation/definitions/job_constructor.v].  The
    [Task] and [Job] aliases (the concrete types as [eqType]s) are related by
    the accepted fieldwise canonical task and job relations, with two-way
    totals; the job generators are related for related tasks, instants,
    identifiers and counts, job lists by the canonical list map. *)

Lemma Task_source_total (tR : JC.Task) : ItTaskRel tR (it_task_export tR).
Proof. exact (concrete_task_source_total tR). Qed.

Lemma Task_target_total (tL : I.Prosa_Implementation_Definitions_JobConstructor_Task) :
  ItTaskRel (it_task_import tL : JC.Task) tL.
Proof. exact (concrete_task_target_total tL). Qed.

Lemma Job_source_total (jR : JC.Job) : ItJobRel jR (it_job_export jR).
Proof. exact (concrete_job_source_total jR). Qed.

Lemma Job_target_total (jL : I.Prosa_Implementation_Definitions_JobConstructor_Job) :
  ItJobRel (it_job_import jL : JC.Job) jL.
Proof. exact (concrete_job_target_total jL). Qed.

Theorem generate_job_at_correspondence tR tL tiR tiL idR idL :
  ItTaskRel tR tL -> SubNatRel tiR tiL -> SubNatRel idR idL ->
  ItJobRel (JC.generate_job_at tR tiR idR)
    (I.Prosa_Implementation_Definitions_JobConstructor_generate_job_at tL tiL idL).
Proof.
  intros Ht Hti Hid. destruct Ht. destruct Hti. destruct Hid.
  unfold ItJobRel, it_job_export, JC.generate_job_at.
  cbn [I.Prosa_Implementation_Definitions_JobConstructor_generate_job_at].
  have Hadd := sub_add_correspondence tiR _ (T.task_deadline tR) _
    (sub_nat_rel_canonical tiR) (sub_nat_rel_canonical (T.task_deadline tR)).
  exact (sub_imported_eq_congr
    (fun d => I.Prosa_Implementation_Definitions_Task_concrete_job_mk
      (sub_nat_to_imported idR) (sub_nat_to_imported tiR) (sub_nat_to_imported (T.task_cost tR)) d
      (it_task_export tR)) _ _ Hadd).
Qed.

(** Job lists are related by the canonical list map. *)
Fixpoint jc_jobs_export (xs : seq T.concrete_job) :
    I.List_inst1 I.Prosa_Implementation_Definitions_Task_concrete_job :=
  match xs with
  | [::] => I.List_nil_inst1 _
  | x :: tail => I.List_cons_inst1 _ (it_job_export x) (jc_jobs_export tail)
  end.

Definition JcJobListRel (xsR : seq T.concrete_job)
    (xsL : I.List_inst1 I.Prosa_Implementation_Definitions_Task_concrete_job) : SProp :=
  Lean.eq (jc_jobs_export xsR) xsL.

Fixpoint jc_jobs_import (xs : I.List_inst1 I.Prosa_Implementation_Definitions_Task_concrete_job) :
    seq T.concrete_job :=
  match xs with
  | I.List_nil_inst1 => [::]
  | I.List_cons_inst1 x tail => it_job_import x :: jc_jobs_import tail
  end.

Lemma jc_jobs_source_roundtrip xs : Logic.eq (jc_jobs_import (jc_jobs_export xs)) xs.
Proof.
  elim: xs => [|x tail IH] //=. by rewrite (it_job_source_roundtrip x) IH.
Qed.

Fixpoint jc_jobs_target_roundtrip xs : JcJobListRel (jc_jobs_import xs) xs :=
  match xs with
  | I.List_nil_inst1 => @Lean.eq_refl _ _
  | I.List_cons_inst1 x tail =>
      sub_imported_eq_congr2 (I.List_cons_inst1 _) _ _ _ _ (it_job_target_roundtrip x)
        (jc_jobs_target_roundtrip tail)
  end.

Lemma jc_range_succ (start len step : Lean.Nat) :
  Logic.eq (I.List_range' start (Lean.Nat_succ len) step)
    (I.List_cons_inst1 Lean.Nat start (I.List_range' (Lean.Nat_add start step) len step)).
Proof. reflexivity. Qed.

(** The generated jobs, over the ascending identifiers [start, start + len). *)
Fixpoint jc_generate_map_range tR tiR (len start : nat) {struct len} :
  JcJobListRel (map (JC.generate_job_at tR tiR) (iota start len))
    (I.List_map_inst3 _ _
      (I.Prosa_Implementation_Definitions_JobConstructor_generate_job_at (it_task_export tR)
        (sub_nat_to_imported tiR))
      (I.List_range' (sub_nat_to_imported start) (sub_nat_to_imported len)
        (sub_nat_to_imported 1))).
Proof.
  destruct len as [|len]; first exact (@Lean.eq_refl _ _).
  cbn [sub_nat_to_imported iota map].
  rewrite jc_range_succ.
  have Hstart : Logic.eq (Lean.Nat_add (sub_nat_to_imported start) (sub_nat_to_imported 1))
      (sub_nat_to_imported start.+1) by reflexivity.
  rewrite Hstart.
  exact (sub_imported_eq_congr2 (I.List_cons_inst1 _) _ _ _ _
    (generate_job_at_correspondence tR _ tiR _ start _ (concrete_task_source_total tR)
      (sub_nat_rel_canonical tiR) (sub_nat_rel_canonical start))
    (jc_generate_map_range tR tiR len start.+1)).
Defined.

Theorem generate_jobs_at_correspondence tR tL nR nL tiR tiL :
  ItTaskRel tR tL -> SubNatRel nR nL -> SubNatRel tiR tiL ->
  JcJobListRel (JC.generate_jobs_at tR nR tiR)
    (I.Prosa_Implementation_Definitions_JobConstructor_generate_jobs_at tL nL tiL).
Proof.
  intros Ht Hn Hti. destruct Ht. destruct Hn. destruct Hti.
  unfold JC.generate_jobs_at.
  cbn [I.Prosa_Implementation_Definitions_JobConstructor_generate_jobs_at].
  exact (jc_generate_map_range tR tiR nR 0).
Qed.
