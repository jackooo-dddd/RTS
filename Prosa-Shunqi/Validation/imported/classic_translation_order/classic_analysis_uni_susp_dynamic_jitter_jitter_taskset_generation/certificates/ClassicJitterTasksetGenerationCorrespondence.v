From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.priority classic.analysis.uni.susp.dynamic.jitter.jitter_taskset_generation.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicJitterTasksetGeneration.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicJitterTasksetGenerationBase ClassicJitterTasksetGenerationList.

Module I := ImportedClassicJitterTasksetGeneration.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/uni/susp/dynamic/jitter/jitter_taskset_generation.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the task type is an [eqType], identified, with the Lean [DecidableEq] instance given by its decision procedure
    ([ct_decidable_eq]); task parameters pointwise through [SubNatRel]; FP policies pointwise on Booleans; all with two-way
    totals.  [if tsk == tsk_i] against the Lean [if tsk = tsk_i] on the canonical instance; the Boolean test of
    [task_jitter] against the Lean [if b = true]. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

Lemma cl_nat_logic nR nL : SubNatRel nR nL -> Logic.eq nL (sub_nat_to_imported nR).
Proof. intro H. exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ H)). Qed.

Lemma cl_nat_input nR nL : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof. intro H. rewrite (cl_nat_logic _ _ H). exact (sub_nat_rocq_roundtrip nR). Qed.


(* ------------------------------------------------------------------ *)
(** * Auxiliary relations (as in the accepted classic jitter_schedule certificate) *)

Lemma ctg_ite_eq (J : eqType) (A : Type) (x y : J) (a b : A) :
  Logic.eq (I.ite A (Lean.eq x y) (ct_decidable_eq J x y) a b) (if x == y then a else b).
Proof. rewrite /ct_decidable_eq. by case: (@eqP J x y). Qed.

Lemma ctg_ite_bool (A : Type) bR bL (Hb : CtBoolRel bR bL) (a b : A) :
  Logic.eq (I.ite A (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) a b) (if bR then a else b).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). clear Hb. by case: bR. Qed.

Definition CtgParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (ocR : Task -> nat) (ocL : Task -> Lean.Nat).
Hypothesis Hoc : CtgParRel Task ocR ocL.

Theorem JitterTaskSetGeneration_inflated_task_cost_correspondence sbR sbL (Hsb : CtgParRel Task sbR sbL) tsk_i :
  CtgParRel Task (@JitterTaskSetGeneration.inflated_task_cost Task ocR sbR tsk_i) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterTasksetGeneration_JitterTaskSetGeneration_inflated_task_cost Task dT ocL sbL tsk_i).
Proof.
  intro x. apply: coq_eq_to_imported_eq. rewrite /JitterTaskSetGeneration.inflated_task_cost. unfold I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterTasksetGeneration_JitterTaskSetGeneration_inflated_task_cost.
  rewrite ctg_ite_eq. case: (x == tsk_i).
  - exact (imported_eq_to_coq_eq _ _ (sub_add_correspondence _ _ _ _ (Hoc x) (Hsb x))).
  - exact (imported_eq_to_coq_eq _ _ (Hoc x)).
Qed.

Theorem JitterTaskSetGeneration_task_jitter_correspondence hpR hpL (Hhp : forall a b, CtBoolRel (hpR a b) (hpL a b)) tsk_i
    RR RL (HR : CtgParRel Task RR RL) :
  CtgParRel Task (@JitterTaskSetGeneration.task_jitter Task ocR hpR tsk_i RR) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterTasksetGeneration_JitterTaskSetGeneration_task_jitter Task dT ocL hpL tsk_i RL).
Proof.
  intro x. apply: coq_eq_to_imported_eq. rewrite /JitterTaskSetGeneration.task_jitter. unfold I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterTasksetGeneration_JitterTaskSetGeneration_task_jitter.
  rewrite (ctg_ite_bool _ _ _ (ct_bool_and _ _ _ _ (Hhp x tsk_i) (ct_bool_not _ _ (ct_decide_eq Task x tsk_i)))).
  case: (hpR x tsk_i && (x != tsk_i)).
  - exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ (HR x) (Hoc x))).
  - reflexivity.
Qed.
End Defs.
