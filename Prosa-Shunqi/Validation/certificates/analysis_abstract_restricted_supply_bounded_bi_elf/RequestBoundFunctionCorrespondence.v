From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import RequestBoundFunctionSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBoundedBiElf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence.

Module I := ImportedBoundedBiElf.
Module S := RequestBoundFunctionSemanticSource.RequestBoundFunctionSemanticSource.

(** Definition certificates for [analysis/definitions/request_bound_function.v].

    Source side: the extracted byte-identical definition blocks; target side:
    the compiled Lean declarations.  Inputs: [TaskCost] and [MaxArrivals]
    pointwise by [SubNatRel], the FP policy pointwise on Booleans, task sets
    by [ArListRel].  MathComp's sequence sums (plain and filtered) are
    related to [sumSeq]/[sumFiltered] through kernel-checked Lean constructor
    equations exported with the artifact. *)

Lemma rbf_logic_eq_to_lean_eq {A : Type} (x y : A) :
  Logic.eq x y -> Lean.eq x y.
Proof. intros []. exact (@Lean.eq_refl _ _). Qed.

Lemma rbf_neq_related (T : eqType) (x y : T) :
  ArBoolRel (x != y)
    (I.Decidable_decide (I.Not (Lean.eq x y)) (I.instDecidableNot (Lean.eq x y) (ar_decidable_eq T x y))).
Proof.
  apply rbf_logic_eq_to_lean_eq.
  unfold ar_decidable_eq. case: eqP => H; reflexivity.
Qed.

(** ** Sequence sums *)

Section Sums.
  Context (X : Type).
  Variable FR : X -> nat.
  Variable FL : X -> Lean.Nat.
  Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

  Lemma rbf_sum_canonical (xs : seq X) :
    SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (ar_list_to_imported xs) FL).
  Proof.
    induction xs as [|x xs IH].
    - rewrite big_nil.
      exact (sub_imported_eq_sym _ _
        (I.Prosa_Validation_RequestBoundFunctionInterface_production_sumSeq_nil X FL)).
    - rewrite big_cons. cbn [ar_list_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_RequestBoundFunctionInterface_production_sumSeq_cons
          X FL x (ar_list_to_imported xs)))).
      exact (svc_target_add_related _ _ _ _ (HF x) IH).
  Qed.

  Lemma rbf_sum_related (xsR : seq X) (xsL : I.List X) :
    ArListRel xsR xsL ->
    SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
  Proof.
    intro Hxs.
    exact (sub_imported_eq_trans _ _ _ (rbf_sum_canonical xsR)
      (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
  Qed.

  Variable PR : X -> bool.
  Variable PL : X -> I.Bool.
  Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).

  Lemma rbf_sum_filtered_canonical (xs : seq X) :
    SubNatRel (\sum_(x <- xs | PR x) FR x)
      (I.Prosa_Util_Sum_sumFiltered X (ar_list_to_imported xs) PL FL).
  Proof.
    induction xs as [|x xs IH].
    - rewrite big_nil.
      exact (sub_imported_eq_sym _ _
        (I.Prosa_Validation_RequestBoundFunctionInterface_production_sumFiltered_nil X PL FL)).
    - rewrite big_cons. cbn [ar_list_to_imported].
      have Hx := HP x. unfold ArBoolRel in Hx.
      destruct (PR x).
      + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
          (I.Prosa_Validation_RequestBoundFunctionInterface_production_sumFiltered_cons_true
            X PL FL x (ar_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
        exact (svc_target_add_related _ _ _ _ (HF x) IH).
      + refine (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
          (I.Prosa_Validation_RequestBoundFunctionInterface_production_sumFiltered_cons_false
            X PL FL x (ar_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
  Qed.

  Lemma rbf_sum_filtered_related (xsR : seq X) (xsL : I.List X) :
    ArListRel xsR xsL ->
    SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
  Proof.
    intro Hxs.
    exact (sub_imported_eq_trans _ _ _ (rbf_sum_filtered_canonical xsR)
      (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
  Qed.
End Sums.

(** ** Definitions *)

Section Rbf.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : forall (tsk : Task) (nR : nat) (nL : Lean.Nat), SubNatRel nR nL ->
    SubNatRel (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk nR)
      (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk nL).

  Theorem task_request_bound_function_correspondence (tsk : Task) (dR : nat) (dL : Lean.Nat) :
    SubNatRel dR dL ->
    SubNatRel (@S.task_request_bound_function Task tcR maR tsk dR)
      (I.Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function
        Task dT tcL maL tsk dL).
  Proof.
    intro Hd. unfold S.task_request_bound_function.
    cbn [I.Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function].
    exact (sub_mul_correspondence _ _ _ _ (Htc tsk) (Hma tsk _ _ Hd)).
  Qed.

  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.

  Let RBF (dR : nat) (dL : Lean.Nat) (Hd : SubNatRel dR dL) (tsk : Task) :=
    task_request_bound_function_correspondence tsk dR dL Hd.

  Theorem total_request_bound_function_correspondence (dR : nat) (dL : Lean.Nat) :
    SubNatRel dR dL ->
    SubNatRel (@S.total_request_bound_function Task tcR maR tsR dR)
      (I.Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function
        Task dT tcL maL tsL dL).
  Proof.
    intro Hd. unfold S.total_request_bound_function.
    cbn [I.Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function].
    exact (rbf_sum_related _ _ _ (RBF dR dL Hd) _ _ Hts).
  Qed.

  Variable fpR : prosa.model.priority.definitions.FP_policy Task.
  Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hfp : forall x y : Task,
    ArBoolRel (@prosa.model.priority.definitions.hep_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL x y).

  Theorem total_hep_request_bound_function_FP_correspondence (tsk : Task) (dR : nat) (dL : Lean.Nat) :
    SubNatRel dR dL ->
    SubNatRel (@S.total_hep_request_bound_function_FP Task tcR maR tsR fpR tsk dR)
      (I.Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP
        Task dT tcL maL tsL fpL tsk dL).
  Proof.
    intro Hd. unfold S.total_hep_request_bound_function_FP.
    cbn [I.Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP].
    apply rbf_sum_filtered_related; [exact (RBF dR dL Hd)| |exact Hts].
    intro o. exact (Hfp o tsk).
  Qed.

  Theorem total_ohep_request_bound_function_FP_correspondence (tsk : Task) (dR : nat) (dL : Lean.Nat) :
    SubNatRel dR dL ->
    SubNatRel (@S.total_ohep_request_bound_function_FP Task tcR maR tsR fpR tsk dR)
      (I.Prosa_Analysis_Definitions_RequestBoundFunction_total_ohep_request_bound_function_FP
        Task dT tcL maL tsL fpL tsk dL).
  Proof.
    intro Hd. unfold S.total_ohep_request_bound_function_FP.
    cbn [I.Prosa_Analysis_Definitions_RequestBoundFunction_total_ohep_request_bound_function_FP].
    apply rbf_sum_filtered_related; [exact (RBF dR dL Hd)| |exact Hts].
    intro o. exact (ar_bool_and_related _ _ _ _ (Hfp o tsk) (rbf_neq_related Task o tsk)).
  Qed.

  Theorem total_ep_request_bound_function_FP_correspondence (tsk : Task) (dR : nat) (dL : Lean.Nat) :
    SubNatRel dR dL ->
    SubNatRel (@S.total_ep_request_bound_function_FP Task tcR maR tsR fpR tsk dR)
      (I.Prosa_Analysis_Definitions_RequestBoundFunction_total_ep_request_bound_function_FP
        Task dT tcL maL tsL fpL tsk dL).
  Proof.
    intro Hd. unfold S.total_ep_request_bound_function_FP.
    cbn [I.Prosa_Analysis_Definitions_RequestBoundFunction_total_ep_request_bound_function_FP].
    apply rbf_sum_filtered_related; [exact (RBF dR dL Hd)| |exact Hts].
    intro o. unfold prosa.model.priority.definitions.ep_task.
    cbn [I.Prosa_Model_Priority_Definitions_ep_task].
    exact (ar_bool_and_related _ _ _ _ (Hfp o tsk) (Hfp tsk o)).
  Qed.

  Theorem total_hp_request_bound_function_FP_correspondence (tsk : Task) (dR : nat) (dL : Lean.Nat) :
    SubNatRel dR dL ->
    SubNatRel (@S.total_hp_request_bound_function_FP Task tcR maR tsR fpR tsk dR)
      (I.Prosa_Analysis_Definitions_RequestBoundFunction_total_hp_request_bound_function_FP
        Task dT tcL maL tsL fpL tsk dL).
  Proof.
    intro Hd. unfold S.total_hp_request_bound_function_FP.
    cbn [I.Prosa_Analysis_Definitions_RequestBoundFunction_total_hp_request_bound_function_FP].
    apply rbf_sum_filtered_related; [exact (RBF dR dL Hd)| |exact Hts].
    intro o. unfold prosa.model.priority.definitions.hp_task.
    cbn [I.Prosa_Model_Priority_Definitions_hp_task].
    exact (ar_bool_and_related _ _ _ _ (Hfp o tsk) (svc_bool_not_related _ _ (Hfp tsk o))).
  Qed.
End Rbf.
