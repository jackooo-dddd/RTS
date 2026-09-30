(* Helper copy of the accepted EdfPiBoundCorrespondence.v of the accepted restricted-supply fully nonpreemptive EDF certificate chain, re-bound to this export and
   to the replayed arrivals modules of this chain.  Its [bigMaxListCond] constructor equations are taken from the
   accepted EDF blocking-bound export root of this export, whose kernel-checked Lean statements are identical to
   those of the EDF busy-window root it originally used. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import EdfPiBoundSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaOvhEdfFullyNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence
  OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations
  OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence
  OvhTaskPreemptionParametersCorrespondence OvhRequestBoundFunctionCorrespondence.

Module I := ImportedRtaOvhEdfFullyNonpreemptive.
Module S := EdfPiBoundSemanticSource.EdfPiBoundSemanticSource.
Module T := prosa.TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.

(** Definition certificate for [analysis/definitions/busy_interval/edf_pi_bound.v].

    Source side: the extracted byte-identical definition block (the
    task-preemption-parameters and request-bound-function imports bound to
    the accepted extracted sources); target side: the compiled Lean
    definition.  Inputs: [TaskCost], [TaskDeadline] and [MaxArrivals]
    pointwise by [SubNatRel], [TaskMaxNonpreemptiveSegment] by the accepted
    [TppMaxSegmentRel], task sets by [ArListRel].  The conditional [\max] is
    related to [bigMaxListCond] through kernel-checked Lean constructor
    equations exported with the artifact and the accepted [maxn]/[Nat.max]
    correspondence (as in the accepted EDF blocking bound); the RBF and the
    filtered sum are closed by the accepted [OvhRequestBoundFunctionCorrespondence]
    re-instantiated at this artifact.  No source or target theorem is used. *)

(** ** Conditional maximum over a sequence *)

Section BigMax.
  Context (X : Type).
  Variable PR : X -> bool.
  Variable PL : X -> I.Bool.
  Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).
  Variable FR : X -> nat.
  Variable FL : X -> Lean.Nat.
  Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

  Lemma epi_bigmax_canonical (xs : seq X) :
    SubNatRel (\max_(x <- xs | PR x) FR x)
      (I.Prosa_Util_Minmax_bigMaxListCond X (ar_list_to_imported xs) PL FL).
  Proof.
    induction xs as [|x xs IH].
    - rewrite big_nil.
      exact (sub_imported_eq_sym _ _
        (I.Prosa_Validation_BlockingBoundInterface_production_bigMaxListCond_nil X PL FL)).
    - rewrite big_cons. cbn [ar_list_to_imported].
      have Hx := HP x. unfold ArBoolRel in Hx.
      destruct (PR x).
      + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
          (I.Prosa_Validation_BlockingBoundInterface_production_bigMaxListCond_cons_true
            X PL FL x (ar_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
        refine (sub_imported_eq_trans _ _ _
          (sub_imported_eq_sym _ _ (pp_max_canonical (FR x) (\max_(y <- xs | PR y) FR y))) _).
        exact (sub_imported_eq_congr2 I.Nat_max _ _ _ _ (HF x) IH).
      + refine (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
          (I.Prosa_Validation_BlockingBoundInterface_production_bigMaxListCond_cons_false
            X PL FL x (ar_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
  Qed.

  Lemma epi_bigmax_related (xsR : seq X) (xsL : I.List X) :
    ArListRel xsR xsL ->
    SubNatRel (\max_(x <- xsR | PR x) FR x) (I.Prosa_Util_Minmax_bigMaxListCond X xsL PL FL).
  Proof.
    intro Hxs.
    exact (sub_imported_eq_trans _ _ _ (epi_bigmax_canonical xsR)
      (sub_imported_eq_congr (fun l => I.Prosa_Util_Minmax_bigMaxListCond X l PL FL) _ _ Hxs)).
  Qed.
End BigMax.

(** ** Definition *)

Section EdfPi.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable tdR : prosa.model.task.concept.TaskDeadline Task.
  Variable tdL : I.Prosa_Model_Task_Concept_TaskDeadline Task dT.
  Hypothesis Htd : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR tsk)
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL tsk).
  Variable mR : T.TaskMaxNonpreemptiveSegment Task.
  Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
  Hypothesis Hm : TppMaxSegmentRel Task mR mL.
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : forall (tsk : Task) (nR : nat) (nL : Lean.Nat), SubNatRel nR nL ->
    SubNatRel (@prosa.model.task.arrival.curves.max_arrivals Task maR tsk nR)
      (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT maL tsk nL).
  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.

  Theorem longest_busy_interval_with_pi_correspondence (tsk : Task) :
    SubNatRel (@S.longest_busy_interval_with_pi Task tcR tdR mR maR tsR tsk)
      (I.Prosa_Analysis_Definitions_BusyInterval_EdfPiBound_longest_busy_interval_with_pi
        Task dT tcL tdL mL maL tsL tsk).
  Proof.
    unfold S.longest_busy_interval_with_pi.
    cbn [I.Prosa_Analysis_Definitions_BusyInterval_EdfPiBound_longest_busy_interval_with_pi].
    apply epi_bigmax_related; [| |exact Hts].
    - intro o. exact (ar_decide_lt_related _ _ _ _ (Htd tsk) (Htd o)).
    - intro o.
      apply svc_target_add_related.
      + exact (svc_target_sub_related _ _ _ _ (Hm o) (sub_nat_rel_canonical 1)).
      + apply rbf_sum_filtered_related; [| |exact Hts].
        * intro h.
          exact (task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma h _ _
            (svc_target_sub_related _ _ _ _ (Htd o) (Htd h))).
        * intro h. exact (ar_decide_le_related _ _ _ _ (Htd h) (Htd o)).
  Qed.
End EdfPi.
